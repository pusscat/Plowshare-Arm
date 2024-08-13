"""
rop_finder2.py: a Capstone based ROP gadget finder.

"""
import argparse
import binascii
import ctypes
import logging
import multiprocessing
import os
import queue
import sqlite3
import sys
import threading
import time

# third-party modules
import capstone
import elftools.elf.constants
import elftools.elf.elffile
import pefile
import zmq

SEG_LOCK = multiprocessing.Lock()
# current segment we're working on. Allocate 100MB
CURRENT_SEGMENT = multiprocessing.Array(ctypes.c_char, 100 * (2 ** 20), 
                                        lock=SEG_LOCK)
FINISHED_MESSAGE = (-1, -1, -1, -1)

class GadgetQueuePushStub(object):
  """
  Object to act as a means to enqueue messages to workers in a platform
  independent way.
  """
  def __init__(self, socket_address, sempahore):
    self.context = zmq.Context()
    self.socket = self.context.socket(zmq.PUSH)
    self.socket.bind(socket_address)
    self.semaphore = sempahore

  def put(self, item):
    """
    send an item to the other end of the zmq socket.
    """
    logger = multiprocessing.get_logger()
    logger.debug("ACQUIRING SEMAPHORE!")
    self.semaphore.acquire()
    logger.debug("SEMAPHORE ACQUIRED!")

    logger.debug("SENDING JOB!")
    self.socket.send_pyobj(item)
    self.semaphore.release()


class GadgetQueuePullStub(threading.Thread):
  """
  Object to act as the receiving end of the message queue
  """
  def __init__(self, socket_address):
    threading.Thread.__init__(self)
    self.socket_addr = socket_address
    self.queue = Queue.Queue(1)

  def GetQueue(self):
    return self.queue

  def run(self):
    context = zmq.Context()
    sock = context.socket(zmq.PULL)
    sock.connect(self.socket_addr)
    poller = zmq.Poller()
    poller.register(sock, zmq.POLLIN)

    while 1:
      ready_sockets = dict(poller.poll(1000))

      if sock in ready_sockets:
        msg = sock.recv_pyobj()
        self.queue.put(msg)

        if msg == FINISHED_MESSAGE:
          break


class SectionStore(object):
  """
  Stores executable sections for processing.
  """
  def __init__(self, filename, base_addr, job_size=0x1000, raw=False):
    """
    Constructor

    Args:
      args: an argparse args object

    Returns:
      a new section store
    """
    self.filename = filename
    self.base_addr = base_addr
    self.job_size = job_size
    self.raw = raw
    
  def SetJobSize(self, job_size):
    self.job_size = job_size

  def ReturnReadFileFormatFunc(self, filename):
    """
    Process a file to extract segments

    Args:
      filename: a path to a filename.

    Returns:
      a callback for that'll yield the r-x sections of the file.
    """
    if self.raw:
      def RawFunc():
        seg_name = "raw_" + hex(self.base_addr).replace('l','')
        yield (seg_name, self.base_addr, self.base_addr, 
               multiprocessing.Array(ctypes.c_char, open(filename).read()))
        return

      return RawFunc

    if not os.path.exists(filename):
      return
    else:
      with open(filename, 'rb') as f:
        magic = f.read(4)

      if magic.startswith("\x4d\x5a"):
        def ProcessPE():
          return self.ReadPEFile(filename)
        return ProcessPE
      elif magic.startswith("\x7F\x45\x4C\x46"):
        def ProcessElf():
          return self.ReadElfFile(filename)
        return ProcessElf
      else:
        raise NotImplementedError("Unknown File Format")

  def ReadElfFile(self, filename):
    """
    Read an Elf file and find it's r-x sections to search for ROP gadgets in

    Args:
      filename: a string path to the file name.
      options: an optparse options object with the following option:
               - base: an integer base to load the module at instead of the 
                       one specified in the file.

    Yields:
      A 3 tuple of:
         -- segment_name (string)
         -- starting_addr (integer)
         -- segment_bytes (string)
    """
    segment_name = filename
    starting_addr = 0x0
    segment_bytes = ""

    elf = elftools.elf.elffile.ELFFile(open(filename, 'rb'))
    text_segment = elf.get_section_by_name(".text")

    # find the first loadable segment that is loaded with execute perms
    # this will always be the .text segment
    for segment in elf.iter_segments():
      if segment.header.p_flags & elftools.elf.constants.P_FLAGS.PF_X and \
         segment.section_in_segment(text_segment):
        # this is hard coded because from a loaders perspective ELF only knows 
        # loadable segments. The first executable one is always the ".text" segment
        segment_name += ".text_segment"
        if not self.base_addr:
          starting_addr = segment.header.p_vaddr
        else:
          starting_addr = options.base

        segment_bytes = segment.data()
        yield segment_name, starting_addr, segment_bytes


  def ReadPEFile(self, filename):
    """
    Read a PE32/PE32+ file and find ROP gadgets in its text section.

    Args:
      filename: a string path to the file name.

    Yields:
      A 3 tuple of: 
         -- segement_name (string) 
         -- starting_addr (integer)
         -- segment_bytes (string)
    """
    segment_name = filename
    starting_addr = 0x0
    segment_bytes = ""
    pe = pefile.PE(filename)
    
    for section in pe.sections:
      if section.Characteristics & pefile.SECTION_CHARACTERISTICS['IMAGE_SCN_MEM_EXECUTE']:
        segment_name += section.Name.replace('\x00','')
        
        if not self.base_addr:
          starting_addr = pe.OPTIONAL_HEADER.ImageBase + section.VirtualAddress
        else:
          starting_addr = self.base_addr + section.VirtualAddress
          
        # we use bytearray because we want a mutable string
        segment_bytes = multiprocessing.Array(ctypes.c_char, section.get_data(), 
                                              lock=False)
        
        yield segment_name, starting_addr, segment_bytes

  def GetPageRanges(self):
    """
    Yield Page Ranges to start searching segments for gadgets.
    """
    process_func = self.ReturnReadFileFormatFunc(self.filename)

    for seg_name, starting_addr, seg_bytes in process_func():
      seg_len = len(seg_bytes) 
      offset = 0
      while offset < seg_len:
        end = offset + self.job_size
        
        if end > seg_len:
          end = seg_len

        yield (seg_name, starting_addr + offset, offset, end, seg_bytes)
        
        offset = end


class GadgetFinder(object):
  """
  Abstract base class for gadgets 
  """
  def __init__(self):
    raise NotImplementedError("Must be subclassed")

  def GetInstructionAlignment(self):
    """
    Return the required instruction alignment

    e.g. 1-byte on x86 or variable width instruction sets with 1-byte instrucitons
    e.g. 2-bytes for thumb
    e.g. 4-byte for mips, arm or arm64
    """
    return 1

  def ArchSupportsDirectPCAccess(self):
    """
    Return if architechture supports direct access of the Program Counter.
    """
    return False

  def IsTerminalInstruction(self, inst):
    """
    Determines if this instruction signifies the end of a gadget

    Args:
      inst: a capstone instruction for this given architechture

    Returns:
      True if this is a terminal instruction that would end a gadget.

      False otherwise.
    """
    if inst.id in self.branch_insts:
      if inst.id == self.ret_inst:
        return True

      for op in inst.operands:
        if op.type == self.reg_type:
          return True
        elif op.type == self.mem_type:
          if op.mem.base != 0:
            return True

      return False

    elif self.ArchSupportsDirectPCAccess():
      if self.pc_reg in inst.regs_write:
        for op in inst.operands:
          if op.type == self.reg_type and op.value != self.pc_reg:
            return True
      else:
        return False
    else:
      return False

  def IsUnsupportedBranch(self, inst):
    """
    Determines if this instruction signifies the end of a gadget

    Args:
      inst: a capstone instruction for this given architechture

    Returns:
      True if this is a terminal instruction that would end a gadget.

      False otherwise.
    """
    if inst.id in self.branch_insts:
      if inst.id == self.ret_inst:
        return False

      for op in inst.operands:
        if op.type == self.reg_type:
          return False
        elif op.type == self.mem_type:
          if op.mem.base != 0:
            return False

      return True

    elif self.ArchSupportsDirectPCAccess():

      regs_read, regs_write = inst.regs_access()

      if self.pc_reg in regs_write:

        for op in inst.operands:
          if op.type == self.reg_type and op.value != self.pc_reg:
            return False
        return True

    else:
      return False


class ARMGadgetFinder(GadgetFinder):
  """
  Class for handling Armv7 and thumb / thumb2
  """
  def __init__(self, mode):
    self.context = capstone.Cs(capstone.CS_ARCH_ARM, mode)
    self.context.detail = True
    self.branch_insts = (capstone.arm.ARM_INS_B, 
                         capstone.arm.ARM_INS_BX,
                         capstone.arm.ARM_INS_BL, 
                         capstone.arm.ARM_INS_BLX)
    self.pc_reg = capstone.arm.ARM_REG_PC
    self.reg_type = capstone.arm.ARM_OP_REG
    self.mem_type = capstone.arm.ARM_OP_MEM
    self.ret_inst = None

  def ArchSupportsDirectPCAccess(self):
    return True

  def GetInstructionAlignment(self):
    return 4


class ThumbGadgetFinder(GadgetFinder):
  def __init__(self, mode):
    self.context = capstone.Cs(capstone.CS_ARCH_ARM, mode)
    self.context.detail = True    
    self.branch_insts = (capstone.arm.ARM_INS_B, 
                         capstone.arm.ARM_INS_BX,
                         capstone.arm.ARM_INS_BL, 
                         capstone.arm.ARM_INS_BLX)

    self.pc_reg = capstone.arm.ARM_REG_PC
    self.reg_type = capstone.arm.ARM_OP_REG
    self.mem_type = capstone.arm.ARM_OP_MEM
    self.ret_inst = None

  def ArchSupportsDirectPCAccess(self):
    return True

  def GetInstructionAlignment(self):
    return 4


class ARM64GadgetFinder(GadgetFinder):
  pass

class Mips32GadgetFinder(GadgetFinder):
  pass

class Mips64GadgetFinder(GadgetFinder):
  pass

class X86GadgetFinder(GadgetFinder):
  def __init__(self, mode):
    self.context = capstone.Cs(capstone.CS_ARCH_X86, mode)
    self.context.detail = True
    self.branch_insts = (capstone.x86.X86_INS_CALL, 
                         capstone.x86.X86_INS_JA,
                         capstone.x86.X86_INS_JAE,
                         capstone.x86.X86_INS_JB,
                         capstone.x86.X86_INS_JBE,
                         capstone.x86.X86_INS_JCXZ,
                         capstone.x86.X86_INS_JE,
                         capstone.x86.X86_INS_JECXZ,
                         capstone.x86.X86_INS_JG,
                         capstone.x86.X86_INS_JGE,
                         capstone.x86.X86_INS_JL,
                         capstone.x86.X86_INS_JLE,
                         capstone.x86.X86_INS_JMP,
                         capstone.x86.X86_INS_JNE,
                         capstone.x86.X86_INS_JNO,
                         capstone.x86.X86_INS_JNP,
                         capstone.x86.X86_INS_JNS,
                         capstone.x86.X86_INS_JO,
                         capstone.x86.X86_INS_JP,
                         capstone.x86.X86_INS_JRCXZ,
                         capstone.x86.X86_INS_JS,
                         capstone.x86.X86_INS_RET,
                         capstone.x86.X86_INS_SYSCALL,
                         capstone.x86.X86_INS_SYSENTER)
    self.ret_inst = capstone.x86.X86_INS_RET

    if mode == capstone.CS_MODE_16:
      self.pc_reg = capstone.x86.X86_REG_IP
    elif mode == capstone.CS_MODE_32:
      self.pc_reg = capstone.x86.X86_REG_EIP
    elif mode == capstone.CS_MODE_64:
      self.pc_reg = capstone.x86.X86_REG_RIP
    else:
      raise NotImplementedError("Unsupported mode")
    self.reg_type = capstone.x86.X86_OP_REG
    self.mem_type = capstone.x86.X86_OP_MEM



def CreateGadgetFinder(cpu):
  """
  Create a capstone disassembler context from a cpu and mode strings

  Args:
    cpu: a string naming the CPU

  Returns:
    a capstone disassembly object
  """
  gadget_finders = {"x86": (X86GadgetFinder, capstone.CS_MODE_32),
                    "x86-16": (X86GadgetFinder, capstone.CS_MODE_16),
                    "x64": (X86GadgetFinder, capstone.CS_MODE_64),
                    "arm": (ARMGadgetFinder, capstone.CS_MODE_ARM + capstone.CS_MODE_LITTLE_ENDIAN),
                    "arm-be": (ARMGadgetFinder, capstone.CS_MODE_ARM + capstone.CS_MODE_BIG_ENDIAN),
                    "thumb": (ThumbGadgetFinder, capstone.CS_MODE_THUMB + capstone.CS_MODE_LITTLE_ENDIAN),
                    "thumb-be": (ThumbGadgetFinder, capstone.CS_MODE_THUMB + capstone.CS_MODE_BIG_ENDIAN),
                    "arm64": (ARM64GadgetFinder, capstone.CS_MODE_V8 + capstone.CS_MODE_LITTLE_ENDIAN)}

  if cpu not in gadget_finders:
    raise NotImplementedError("CPU type: {cpu} not supported".format(cpu=cpu))
  else:
    finder, mode = gadget_finders[cpu]

  return finder(mode)


def ConfigureLogging(arg):
  levels = {'warn': logging.WARN, 'info': logging.INFO, 'debug': logging.DEBUG}
  logger = multiprocessing.log_to_stderr()
  logger.setLevel(levels[arg])

def IntOrHextInt(value):
  if value.startswith('0x'):
    return int(value, 16)
  else:
    return int(value)


def FindGadget(seg_name, segment, starting_addr, offset, finder):
  """
  Disassemble until you find a jmp reg, call reg, or ret

  Args:
    seg_name: a string name (not used)
    segment: a string containing all of the bytes in a segment.
    starting_addr: integer representing the starting VA of a segment.
    offset: a positive integer offset in the buffer
    finder: a GadgetFinder subclass

  Returns:
    A list of gadget instructions found from this offset.

  Side Effects:
    Fills the gadget queue with disassembled gadgets.
  """
  gadget = []
  buf = segment[offset:offset+256]

  for inst in finder.context.disasm(buf, starting_addr + offset):
    if inst.errno() != 0 or finder.IsUnsupportedBranch(inst):
      return []
    else:
      gadget.append(inst)

    if finder.IsTerminalInstruction(inst):
      # we've found a valid gadget now add it to our queue
      return gadget

  return []


def PrintGadget(segment_name, gadget):
  """
  Print all of the gadgets we've found
  """
  for inst in gadget:
    print ("%s :\t%s %s" % (hex(inst.address).replace('L',''), 
                           binascii.hexlify(inst.bytes).ljust(17, ' '),
                           "%s %s" % (inst.mnemonic, inst.op_str)))
  print ('--')


def FindGadgetsWorkerProcess(job_queue, gadget_queue, end_event, semaphore, finder):
  """
  Worker Process for finding gadgets
  """
  logger = multiprocessing.get_logger()
  gq = GadgetQueuePullStub(job_queue)
  job_queue = gq.GetQueue()
  gq.start()
  
  alignment = finder.GetInstructionAlignment()

  while True:
    job = job_queue.get()
    semaphore.acquire()
    
    if job == FINISHED_MESSAGE:
      logger.debug("Shutting down worker")
      end_event.set()
      semaphore.release()
      break

    name, base_addr, start, end = job
    logger.warn("Processing job for %s: %s offset: %s end: %s" % (name, 
                                                                  hex(base_addr), 
                                                                  hex(start),
                                                                  hex(end)))

    for offset in xrange(start, end, alignment):
      gadget = FindGadget(name, CURRENT_SEGMENT, base_addr, offset, finder)

      if gadget:
        PrintGadget(name, gadget)
        pass
      
    logger.warn("Finished Processing job for %s: %s offset: %s end: %s" % (name, 
                                                                  hex(base_addr), 
                                                                  hex(start),
                                                                  hex(end)))
    semaphore.release()



def SpawnGadgetProcesses(number, finder):
  """
  Spawn worker threads for finding indices of terminal instructions and gadgets

  Args:
    gadget_queue: a Multiprocess.JoinableQueue instance

  Returns:
    a lists of Processes objects
  """
  job_queue = "ipc://gadget_job_queue"
  gadget_queue = "ipc://gadget_queue"

  semaphore = multiprocessing.Semaphore(number)

  gadget_processes = []

  for i in xrange(number):
    finished_event = multiprocessing.Event()
    t = multiprocessing.Process(target=FindGadgetsWorkerProcess, 
                                args=(job_queue, gadget_queue,
                                      finished_event, semaphore, finder))
    t.daemon = True
    t.start()
    gadget_processes.append((t, finished_event)) 

  return gadget_processes, GadgetQueuePushStub(job_queue, semaphore), gadget_queue


def FillCurrentSegment(sect_bytes):
  logger = multiprocessing.get_logger()
  logger.debug("Filling Shared memory")
  
  #TODO there has to be a faster way to do this.
  CURRENT_SEGMENT[:len(sect_bytes)] = sect_bytes


def WaitForWorkerPoolToFinish(worker_pool, worker_queue, pool_name=""):
  """
  Wait for a set of workers to finish processing. This will keep spamming the
  worker queue with finished messages until they're all stopped this is to
  avoid zmq issues
  """
  logger = multiprocessing.get_logger()
  logger.warn("Waiting for workers in %s pool to finish" % pool_name)
  
  time.sleep(5.0)
  
  for worker,event in worker_pool:
    worker_queue.put(FINISHED_MESSAGE)

  for worker,event in worker_pool:
    logger.debug("Waiting for worker %s" % str(worker))
    if event.wait(0.2):
      logger.debug("Worker %s Finished" % str(worker))
   
  logger.warn("All workers have finished")


def ParseArgs():
  """
  Parse commandline options and arguments
  """
  parser = argparse.ArgumentParser()
  parser.add_argument('-b', '--base', type=IntOrHextInt, dest='base_addr',
                      help='set the base address for the module to x')
  parser.add_argument('-l', '--logging', dest='log_level', type=ConfigureLogging, default="warn",
                      help='Activate multiprocessing logging and set it to the supplied level')
  parser.add_argument('-n','--finders', dest='num_finders', type=int, 
                      help='number of gadget finders to spawn', 
                      default=multiprocessing.cpu_count() - 2)
  parser.add_argument('-q', '--quiet', dest='quiet', action='store_true', default=False,
                      help='do not print the gadgets that were found')
  parser.add_argument('-r', '--raw', dest='raw', action='store_true', default=False,
                      help='treate files as raw memory dumps')
  parser.add_argument('-s', '--sqlite', dest='sqlite', 
                      help='log gadgets into the specified sqlite db')
  parser.add_argument('cpu', help='processor and mode to disassmble the input file with')
  parser.add_argument('input_file',
                      help='This is a PE / ELF file / otool dump / raw memory dump')

  args = parser.parse_args()

  args.gadget_finder = CreateGadgetFinder(args.cpu)

  return args


def Main():
  """
  Program entry point
  """
  args = ParseArgs()
  finder = args.gadget_finder
  logger = multiprocessing.get_logger()

  #if args.sqlite:
  #  db = InitializeDatabase(args.sqlite)

  # extract the r-x sections and the base addresses of each module
  # map the sections as necessary
  section_store = SectionStore(args.input_file, args.base_addr, raw=args.raw)

  finder_pool, job_queue, gadget_queue = SpawnGadgetProcesses(args.num_finders, finder)
  time.sleep(1.0)

  ## TODO create our thread pool of gadget processors
  last_name = None
  
  for name, base_addr, start, stop, sect_bytes in section_store.GetPageRanges():
    if not last_name or (last_name and name != last_name):
      last_name = name
      FillCurrentSegment(sect_bytes)

    job_queue.put((name, base_addr, start, stop))

  WaitForWorkerPoolToFinish(finder_pool, job_queue, "Gadget Worker")
  #Wait for database processing to finish

if __name__ == '__main__':
  Main()
