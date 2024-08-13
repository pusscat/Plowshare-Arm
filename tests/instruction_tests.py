import importlib
import os
import sys
import unittest
import code
import struct

code_path = os.path.dirname(__file__)
code_path = os.path.join(code_path, os.pardir)
sys.path.append(code_path)

sys.path.append(os.path.join("..", "..", "remoteAssembler", "local"))

from remAsm import RemAsm


import capstone
import z3

import instructions
import constraint_dsl

class BasicInstructionTest(unittest.TestCase):
    def checkSequence(self, constraints, instruction_bytes):
        base = 0x10000
        cpu = instructions.CPU(32, instruction_bytes, base)

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, 0x10000)

        #cpu.ModelCode(base)

        s = z3.Solver()
        sat_constraints = []

        for const in constraints:
            sat_const, unsat_const = constraint_dsl.ParseConstraint(cpu, const)
            s.add(unsat_const)
            sat_constraints.append(sat_const)

        self.assertEqual(s.check(), z3.unsat)
        s = z3.Solver()
        s.add(sat_constraints)
        self.assertEqual(s.check(), z3.sat)

    def testAllTheThings(self):
        instruction_bytes = []
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("mov r1, r0")

        for opcodes in instruction_bytes:
            self.checkSequence(["r0_start == r0_start"], opcodes)

class TestGadgets(unittest.TestCase):
    def testXENO(self):
        base = 0x10000
        gadget2 = 0x10200
        stack = 0x30000
        remote = RemAsm("ARM32")
        instruction_bytes  = remote.Assemble("add r2, sp, #0x34")
        instruction_bytes += remote.Assemble("blx r5")
        cpu = instructions.CPU(32, instruction_bytes, base)

        instruction_bytes2 = remote.Assemble("mov r0, r2")
        instruction_bytes2 += remote.Assemble("ldm sp!, {r4-r6, pc}")
        cpu.InitMemoryBlock(gadget2, instruction_bytes2)

        cpu.SetRegister('r2', z3.BitVecVal(0x00000000, cpu.bitwidth))
        cpu.SetRegister('r5', z3.BitVecVal(gadget2, cpu.bitwidth))
        cpu.SetRegister('sp', z3.BitVecVal(stack, cpu.bitwidth))

        stackData = "\x41\x41\x41\x41\x42\x42\x42\x42\x43\x43\x43\x43\x44\x43\x42\x41"
        cpu.InitMemoryBlock(stack, stackData)

        cpu.ModelCode(base)

        self.assertEqual(cpu.GetRegisterValue('r0').as_long(), stack+0x34)
        self.assertEqual(cpu.GetRegisterValue('pc').as_long(), 0x41424344)

class TestMov(unittest.TestCase):
    def testMovRegReg(self):
        # MOV REG, REG and check zero flag
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("movs r1, r0")
        cpu = instructions.CPU(32)
        cpu.SetRegister("R0", z3.BitVecVal(0x0000, 32))
        cpu.SetRegister("R1", z3.BitVecVal(0x4141, 32))
        cpu.SetRegister("CPSR", z3.BitVecVal(0x0, 32))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, 0x10000)
        cpu.DoMov(list(insts)[0])

        self.assertEqual(cpu.GetRegisterValue('r0').as_long(), 0x0000)
        self.assertEqual(cpu.GetRegisterValue('r1').as_long(), 0x0000)

        self.assertEqual(cpu.GetRegisterValue('CPSR').as_long(), 1 << 30) # Z

    def testMovRegImmNoShift(self):
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("movs r2, #0x41")
        cpu = instructions.CPU(32)
        cpu.SetRegister("R2", z3.BitVecVal(0x0000, 32))
        cpu.SetRegister("CPSR", z3.BitVecVal(1 << 30, 32)) # Set Z to make sure its unset

        
        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, 0x10000)
        cpu.DoMov(list(insts)[0])


        self.assertEqual(cpu.GetRegisterValue('r2').as_long(), 0x41)
        self.assertEqual(cpu.GetRegisterValue('cpsr').as_long(), 0x0000)

    def testMovRegRegLSLImm(self):
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("MOV r0, r0, LSL #1")
        cpu = instructions.CPU(32)
        cpu.SetRegister("R0", z3.BitVecVal(0x0041, 32))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, 0x10000)
        cpu.DoMov(list(insts)[0])
        
        self.assertEqual(cpu.GetRegisterValue('r0').as_long(), 0x82)

    # FAILS - capstone bug
    def testMovRegRegLSLReg(self):
        return 
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("MOV r0, r0, LSL R1")
        cpu = instructions.CPU(32)
        cpu.SetRegister("R0", z3.BitVecVal(0x0041, 32))
        cpu.SetRegister("R1", z3.BitVecVal(0x0001, 32))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, 0x10000)
        cpu.DoMov(list(insts)[0])
        
        self.assertEqual(cpu.GetRegisterValue('r0').as_long(), 0x82)


class  TestLoad(unittest.TestCase):
    def testBlxReg(self):
        base = 0x10000
        stack = 0x30000
        address = 0x10200
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("blx r5")
        cpu = instructions.CPU(32)
        cpu.SetRegister('PC', z3.BitVecVal(base, cpu.bitwidth))
        cpu.SetRegister('R5', z3.BitVecVal(address, cpu.bitwidth))
        cpu.SetRegister('SP', z3.BitVecVal(stack, cpu.bitwidth))

        
        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        cpu.DoBlx(list(insts)[0])

        self.assertEqual(cpu.GetRegisterValue('LR').as_long(), base+4)
        self.assertEqual(cpu.GetRegisterValue('PC').as_long(), address)


    def testLdrRegRegImm(self):
        base = 0x10000
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("LDR r3, [r0], #4")
        cpu = instructions.CPU(32)
        address = 0x10200
        value = 0x41424344
        cpu.SetRegister('R0', z3.BitVecVal(address, 32))
        cpu.SetRegister('R3', z3.BitVecVal(0x00, 32))
        cpu.SetMemory(address, cpu.bitwidth, z3.BitVecVal(value, cpu.bitwidth))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        cpu.DoLdr(list(insts)[0])


        self.assertEqual(cpu.GetRegisterValue('r3').as_long(), value)

    def testLdrRegMem(self):
        base = 0x10000
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("LDR r1, =0x10200")

        cpu = instructions.CPU(32, instruction_bytes, base)
        cpu.SetRegister('R1', z3.BitVecVal(0x00, 32))
        cpu.SetRegister('PC', z3.BitVecVal(base+8, 32))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        cpu.DoLdr(list(insts)[0])
        
        self.assertEqual(cpu.GetRegisterValue('r1').as_long(), 0x10200)

    def testPop(self):
        base = 0x10000
        spAddr = 0x10200
        val4 = 0x44444444
        val5 = 0x45454545
        val6 = 0x46464646
        pc = 0x47474747
        remote = RemAsm('ARM32')
        instruction_bytes = remote.Assemble("ldm sp!, {r4-r6, pc}")

        cpu = instructions.CPU(32, instruction_bytes, base)
        cpu.SetRegister('SP', z3.BitVecVal(spAddr, 32))
        cpu.SetRegister('R4', z3.BitVecVal(0x00, 32))
        cpu.SetRegister('R5', z3.BitVecVal(0x00, 32))
        cpu.SetRegister('R6', z3.BitVecVal(0x00, 32))
        cpu.SetMemory(spAddr, cpu.bitwidth, z3.BitVecVal(val4, cpu.bitwidth))
        cpu.SetMemory(spAddr+4, cpu.bitwidth, z3.BitVecVal(val5, cpu.bitwidth))
        cpu.SetMemory(spAddr+8, cpu.bitwidth, z3.BitVecVal(val6, cpu.bitwidth))
        cpu.SetMemory(spAddr+0xC, cpu.bitwidth, z3.BitVecVal(pc, cpu.bitwidth))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        moo = list(insts)
        cpu.DoLdm(moo[0])
       

        self.assertEqual(cpu.GetRegisterValue('r4').as_long(), val4)
        self.assertEqual(cpu.GetRegisterValue('r5').as_long(), val5)
        self.assertEqual(cpu.GetRegisterValue('r6').as_long(), val6)
        self.assertEqual(cpu.GetRegisterValue('pc').as_long(), pc)


    def testLdm(self):
        base = 0x10000
        spAddr = 0x10200
        val4 = 0x44444444
        val5 = 0x45454545
        val6 = 0x46464646
        pc = 0x47474747
        remote = RemAsm('ARM32')
        instruction_bytes = remote.Assemble("ldm r0!, {r4-r6, pc}")

        cpu = instructions.CPU(32, instruction_bytes, base)
        cpu.SetRegister('R0', z3.BitVecVal(spAddr, 32))
        cpu.SetRegister('R4', z3.BitVecVal(0x00, 32))
        cpu.SetRegister('R5', z3.BitVecVal(0x00, 32))
        cpu.SetRegister('R6', z3.BitVecVal(0x00, 32))
        cpu.SetMemory(spAddr, cpu.bitwidth, z3.BitVecVal(val4, cpu.bitwidth))
        cpu.SetMemory(spAddr+4, cpu.bitwidth, z3.BitVecVal(val5, cpu.bitwidth))
        cpu.SetMemory(spAddr+8, cpu.bitwidth, z3.BitVecVal(val6, cpu.bitwidth))
        cpu.SetMemory(spAddr+0xC, cpu.bitwidth, z3.BitVecVal(pc, cpu.bitwidth))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        moo = list(insts)
        cpu.DoLdm(moo[0])


        self.assertEqual(cpu.GetRegisterValue('r4').as_long(), val4)
        self.assertEqual(cpu.GetRegisterValue('r5').as_long(), val5)
        self.assertEqual(cpu.GetRegisterValue('r6').as_long(), val6)
        self.assertEqual(cpu.GetRegisterValue('pc').as_long(), pc)




class TestStore(unittest.TestCase):
    def testStrRegRegSize(self):
        base = 0x10000
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("str r0, [r1], #4")
        cpu = instructions.CPU(32, instruction_bytes, base)

        address = 0x10200
        value = 0x41424344
        cpu.SetRegister('R1', z3.BitVecVal(address, 32))
        cpu.SetRegister('R0', z3.BitVecVal(value, 32))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        cpu.DoStr(list(insts)[0])

        self.assertEqual(cpu.ReadMemory(address, cpu.bitwidth).as_long(), value)

    def testPushRegs(self):
        base = 0x10000
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("push {r4-r6}")
        cpu = instructions.CPU(32, instruction_bytes, base)

        r4Val = 0x44444444
        r5Val = 0x55555555
        r6Val = 0x66666666
        spVal = 0x30000
        cpu.SetRegister('R4', z3.BitVecVal(r4Val, cpu.bitwidth))
        cpu.SetRegister('R5', z3.BitVecVal(r5Val, cpu.bitwidth))
        cpu.SetRegister('R6', z3.BitVecVal(r6Val, cpu.bitwidth))
        cpu.SetRegister('SP', z3.BitVecVal(spVal, cpu.bitwidth))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        cpu.DoStm(list(insts)[0])

        self.assertEqual(cpu.ReadMemory(spVal, cpu.bitwidth).as_long(), r4Val)
        self.assertEqual(cpu.ReadMemory(spVal+4, cpu.bitwidth).as_long(), r5Val)
        self.assertEqual(cpu.ReadMemory(spVal+8, cpu.bitwidth).as_long(), r6Val)
        self.assertEqual(cpu.GetRegisterValue('sp').as_long(), spVal+(cpu.ptrSize*3))

class TestSwp(unittest.TestCase):
    def testRegRegMem(self):
        base = 0x10000
        r2Addr = 0x20000
        val1 = 0x1
        val2 = 0x2
        val3 = 0x3
        val4 = 0x4

        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("swp r0, r1, [r2]")

        cpu = instructions.CPU(32, instruction_bytes, base)
        cpu.SetRegister('r0', z3.BitVecVal(val1, cpu.bitwidth))
        cpu.SetRegister('r1', z3.BitVecVal(val2, cpu.bitwidth))
        cpu.SetRegister('r2', z3.BitVecVal(r2Addr, cpu.bitwidth))
        cpu.SetMemory(r2Addr, cpu.bitwidth, z3.BitVecVal(val4, cpu.bitwidth))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        cpu.DoSwp(list(insts)[0])

        self.assertEqual(cpu.GetRegisterValue('r0').as_long(), val4)
        self.assertEqual(cpu.ReadMemory(r2Addr, cpu.bitwidth).as_long(), val2)

class TestAdd(unittest.TestCase):
    def testAddRegReg(self):
        base = 0x10000
        val1 = 0x4100
        val2 = 0x0042
        
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("add r0, r1, r2")
        
        cpu = instructions.CPU(32, instruction_bytes, base)

        cpu.SetRegister('r1', z3.BitVecVal(val1, 32))
        cpu.SetRegister('r2', z3.BitVecVal(val2, 32))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        cpu.DoAdd(list(insts)[0])

        self.assertEqual(cpu.GetRegisterValue('r0').as_long(), val1+val2)

class TestSub(unittest.TestCase):
    def testSubRegReg(self):
        base = 0x10000
        val1 = 0x4100
        val2 = 0x0042
        
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("sub r0, r1, r2")
        
        cpu = instructions.CPU(32, instruction_bytes, base)

        cpu.SetRegister('r1', z3.BitVecVal(val1, 32))
        cpu.SetRegister('r2', z3.BitVecVal(val2, 32))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        cpu.DoSub(list(insts)[0])

        self.assertEqual(cpu.GetRegisterValue('r0').as_long(), val1-val2)

    def testRsbRegReg(self):
        base = 0x10000
        val2 = 0x4100
        val1 = 0x0042
        
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("rsb r0, r1, r2")
        
        cpu = instructions.CPU(32, instruction_bytes, base)

        cpu.SetRegister('r1', z3.BitVecVal(val1, 32))
        cpu.SetRegister('r2', z3.BitVecVal(val2, 32))

        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        cpu.DoRsb(list(insts)[0])

        self.assertEqual(cpu.GetRegisterValue('r0').as_long(), val2-val1)

class TestConditions(unittest.TestCase):
    def testAddZeroCond(self):
        base = 0x10000
        origVal = 0x6969
        val1 = 0x4100
        val2 = 0x0042
        remote = RemAsm("ARM32")
        instruction_bytes = remote.Assemble("addeq r0, r1, r2")
        #print ' '.join(x.encode('hex') for x in instruction_bytes)

        cpu = instructions.CPU(32, instruction_bytes, base)

        cpu.SetRegister('r0', z3.BitVecVal(origVal, 32))
        cpu.SetRegister('r1', z3.BitVecVal(val1, 32))
        cpu.SetRegister('r2', z3.BitVecVal(val2, 32))
        cpu.SetRegister('CPSR', z3.BitVecVal(0x00, 32))


        md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        md.detail = True
        insts = md.disasm(instruction_bytes, base)
        moo = list(insts)[0]
        cpu.DoAdd(moo)

        self.assertEqual(cpu.GetRegisterValue('r0').as_long(), origVal)

        cpu.SetFlag('Z', True)
        cpu.DoAdd(moo)
        self.assertEqual(cpu.GetRegisterValue('r0').as_long(), val1+val2)


if __name__ == '__main__':
    unittest.main()
