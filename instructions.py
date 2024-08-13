"""
instructions.py  -- objects and instructions for ARM symbolic execution

Author: Lurene
"""

# generic imports
import binascii
import os
import platform
import sys
import gc
import struct
import code

# 3rd party dependencies
import capstone
import z3

# app specific
from const_strings import *


def rname(operand):
    return REG_STRINGS[operand.reg].split('_')[2] 

class zomgError(Exception):
    pass

class RegOperand(object):
    def __init__(self, name):
        self.name = name
        self.type = 'Register'

    def __str__(self):
        return self.name

class MemOperand(object):
    def __init__(self, string, size):
        self.name = ''
        self.type = 'AbsoluteMemoryAddress'
        self.string = string
        self.size = size

    def __str__(self):
        return self.string

class Register(object):
    def __init__(self, name, alias, bitwidth):
        self.name = name
        self.alias = alias
        self.bitwidth = bitwidth
        self.value = [z3.BitVec(self.name, bitwidth)]

    def GetCurrentValue(self):
        return self.value[-1]

    def GetInitialValue(self):
        return self.value[0]

    def SetInitialValue(self, value):
        self.value[0] = value


"""
Main CPU state object
"""
class CPU(object):
    def __init__(self, bitwidth, instruction_bytes=None, base=None):
        self.regs = [Register('R0', '', bitwidth),
                     Register('R1', '', bitwidth),
                     Register('R2', '', bitwidth),
                     Register('R3', '', bitwidth),
                     Register('R4', '', bitwidth),
                     Register('R5', '', bitwidth),
                     Register('R6', '', bitwidth),
                     Register('R7', '', bitwidth),
                     Register('R8', '', bitwidth),
                     Register('R9', '', bitwidth),
                     Register('R10', '', bitwidth),
                     Register('R11', '', bitwidth),
                     Register('R12', '', bitwidth),
                     Register('R13', 'SP', bitwidth),
                     Register('R14', 'LR', bitwidth),
                     Register('R15', 'PC', bitwidth),
                     Register('R16', 'CPSR', bitwidth)]

        self.bitwidth = bitwidth
        self.ptrSize = bitwidth / 8
        self.memory = z3.Array('mem', z3.BitVecSort(bitwidth), z3.BitVecSort(8))
        
        self.ARM_MODE = z3.BitVecVal(0, 1)
        self.THUMB_MODE = z3.BitVecVal(1, 1)
        self.currentMode = self.ARM_MODE
        self.instructionSize = 4 # thumb isnt implemented yet XXX

        self.currentInst = None
        self.error_log = open('error_log.txt', 'a+')

        # Types by CPU type
        if bitwidth == 32:
            self.pcReg = capstone.arm.ARM_REG_PC
            self.regType = capstone.arm.ARM_OP_REG
            self.immType = capstone.arm.ARM_OP_IMM
            self.memType = capstone.arm.ARM_OP_MEM
            self.invalidShift = capstone.arm.ARM_SFT_INVALID
            self.invalidCond = capstone.arm.ARM_CC_INVALID
            self.alwaysCond = capstone.arm.ARM_CC_AL
            self.zsetCond = capstone.arm.ARM_CC_EQ
            self.zclearCond = capstone.arm.ARM_CC_NE 
            self.vsetCond = capstone.arm.ARM_CC_VS
            self.vclearCond = capstone.arm.ARM_CC_VC 
            self.csetCond = capstone.arm.ARM_CC_HS
            self.cclearCond = capstone.arm.ARM_CC_LO 
            self.miCond = capstone.arm.ARM_CC_MI
            self.plCond = capstone.arm.ARM_CC_PL
            self.hiCond = capstone.arm.ARM_CC_HI 
            self.lsCond = capstone.arm.ARM_CC_LS 
            self.geCond = capstone.arm.ARM_CC_GE
            self.leCond = capstone.arm.ARM_CC_LE
            self.gtCond = capstone.arm.ARM_CC_GT
            self.ltCond = capstone.arm.ARM_CC_LT


        if bitwidth == 64:
            self.pcReg = capstone.arm64.ARM64_REG_PC
            self.regType = capstone.arm64.ARM64_OP_REG
            self.immType = capstone.arm64.ARM64_OP_IMM
            self.memType = capstone.arm64.ARM64_OP_MEM
            self.invalidShift = capstone.arm64.ARM64_SFT_INVALID
            self.invalidCond = capstone.arm64.ARM64_CC_INVALID
            self.alwaysCond = capstone.arm64.ARM64_CC_AL

        if instruction_bytes != None and base != None:
            for i in xrange(0, len(instruction_bytes)):
                nextByte =  z3.BitVecVal(struct.unpack('B', instruction_bytes[i:i+1])[0],8)
                #print (hex(i) + " " + hex(struct.unpack('B', instruction_bytes[i:i+1])[0]))
                self.SetMemory(base+i, 8, nextByte)


    def ReadMemory(self, address, bitwidth):
        # Read little endian from memory
        value = z3.Select(self.memory, address)
        for i in xrange(1, bitwidth/8):
            value = z3.Concat(z3.Select(self.memory, address+i), value)
        return z3.simplify(value)
    
    def ReadMemoryBytes(self, address, sizeInBytes):
        return self.ReadMemory(address, sizeInBytes*8)

    def SetMemory(self, address, bitwidth, newValue):
        # Write little endian to memory
        for i in xrange(0, bitwidth/8):
            # Grab 8 bits at a time
            nextByte = z3.simplify(z3.Extract(7 + (8*i), 0 + (8*i), newValue))
            self.memory = z3.Store(self.memory, address + i, nextByte)

    def CreateCarryFlagCondition(self, oldDstVal, oldSrcVal, subOp):
        maxInt = ~z3.BitVecVal(0, oldDstVal.size())

        if subOp:
            return z3.UGT(~oldSrcVal + 1, oldDstVal)
        else:
            return z3.And(z3.UGT(oldSrcVal, 0), z3.UGT(oldDstVal, (maxInt - oldSrcVal)))

    def CreateOverflowFlagCondition(self, oldDstVal, oldSrcVal, bitwidth):
        op1 = z3.Extract(bitwidth-1, bitwidth-2, oldDstVal)
        op2 = z3.Extract(bitwidth-1, bitwidth-2, oldSrcVal)
        ofCond = (((op1 ^ op2) ^ 0x2) & (((op1 + op2) ^ op2) & 0x2)) != 0

        return ofCond

    def UpdateFlags(self, flags, oldDstVal, oldSrcVal, newVal, bitwidth, carry, subOp):
        ofCond = self.CreateOverflowFlagCondition(oldDstVal, oldSrcVal, bitwidth)
        cfCond = self.CreateCarryFlagCondition(oldDstVal, oldSrcVal, subOp)

        validFlags = {'N': ((newVal & (1 << bitwidth - 1)) != 0),
                      'Z': newVal == 0,
                      'C': cfCond == True,
                      'V': ofCond == True }

        for flag in flags:
            self.SetFlag(flag, validFlags[flag])
        
    def SetFlag(self, flagName, condition):
        flags = {'N': 31,
                 'Z': 30,
                 'C': 29,
                 'V': 28,
                 'J': 24,
                 'T': 5}

        flagReg = self.GetRegisterValue('CPSR')

        conditionMet = flagReg | z3.BitVecVal(1 << flags[flagName], self.bitwidth)
        conditionNotMet = flagReg & z3.BitVecVal(~(1 << flags[flagName]), self.bitwidth)

        rhs = z3.simplify(z3.If(condition, conditionMet, conditionNotMet))

        self.SetRegister('CPSR', rhs)

    def GetFlag(self, flagName):
        flags = {'N': 31,
                 'Z': 30,
                 'C': 29,
                 'V': 28,
                 'J': 24,
                 'T': 5}

        flagsReg = self.GetRegisterValue('CPSR')
        flagIndex = flags[flagName]

        return z3.simplify(z3.Extract(flagIndex, flagIndex, flagsReg))

    def GetPCObj(self):
        return self.regs[15]

    def SetPC(self, value):
        self.regs[15].value.append(value)

    def IncPC(self, instruction):
        regs_read, regs_write = instruction.regs_access()
        if self.pcReg in regs_write:
            return 0
        
        PC = self.GetPCObj()
        return self.SetPC(z3.simplify(PC.GetCurrentValue() + self.instructionSize))

    def GetSPObj(self):
        return self.regs[13]

    def SetSP(self, value):
        self.regs[13].value.append(value)
        return value

    def GetRegisterObjectByName(self, regName):
        regName = regName.upper()
        for reg in self.regs:
            if regName == reg.name or regName == reg.alias:
                return reg

    def SetRegister(self, regName, value):
        regObj = self.GetRegisterObjectByName(regName)
        currentVal = regObj.GetCurrentValue()

        if self.bitwidth != value.size():
            value = z3.Extract(self.bitwidth - 1, 0, value)
            value = z3.ZeroExt(self.bitwidth - value.size(), value)
        regObj.value.append(z3.simplify(value))
        return regObj.GetCurrentValue()

    def SetRegisterInitialValue(self, regName, value):
        regObj = self.GetRegisterObjectByName(regName)
        regObj.SetInitialValue(z3.simplify(value))
        return regOvj.GetCurrentValue()

    def GetRegisterValue(self, regName):
        regObj = self.GetRegisterObjectByName(regName)
        return regObj.GetCurrentValue()

    def GetRegisterInitialValue(self, regName):
        regObj = self.GetRegisterObjectByName(regName)
        return regObj.GetInitialValue()

    def ShiftValue(self, value, shiftType, shiftValue):
        # REGISTER SHIFTS ARE NOT WORKING IN CAPSTONE :(
        if shiftType == capstone.arm.ARM_SFT_ASR_REG or \
           shiftType == capstone.arm.ARM_SFT_LSL_REG or \
           shiftType == capstone.arm.ARM_SFT_LSR_REG or \
           shiftType == capstone.arm.ARM_SFT_ROR_REG or \
           shiftType == capstone.arm.ARM_SFT_RRX_REG:
            shiftValue = self.GetRegisterValue(rname(shiftValue))

        if shiftType == capstone.arm.ARM_SFT_ASR or shiftType == capstone.arm.ARM_SFT_ASR_REG:
            value = z3.simplify(value >> shiftValue)
        if shiftType == capstone.arm.ARM_SFT_LSL or shiftType == capstone.arm.ARM_SFT_LSL_REG:
            value = z3.simplify(value << shiftValue)
        if shiftType == capstone.arm.ARM_SFT_LSR or shiftType == capstone.arm.ARM_SFT_LSR_REG:
            value = z3.simplify(z3.LShR(value, shiftValue))
        if shiftType == capstone.arm.ARM_SFT_ROR or shiftType == capstone.arm.ARM_SFT_ROR_REG:
            value = z3.simplify(z3.RotateRight(value, shiftValue))
        if shiftType == capstone.arm.ARM_SFT_RRX or shiftType == capstone.arm.ARM_SFT_RRX_REG:
            carry = self.GetFlag('C')
            extended = z3.Concat(carry, value)
            newVal = z3.simplify(z3.RotateRight(extended, shiftValue))

            value = z3.Extract(self.bitwidth-1, 0, newVal)
            carry = z3.Extract(self.bitwidth, self.bitwidth-1, newVal)
            self.SetFlag('C', carry == 1)
        
        return value

    def MemOperToAddress(self, operand):
        base = self.GetRegisterValue(rname(operand))
        addr = base + operand.mem.disp

        return z3.simplify(addr)

    def GetOperandValue(self, operand):
        # Get shift if it exists
        shiftType = None
        shiftVal = None
        if operand.shift.type != self.invalidShift:
            if operand.shift.value != 0:
                shiftVal = operand.shift.value
                shiftType = operand.shift.type
        
       
        # Get value
        value = None
        if operand.type == self.regType:
            value = self.GetRegisterValue(rname(operand))
        if operand.type == self.immType:
            value = z3.BitVecVal(operand.imm, self.bitwidth)
        if operand.type == self.memType:
            addr = self.MemOperToAddress(operand)
            value = self.ReadMemory(addr, self.bitwidth)
        
        # Alert if unknown value type
        if value == None:
            print ("ERROR - Udefined operand type: " + OP_STRINGS[operand.type] + " val: " + operand.value)
            print ("name: " + operand.name + " mem: " + operand.mem)
            quit()

        # If shift, then shift the value
        if shiftType != None:
            value = self.ShiftValue(value, shiftType, shiftVal)

        return z3.simplify(value)

    def SetOperandValue(self, operand, value):
        if operand.type == self.regType:
            return self.SetRegister(rname(operand), value)

        # Is this all we need in ARM?? XXX

    def AddConditions(self, instruction, origValue, newValue):
        cond = instruction.cc

        if cond == self.invalidCond: return newValue
        if cond == self.alwaysCond: return newValue
        if cond == self.zsetCond:
            return z3.simplify(z3.If(self.GetFlag('Z') == 1, newValue, origValue))
        if cond == self.zclearCond:
            return z3.simplify(z3.If(self.GetFlag('Z') == 0, newValue, origValue))
        if cond == self.vsetCond:
            return z3.simplify(z3.If(self.GetFlag('V') == 1, newValue, origValue))
        if cond == self.vclearCond:
            return z3.simplify(z3.If(self.GetFlag('V') == 0, newValue, origValue))
        if cond == self.miCond:
            return z3.simplify(z3.If(self.GetFlag('N') == 1, newValue, origValue))
        if cond == self.plCond:
            return z3.simplify(z3.If(self.GetFlag('N') == 0, newValue, origValue))
        if cond == self.csetCond:
            return z3.simplify(z3.If(self.GetFlag('C') == 1, newValue, origValue))
        if cond == self.cclearCond:
            return z3.simplify(z3.If(self.GetFlag('C') == 0, newValue, origValue))
        if cond == self.hiCond: 
            return z3.simplify(z3.If(z3.And(self.GetFlag('C') == 1, self.GetFlag('Z') == 0), \
                                newValue, origValue))
        if cond == self.lsCond: 
            return z3.simplify(z3.If(z3.And(self.GetFlag('C') == 0, self.GetFlag('Z') == 1), \
                                newValue, origValue))
        if cond == self.geCond:
            return z3.simplify(z3.If(z3.Xnor(self.GetFlag('C'), self.GetFlag('Z')) == 1, \
                                newValue, origValue))
        if cond == self.ltCond: 
            return z3.simplify(z3.If(z3.Xnor(self.GetFlag('C'), self.GetFlag('Z')) == 0, \
                                newValue, origValue))
        if cond == self.gtCond: pass
        if cond == self.leCond: pass
    
        return newValue

    def InitMemoryBlock(self, address, data):
        for i in xrange(0, len(data)):
            nextByte =  z3.BitVecVal(struct.unpack('B', data[i:i+1])[0],8)
            self.SetMemory(address+i, 8, nextByte)


    def HandleInstructionAtPC(self):
        functionTable = {"MOV": self.DoMov,
                     "BLX": self.DoBlx,
                     "BL": self.DoBl,
                     "B": self.DoB,
                     "LDR": self.DoLdr,
                     "LDM": self.DoLdm,
                     "POP": self.DoLdm,
                     "STR": self.DoStr,
                     "STM": self.DoStm,
                     "PUSH": self.DoStm,
                     "SUB": self.DoSub,
                     "RSB": self.DoRsb,
                     "ADC": self.DoAdc,
                     "SBC": self.DoSbc,
                     "CMP": self.DoCmp,
                     "CMN": self.DoCmn,
                     "TST": self.DoTst,
                     "TEQ": self.DoTeq,
                     "SWP": self.DoSwp,
                     "BKPT": None,
                     "ADD": self.DoAdd}
        
        curPC = self.GetRegisterValue('PC')
        curInstAddr = z3.simplify(curPC).as_long()
        instBytes = ''
        for i in xrange(0, self.instructionSize):
            curInst = self.ReadMemoryBytes(curInstAddr, 1)
            try:
                instBytes += struct.pack('B', curInst.as_long())[0]
            except:
                return False
            curInstAddr += 1

        instructions = self.md.disasm(instBytes, curInstAddr)
        instruction = list(instructions)[0]

        if instruction.mnemonic.upper() not in functionTable.keys():
            print ("Unknown instruction: " + instruction.mnemonic)
            return False

        print (hex(curInstAddr) + ": " + instruction.mnemonic.upper())
        if "BKPT" in instruction.mnemonic.upper():
            return False
        functionTable[instruction.mnemonic.upper()](instruction)
        return True

    def ModelCode(self, startPC):
        startPC = z3.BitVecVal(startPC, self.bitwidth)
        self.SetRegister('PC', startPC) # adjust because ARM is insane with its pipeline
        
        self.md = capstone.Cs(capstone.CS_ARCH_ARM, capstone.CS_MODE_ARM)
        self.md.detail = True

        counter = 0
        maxInstructions = 200
        while self.HandleInstructionAtPC() != False and counter < maxInstructions:
            counter += 1
        
        print ("Executed %d instructions" % (counter))


    # INSTRUCTIONS!
    def DoMov(self, instruction):
        
        opers = instruction.operands
        dstOperand = opers[0]
        srcOperand = opers[1]

        srcVal = self.GetOperandValue(srcOperand)
        dstVal = self.GetOperandValue(dstOperand)

        if instruction.update_flags:
            self.UpdateFlags(['N', 'Z'], dstVal, srcVal, srcVal, 
                self.bitwidth, False,False)
   
        newVal = self.AddConditions(instruction, dstVal, srcVal)
        self.SetRegister(rname(dstOperand), newVal)
        return self.IncPC(instruction)

    def DoSwp(self, instruction):
        opers = instruction.operands

        RdOper = opers[0]
        RnAddr = self.MemOperToAddress(opers[2])

        RdVal = self.GetOperandValue(opers[0])
        RmVal = self.GetOperandValue(opers[1])
        RnVal = self.GetOperandValue(opers[2])

        self.SetRegister(rname(RdOper), RnVal)
        self.SetMemory(RnAddr, self.bitwidth, RmVal)
        return self.IncPC(instruction) 

    def DoLdr(self, instruction):

        opers = instruction.operands
        dstOperand = opers[0]
        addrOperand = opers[1]
        
        if len(opers) > 2:
            sizeOperand = opers[2]
            
            size = self.GetOperandValue(sizeOperand).as_long()*8
            addr = self.MemOperToAddress(addrOperand)


            value = self.ReadMemory(addr, size)
            value = z3.ZeroExt(self.bitwidth - size, value)
        
        else:
            value = self.GetOperandValue(addrOperand)
        
        dstVal = self.GetOperandValue(dstOperand)

        if instruction.update_flags:
            self.UpdateFlags(['N', 'Z'], dstVal, value, value, 
                self.bitwidth, False,False)
        
        newVal = self.AddConditions(instruction, dstVal, value)
        self.SetRegister(rname(dstOperand), newVal)
        return self.IncPC(instruction) 


    def DoStr(self, instruction):
        
        opers = instruction.operands
        srcOper = opers[0]
        addrOper = opers[1]

        size = self.bitwidth
        if len(opers) > 2:
            size = self.GetOperandValue(opers[2]).as_long() * 8

        addr = self.MemOperToAddress(addrOper)
        dstVal = self.ReadMemory(addr, size)
        value = self.GetOperandValue(srcOper)

        newVal = self.AddConditions(instruction, dstVal, value)
        self.SetMemory(addr, size, value)
        return self.IncPC(instruction) 



    def DoTst(self, instruction):
        opers = instruction.operands

        oper1 = self.GetOperandValue(opers[0])
        oper2 = self.GetOperandValue(opers[1])

        result = z3.simplify(z3.And(oper1, oper2))

        self.UpdateFlags(['N', 'Z'], oper1, oper2, result, self.bitwidth, False, False)

        return self.IncPC(instruction)


    def DoTeq(self, instruction):
        opers = instruction.operands

        oper1 = self.GetOperandValue(opers[0])
        oper2 = self.GetOperandValue(opers[1])

        result = z3.simplify(z3.Xor(oper1, oper2))

        self.UpdateFlags(['N', 'Z'], oper1, oper2, result, self.bitwidth, False, False)

        return self.IncPC(instruction)

    def DoCmp(self, instruction):
        opers = instruction.operands

        oper1 = self.GetOperandValue(opers[0])
        oper2 = self.GetOperandValue(opers[1])

        result = z3.simplify(oper1 - oper2)

        self.UpdateFlags(['N', 'Z', 'C', 'Z'], oper1, oper2, result, self.bitwidth, True, True)

        return self.IncPC(instruction)

    def DoCmn(self, instruction):
        opers = instruction.operands

        oper1 = self.GetOperandValue(opers[0])
        oper2 = self.GetOperandValue(opers[1])

        result = z3.simplify(oper1 + oper2)

        self.UpdateFlags(['N', 'Z', 'C', 'Z'], oper1, oper2, result, self.bitwidth, True, True)

        return self.IncPC(instruction)

    def DoAdd(self, instruction):
        
        opers = instruction.operands
        dstOper = opers[0]
        srcOper1 = opers[1]
        srcOper2 = opers[2]

        dstVal = self.GetOperandValue(dstOper)
        srcVal1 = self.GetOperandValue(srcOper1)
        srcVal2 = self.GetOperandValue(srcOper2)
        value = z3.simplify(srcVal1 + srcVal2)

        if instruction.update_flags:
            self.UpdateFlags(['N', 'Z', 'C', 'V'], dstVal, value, value, 
                self.bitwidth, False,False)

        newVal = self.AddConditions(instruction, dstVal, value)
        self.SetRegister(rname(dstOper), newVal)
        return self.IncPC(instruction)

    def DoAdc(self, instruction):
        
        opers = instruction.operands
        dstOper = opers[0]
        srcOper1 = opers[1]
        srcOper2 = opers[2]

        dstVal = self.GetOperandValue(dstOper)
        srcVal1 = self.GetOperandValue(srcOper1)
        srcVal2 = self.GetOperandValue(srcOper2)

        carryFlag = self.GetFlag("C")

        value = z3.simplify(srcVal1 + srcVal2 + z3.ZeroExt(self.bitwidth - 1, carryFlag))

        if instruction.update_flags:
            self.UpdateFlags(['N', 'Z', 'C', 'V'], dstVal, value, value, 
                self.bitwidth, True,False)

        newVal = self.AddConditions(instruction, dstVal, value)
        self.SetRegister(rname(dstOper), newVal)
        return self.IncPC(instruction)

    def DoSub(self, instruction):
        
        opers = instruction.operands
        dstOper = opers[0]
        srcOper1 = opers[1]
        srcOper2 = opers[2]

        dstVal = self.GetOperandValue(dstOper)
        srcVal1 = self.GetOperandValue(srcOper1)
        srcVal2 = self.GetOperandValue(srcOper2)
        value = z3.simplify(srcVal1 - srcVal2)

        if instruction.update_flags:
            self.UpdateFlags(['N', 'Z', 'C', 'V'], dstVal, value, value, 
                self.bitwidth, False,True)

        newVal = self.AddConditions(instruction, dstVal, value)
        self.SetRegister(rname(dstOper), newVal)
        return self.IncPC(instruction)

    def DoSbc(self, instruction):
        
        opers = instruction.operands
        dstOper = opers[0]
        srcOper1 = opers[1]
        srcOper2 = opers[2]

        dstVal = self.GetOperandValue(dstOper)
        srcVal1 = self.GetOperandValue(srcOper1)
        srcVal2 = self.GetOperandValue(srcOper2)
        
        carryFlag = self.GetFlag("C")

        value = z3.simplify(srcVal1 - srcVal2 -  z3.ZeroExt(self.bitwidth - 1, carryFlag))

        if instruction.update_flags:
            self.UpdateFlags(['N', 'Z', 'C', 'V'], dstVal, value, value, 
                self.bitwidth, False,True)

        newVal = self.AddConditions(instruction, dstVal, value)
        self.SetRegister(rname(dstOper), newVal)
        return self.IncPC(instruction)

    def DoRsb(self, instruction):
        
        opers = instruction.operands
        dstOper = opers[0]
        srcOper1 = opers[1]
        srcOper2 = opers[2]

        dstVal = self.GetOperandValue(dstOper)
        srcVal1 = self.GetOperandValue(srcOper1)
        srcVal2 = self.GetOperandValue(srcOper2)
        value = z3.simplify(srcVal2 - srcVal1)

        if instruction.update_flags:
            self.UpdateFlags(['N', 'Z', 'C', 'V'], dstVal, value, value, 
                self.bitwidth, False,False)

        newVal = self.AddConditions(instruction, dstVal, value)
        self.SetRegister(rname(dstOper), newVal)
        return self.IncPC(instruction)

    def DoLdm(self, instruction):

        if 'pop' in instruction.mnemonic:
            baseAddr = self.GetRegisterValue('sp')
            opers = instruction.operands
        else:
            baseAddr = self.GetOperandValue(instruction.operands[0])
            opers = instruction.operands[1:]

        for oper in opers:
            val = self.ReadMemoryBytes(baseAddr, self.ptrSize)
            self.SetRegister(rname(oper), val)
            baseAddr += self.ptrSize
        
        self.SetRegister('sp', baseAddr)
        return self.IncPC(instruction)

    def DoStm(self, instruction):

        if 'push' in instruction.mnemonic:
            baseAddr = self.GetRegisterValue('sp')
            opers = instruction.operands
            baseAddrReg = 'sp'
        else:
            baseAddr = self.GetOperandValue(instruction.operands[0])
            opers = instruction.operands[1:]
            baseAddrReg = rname(instruction.operands[0])

        for oper in opers:
            val = self.GetOperandValue(oper)
            self.SetMemory(baseAddr, self.bitwidth, val)
            baseAddr += self.ptrSize
        
        self.SetRegister(baseAddrReg, baseAddr)
        return self.IncPC(instruction)

    def DoBlx(self, instruction):
        operand = instruction.operands[0]

        target = self.GetOperandValue(operand)
        modeFlag = z3.Extract(0, 0, target)
        
        self.currentMode = z3.If(modeFlag == 1, self.THUMB_MODE, self.ARM_MODE)

        currentAddr = self.GetRegisterValue('PC')
        self.SetRegister('LR', z3.simplify(currentAddr + self.instructionSize))
        self.SetRegister('PC', z3.simplify(target))

    def DoBl(self, instruction):
        operand = instruction.operands[0]

        target = self.GetOperandValue(operand)
        currentAddr = self.GetRegisterValue('PC')
        self.SetRegister('LR', z3.simplify(currentAddr + self.instructionSize))
        self.SetRegister('PC', z3.simplify(target))

    def DoB(self, instruction):
        operand = instruction.operands[0]

        target = self.GetOperandValue(operand)
        self.SetRegister('PC', z3.simplify(target))

