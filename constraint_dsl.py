"""
constaint_dsl.py -- a domain specific language for specifying constraints

This generates a SQL query string for rop_finder sqlite3 dbs and the specifies 
constraints.

Author: Pete Markowsky <peterm@vodun.org>
Author: Lurene
"""
import types
import os

#third-party modules
import pyparsing
import sys
import z3

def CreateParser(stack):
    
    def pushFirst(s,l,t):
        stack.append(t[0]) 
    
    def pushMem(s, l, t):
        for tok in reversed(t):
            stack.append(tok)
        
    def pushConstraintOp(s,l,t):
        for token in t:
            if token in ('==', '!=', "ULT", "ULE", "AND", "OR", "UGE",
                         "UGT", ">", ">=", "<", "<="):
                stack.append(token)
                return
    
    integer  = pyparsing.Word("0123456789").setParseAction(lambda s,l,t: int(t[0]))
    hex_int  = pyparsing.Combine("0x" + pyparsing.Word("0123456789ABCDEFabcdef")).setParseAction(lambda s,l,t: int(t[0], 16))
    boolean  = pyparsing.oneOf(["True", "False"], caseless=True).setParseAction(lambda s,l,t: bool(t[0]))
    number   = (integer ^ hex_int)
    register = pyparsing.oneOf(["R0", "R1", "R2", "R3", "R4",
                                "R5", "R6", "R7", "R8", "R9", 
                                "R10", "R11", "R12", "R13", "R14", 
                                "R15", "SP", "LR", "PC"], caseless=True)
    reg_name = pyparsing.Combine(register + pyparsing.oneOf(["_start", "_end"]))
    mem_name = pyparsing.Combine("MEM" + pyparsing.oneOf(["_start", "_end"]))
    reg_number = (number ^ reg_name)
    operator = pyparsing.oneOf(["+", "-", "*", "/", "UDIV", "&", "^", "|"], caseless=True)
    constraint_ops = pyparsing.oneOf(['==', '!=', "ULT", "ULE", "AND", "OR", "UGE", "UGT", 
                                      ">", ">=", "<", "<="], caseless=True)
    #TODO make this an expr instead of a reg_number
    mem_expr = mem_name + number + reg_number
    atom = (boolean ^ reg_number).setParseAction(pushFirst) ^ mem_expr.setParseAction(pushMem)
    #expr = (atom.copy().setParseAction(pushFirst) + pyparsing.ZeroOrMore((operator + atom.copy().setParseAction(pushFirst)).setParseAction(pushFirst)))
    expr = (atom + pyparsing.ZeroOrMore((operator + atom).setParseAction(pushFirst)))
    constraint_grammar = (expr + constraint_ops + expr).setParseAction(pushConstraintOp)
    
    return constraint_grammar

def EvalStack(cpu_state, stack, invert=True):
    operations = {"AND": lambda x,y: z3.And(x, y),
                  "OR": lambda x,y: z3.Or(x,y),
                  "&": lambda x,y:  x & y,
                  "|": lambda x,y: x | y,
                  "^": lambda x,y: x ^ y,
                  "+": lambda x,y: x + y,
                  "-": lambda x,y: x - y,
                  "*": lambda x,y: x * y,
                  "/": lambda x,y: x / y,
                  "UDIV": lambda x,y: z3.UDIV(x,y),
                  "ULT": lambda x,y: z3.ULT(x,y),
                  "ULE": lambda x,y: z3.ULE(x,y),
                  "UGT": lambda x,y: z3.UGT(x,y),
                  "UGE": lambda x,y: z3.UGE(x,y),
                  ">": lambda x,y: x > y,
                  ">=": lambda x,y: x >= y,
                  "<": lambda x,y: x < y,
                  "<=": lambda x,y: x <= y}
    
    op = stack.pop()
    
    if type(op) == type(True):
        return op
    elif type(op) == types.IntType:
        return  z3.BitVecVal(op, cpu_state.bitwidth)
    
    if op in operations:
        op1 = EvalStack(cpu_state, stack)
        op2 = EvalStack(cpu_state, stack)
        return operations[op](op2, op1)
    elif op == '!=':
        if invert == True:
            op1 = EvalStack(cpu_state, stack)
            op2 = EvalStack(cpu_state, stack)
            return op1 == op2
        else:
            op1 = EvalStack(cpu_state, stack)
            op2 = EvalStack(cpu_state, stack)
            return op1 != op2
    elif op == '==':
        if invert == True:
            op1 = EvalStack(cpu_state, stack)
            op2 = EvalStack(cpu_state, stack)
            return op1 != op2
        else:
            op1 = EvalStack(cpu_state, stack)
            op2 = EvalStack(cpu_state, stack)
            return op1 == op2
    elif op == "MEM":
        size = EvalStack(cpu_state, stack)
        address = EvalStack(cpu_state, stack)
        return cpu_state.ReadMemory(address, size)
    # handle register types
    elif op.endswith('_start'):
        return cpu_state.GetRegisterInitialValue(op.replace('_start', ''))
    elif op.endswith('_end'):
        return cpu_state.GetRegister(op.replace('_end', ''))
    else:
        raise NotImplementedError("Invalid operation/operand in constraint dsl")
    

def ParseConstraint(cpu_state, constraint, initializer=False):
    """
    Parse a constraint returning the appropriate Z3 Predicate.
    
    Args:
      cpu_state: a CPUState instance
      stack: a stack of token strings.
      
    Returns:
      a tuple of 
        - a constraint that should return unsat (showing equivalence)
        - a constraint that should return sat (showing a set of assignments)
    """
    stack = []
    parser = CreateParser(stack)
    parser.parseString(constraint)
    sat_constraint = EvalStack(cpu_state, stack, invert=False)
    
    if initializer:
        unsat_constraint = sat_constraint
    else:
        unsat_constraint = sat_constraint == False
    
    return sat_constraint, unsat_constraint


def Main():
    class FakeReg(object):
        def __init__(self, name):
            self.size = 32
            self.name = name
            
        def GetCurrentValue(self):
            return z3.BitVec(self.name, self.size)
    
    class TestCpuState(object):
        def __init__(self):
            self.bitwidth = 32
            
        def GetRegister(self, name):
            return FakeReg(name).GetCurrentValue()
        
        def GetRegisterInitialValue(self, name):
            return FakeReg(name).GetCurrentValue()
        
    stack = []
    parser = CreateParser(stack)
    parser.parseString("r1_end + r2_end + r3_end == r1_start + 5")
    unsat_constraint = EvalStack(TestCpuState(), stack)
    stack = []
    parser = CreateParser(stack)
    parser.parseString("r1_end + r2_end + r3_end == r1_start + 5")
    sat_constraint = EvalStack(TestCpuState(), stack, invert=False)
    
    stack = []
    parser = CreateParser(stack)
    parser.parseString("r1_end == MEM_start 32 r1_start")
    sat_constraint = EvalStack(TestCpuState(), stack, invert=False)

    


if __name__ == '__main__':
    Main()
