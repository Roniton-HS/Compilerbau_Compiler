# Convert from the x86 AST classes defined in utils.py into the parse
# tree format used by the interpreter.

from ast import Constant, Name

from lark import Tree
from utils import GlobalValue, label_name
from x86_ast import *
import x86_ast


def convert_int(value):
    return Tree("int_a", [value])
    # if value >= 0:
    #     return Tree("int_a", [value])
    # else:
    #     return Tree("neg_a", [Tree("int_a", [-value])])

def convert_arg(arg):
    match arg:
        case Reg(id):
            return Tree('reg_a', [id])
        case Variable(id):
            return Tree('var_a', [id])
        case Immediate(value):
            return convert_int(value)
        case Deref(reg, offset):
            return Tree('mem_a', [convert_int(offset), reg])
        case ByteReg(id):
            return Tree('reg_a', [id])
        case GlobalValue(id) | x86_ast.Global(id):
            return Tree('global_val_a', [id, 'rip'])
        case _:
            raise Exception('convert_arg: unhandled ' + repr(arg))

def convert_instr(instr):
    match instr:
        case Instr(instr, args):
            return Tree(instr, [convert_arg(arg) for arg in args])
        case Callq(func, args):
            return Tree('callq', [func])
        case IndirectCallq(func, args) | TailJump(func, args):
            if func.id.startswith('r'):
                return Tree('indirect_callq', [Tree('reg_a', [func.id])])
            else:
                return Tree('indirect_callq', [Tree('var_a', [func.id])])
        case Jump(label):
            return Tree('jmp', [label])
        case IndirectJump(reg):
            if reg.id.startswith('r'):
                return Tree('indirect_callq', [Tree('reg_a', [reg.id])])
            else:
                return Tree('indirect_callq', [Tree('var_a', [reg.id])])
        case JumpIf(cc, label):
            return Tree('j' + cc, [label])
        case _:
            raise Exception('error in convert_instr, unhandled ' + repr(instr))

def convert_program(p):
    if hasattr(p, 'body') and isinstance(p.body, list):
        main_instrs = [convert_instr(instr) for instr in p.body]
        main_block = Tree('block', [label_name('main')] + main_instrs)
        return Tree('prog', [main_block])
    elif hasattr(p, 'body') and isinstance(p.body, dict):
        blocks = []
        for (l, ss) in p.body.items():
            blocks.append(Tree('block',
                               [l] + [convert_instr(instr) for instr in ss]))
        return Tree('prog', blocks)
    elif hasattr(p, 'defs') and isinstance(p.defs, list):
        blocks = []
        for fdef in p.defs:
            for (l, ss) in fdef.body.items():
                blocks.append(Tree('block',
                                   [l] + [convert_instr(instr) for instr in ss]))
        return Tree('prog', blocks)


