from graph import UndirectedAdjList
from ast import *
from x86_ast import *
from utils import *
import copy
import compiler_var

Binding = tuple[Name, expr]
Temporaries = list[Binding]

get_fresh_tmp = lambda: generate_name('tmp')

caller_saved_registers: set[location] = set(
    [
        Reg('rax'),
        Reg('rcx'),
        Reg('rdx'),
        Reg('rsi'),
        Reg('rdi'),
        Reg('r8'),
        Reg('r9'),
        Reg('r10'),
        Reg('r11'),
    ]
)

callee_saved_registers: set[location] = set(
    [Reg('rbx'), Reg('r12'), Reg('r13'), Reg('r14'), Reg('r15')]
)

registers_for_coloring = [
    Reg("rcx"),
    Reg("rdx"),
    #Reg("rsi"), the rsi register is used by the rootstack and cannot be used to colour
    Reg("r8"),
    Reg("r9"),
    Reg("r10"),
    Reg("rbx"),
    Reg("r12"),
    Reg("r13"),
    Reg("r14")
]


def get_loc_from_arg(a: arg) -> set[location]:
    match a:
        case Reg(_):
            return set([a])
        case Variable(_):
            return set([a])
        case ByteReg(_):
            return set([a])
        case _:
            return set([])


class Compiler(compiler_var.Compiler):
    def __init__(self):
        super().__init__()
        self.used_callees = set()
        self.spill = 0

    ###########################################################################
    # Uncover Live
    ###########################################################################

    def read_vars(self, i: instr) -> set[location]:
        match i:
            case Instr('movq', [src, target]):
                return get_loc_from_arg(src)
            case Instr('addq', [src, target]) | Instr('subq', [src, target]):
                return get_loc_from_arg(src) | get_loc_from_arg(target)
            case Instr('negq', [var]):
                return get_loc_from_arg(var)
            case Callq(func, _):
                if func == 'print_int':
                    return set([Reg('rdi')])
                else:
                    return set([])
            case _:
                raise Exception(f'Unknown instruction: {i}')

    def write_vars(self, i: instr) -> set[location]:
        match i:
            case Instr('movq', [src, target]) | Instr('addq', [src, target]) | Instr('subq', [src, target]):
                return get_loc_from_arg(target)
            case Instr('negq', [target]):
                return get_loc_from_arg(target)
            case Callq(func, _):
                if func == 'read_int':
                    return set([Reg('rax')])
                else:
                    return set([])
            case _:
                raise Exception(f'Unknown instruction: {i}')

    def uncover_live(self, p: X86Program) -> dict[instr, set[location]]:

        # VORGEGEBEN

        result = {}

        l_after = set()
        l_before = set()

        for i in reversed(p.body):
            result[i] = l_after

            l_before = (l_after - self.write_vars(i)) | self.read_vars(i)
            l_after = l_before

        return result

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(
            self, p: X86Program, live_after: dict[instr, set[location]]
    ) -> UndirectedAdjList:

        ### Hilfe zur Benutzung der Graph-Klasse: ###
        # hier wird zunächst ein Graph erzeugt, welcher alle locations als Knoten beinhaltet
        # dies kann so beibehalten werden, lässt sich aber bei einer entsprechenden Lösung auch vereinfachen 

        # label wird nur für die Anzeige der Graphen benötigt, da diese immer strings als Knotenlabel erwartet
        label = lambda v: v.id if isinstance(v, Reg) else str(v)
        graph = UndirectedAdjList(vertex_label=label)

        for (instruction, vs) in live_after.items():
            for v in vs:
                graph.add_vertex(v)
            match instruction:
                case Instr('movq', [s, d]):
                    for v in live_after[instruction]:
                        if v != s and v != d and not graph.has_edge(d, v):
                            graph.add_edge(d, v)
                case Callq(_, _):
                    for v in live_after[instruction]:
                        for reg in caller_saved_registers:
                            if v != reg and not graph.has_edge(v, reg):
                                graph.add_edge(v, reg)
                case _:
                    for d in live_after[instruction]:
                        for v in self.write_vars(instruction):
                            if v != d and not graph.has_edge(v, d):
                                graph.add_edge(v, d)

        return graph

    ############################################################################
    # Allocate Registers
    ############################################################################

    def color_vertex(self, graph: UndirectedAdjList, coloring: dict[location, arg], vertex: location, colors: set[location]) -> location:
        for color in colors:
            neighbors = graph.adjacent(vertex)
            if all(coloring.get(n, None) != color for n in neighbors):
                if color in callee_saved_registers:
                    self.used_callees.add(color)
                return color
        return None

    def color_graph(
            self, graph: UndirectedAdjList, colors: set[location]
    ) -> dict[location, arg]:
        
        coloring: dict[location, arg] = {}
        
        for v in graph.vertices():
            if isinstance(v, Reg):
                coloring[v] = v

        if len(coloring) < len(graph.vertices()):
            vertex = None
            for v in graph.vertices():
                if v not in coloring and len(graph.adjacent(v)) < len(colors):
                    vertex = v
                    break

            if vertex is None:
                possibly_spilled = max(     # choose vertex with most neighbors
                    (v for v in graph.vertices() if v not in coloring),
                    key=lambda v: len(graph.adjacent(v))
                )

                rm_graph = copy.deepcopy(graph)
                rm_graph.remove_vertex(possibly_spilled)

                coloring = self.color_graph(rm_graph, colors)

                # try coloring possibly_spilled
                color = self.color_vertex(graph, coloring, possibly_spilled, colors)
                if color:
                    coloring[possibly_spilled] = color
                else:
                    self.spill += 1

            else:
                rm_graph = copy.deepcopy(graph)
                rm_graph.remove_vertex(vertex)

                coloring = self.color_graph(rm_graph, colors)            

                coloring[vertex] = self.color_vertex(graph, coloring, vertex, colors)

        return coloring

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes(self, p: X86Program) -> X86Program:
        live_after = self.uncover_live(p)
        graph = self.build_interference(p, live_after)

        home = self.color_graph(graph, registers_for_coloring)

        new_body = self.assign_homes_instrs(p.body, home)
        return X86Program(new_body)

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        conclusion = []
        prelude = [
            Instr('pushq', [Reg('rbp')]),
            Instr('movq', [Reg('rsp'), Reg('rbp')])
        ]

        for i in self.used_callees:
            prelude.append(Instr('pushq', [i]))
            conclusion.insert(0, Instr('popq', [i]))
            self.alloc()

        # stack dividable by 16?
        if self.stack_offset % 16 != 0:
            self.alloc()

        prelude.append((Instr('subq', [Immediate(self.stack_offset), Reg('rsp')])))
        conclusion.insert(0, Instr('addq', [Immediate(self.stack_offset), Reg('rsp')]))
        
        conclusion.extend([
            Instr('popq', [Reg('rbp')]),
            Instr('retq', [])
        ])
        instructions: list[Instr] = []
        for instr in p.body:
            instructions.append(instr)
        return X86Program(prelude + instructions + conclusion)

    ##################################################
    # Compiler
    ##################################################

    def compile(self, s: str, logging=False) -> X86Program:
        compiler_passes = {
            'remove complex operands': self.remove_complex_operands,
            'select instructions': self.select_instructions,
            'assign homes': self.assign_homes,
            'patch instructions': self.patch_instructions,
            'prelude & conclusion': self.prelude_and_conclusion,
        }

        current_program = parse(s)

        if logging == True:
            print()
            print('==================================================')
            print(' Input program')
            print('==================================================')
            print()
            print(s)

        for pass_name, pass_fn in compiler_passes.items():
            current_program = pass_fn(current_program)

            if logging == True:
                print()
                print('==================================================')
                print(f' Output of pass: {pass_name}')
                print('==================================================')
                print()
                print(current_program)

        return current_program


##################################################
# Execute
##################################################

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            try:
                program = f.read()
                compiler = Compiler()
                x86_program = compiler.compile(program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(str(x86_program))

            except:
                print(
                    'Error during compilation! **************************************************'
                )
                import traceback

                traceback.print_exception(*sys.exc_info())
