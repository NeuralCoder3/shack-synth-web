#! /usr/bin/env python3

from z3 import *
from synth import *
from synth import _collect_vars

"""
We handle imperative programs with mutation
by mutating a world state (resulting in a linear program).
The internal constraints model this linearity by forbidding
dead code and having exactly one input and output per node.

We model our state as an integer array with
n registers (some permutation of 1..n)
m swap registers (zero and can be used in instructions)
2 flag registers (less, greater)

Our instructions are:
swap a b  -- swap if value in first register is greater 
cmp a b   -- compare two registers, write the result in the flags
cmovl a b -- move b to a if less flag is set
cmovg a b -- move b to a if greater flag is set
mov a b   -- move b to a
"""

# best to call `python test_sort.py -d 1 -m 12`
# swap                 => works
# swap+cmps+cmovg      => 4s
# swap+cmps+cmovlg     => 9s
# swap+cmps+cmovlg+mov => 7s
# cmps+cmovg           => 1104s @12
# cmps+cmovg           => 2443s (found 11)
# cmps+cmovlg          => 5323s @11
# cmps+cmovlg          => 8098s @12
# cmps+cmovlg+mov      => @11

class Sort:
    def __init__(self, regs, swap=1):
        self.regs = regs
        self.swap = swap
        self.total_regs = regs+swap
        # TODO: limit bitwidth, length
        self.ty    = z3.ArraySort(IntSort(),IntSort())
        # r1, r2, r3, s1, fl, fg
        # register 1..width
        # swap 1..swap
        # flag less, flag greater
        
        x = Array('x', IntSort(), IntSort())
        
        cmps = []
        cmovls = []
        cmovgs = []
        movs = []
        swaps = []
        # compare
        for a in range(self.total_regs):
            for b in range(self.total_regs):
                if a < b:
                    cmp = Func(f'cmp_{a}_{b}', \
                        Store(
                            Store(x, 
                            self.regs+self.swap  , If(Select(x, a)<Select(x, b), 1, 0)),
                            self.regs+self.swap+1, If(Select(x, a)>Select(x, b), 1, 0)
                        )
                    )
                    cmps.append(cmp)

                    swaps.append(
                        Func(f'swap_{a}_{b}', 
                            If(Select(x, a) > Select(x, b),
                                Store(Store(x, a, Select(x, b)), b, Select(x, a)),
                                x
                            )
                        )
                    )
                
                if a != b:
                    cmovls.append(
                        Func(f'cmovl_{a}_{b}',
                            If(Select(x, self.regs+self.swap) == 1,
                                Store(x, a, Select(x, b)),
                                x
                            )
                        )
                    )
                    
                    cmovgs.append(
                        Func(f'cmovg_{a}_{b}',
                            If(Select(x, self.regs+self.swap+1) == 1,
                                Store(x, a, Select(x, b)),
                                x
                            )
                        )
                    )
                    
                    movs.append(
                        Func(f'mov_{a}_{b}',
                            Store(x, a, Select(x, b)),
                        )
                    )

        
        self.cmps = cmps
        self.swaps = swaps
        self.cmovls = cmovls
        self.cmovgs = cmovgs
        self.movs = movs
        self.Id = Func('Id', x)
        
        self.cmds = self.cmps + self.swaps + self.cmovls + self.cmovgs + self.movs + [self.Id]
        for cmd in self.cmds:
            setattr(self, cmd.name, cmd)

class SortBench(TestBase):
    def __init__(self, width, swap, args):
        super().__init__(**vars(args))
        self.size = width
        self.swap = swap
        self.sort    = Sort(self.size, self.swap)
        self.ops = []
        self.ops += self.sort.cmps
        self.ops += self.sort.cmovgs
        self.ops += self.sort.cmovls
        self.ops += self.sort.movs
        # self.ops += self.sort.swaps

    def do_synth(self, name, spec, ops, desc='', **args):
        return super().do_synth(name, spec, ops, desc,
                                theory='ALL', **args)


    def test_sort(self):
        x = Array('x', IntSort(), IntSort())
        
        # either require as formula that y[0]<=y[1]<=y[2] (one could theoretically be zero -- need precise+precondition)
        # or restrict x stronger to be a permutation of 1..width-1 and require y[0]=1 ... y[width-1]=width-1
        y = Array('y', IntSort(), IntSort())
        sorted = []
        for i in range(self.size):
            sorted.append(Select(y, i) == i+1)
        
        # sorted.append(Select(y, self.size) == 0)
        oob = self.size+self.swap+2
        sorted.append(Select(y, oob) == Select(x, oob)) # bind y to be a mutation of x to avoid constants
        
        pred = [] # x[0] ... x[width-1] are a permutation of 1..width-1
        pred.append(Distinct([Select(x, i) for i in range(self.size)])) # all n numbers are different
        pred.append(And([And(1 <= Select(x, i), Select(x, i) <= self.size) for i in range(self.size)])) # numbers are in range 1..n
        pred.append(And([Select(x, i) == 0 for i in range(self.size, self.size+self.swap+2)])) # swap and flag registers are zero
        
        spec = Spec('sort',
                    # [ Implies(And(pred), And(sorted)) ],
                    [ And(sorted) ], # goal/postcondition
                    [ y ], # output
                    [ x ], # input
                    [ And(pred) ] # precondition
        )
        # Note: max const does not prevent a return constant
        return self.do_synth('sort', spec, self.ops, desc='sort using assembly', max_const=0, opt_no_dead_code=True) 
    
    
def validate():
    size = 3
    sort = Sort(size)
    s = Solver()
    
    x = Array('x', IntSort(), IntSort())
    z = Array('z', IntSort(), IntSort())
    s.add(Distinct([Select(x, i) for i in range(size)]))
    s.add(And([And(1 <= Select(x, i), Select(x, i) <= size) for i in range(size)]))
    s.add(And([Select(x, i) == 0 for i in range(size, size+1+2)]))
    
    def specialize(f, x):
        vars = _collect_vars(f)
        for v in vars:
            f = substitute(f, (v, x))
        return f
    
    # or use spec.instantiate(outs, inputs) with intermediate variables
    y = x
    # y = specialize(sort.swap_0_1.func, y)
    # y = specialize(sort.swap_1_2.func, y)
    # y = specialize(sort.swap_0_1.func, y)
    
    # swap a b = cmp a b; cmovg 3 a; cmovg a b; cmovg b 3
    # TODO: maps would make this nicer
    # 0 1
    y = specialize(sort.cmp_0_1.func, y)
    y = specialize(sort.cmovg_3_0.func, y)
    y = specialize(sort.cmovg_0_1.func, y)
    y = specialize(sort.cmovg_1_3.func, y)
    
    # 1 2
    y = specialize(sort.cmp_1_2.func, y)
    y = specialize(sort.cmovg_3_1.func, y)
    y = specialize(sort.cmovg_1_2.func, y)
    y = specialize(sort.cmovg_2_3.func, y)
    
    # 0 1
    y = specialize(sort.cmp_0_1.func, y)
    y = specialize(sort.cmovg_3_0.func, y)
    y = specialize(sort.cmovg_0_1.func, y)
    y = specialize(sort.cmovg_1_3.func, y)
    
    s.add(z == y)
    
    s.add(Not(And(
        Select(z, 0) == 1,
        Select(z, 1) == 2,
        Select(z, 2) == 3
    )))
    
    if s.check() == unsat:
        print("With the example, the result is guaranteed to be sorted.")
    else:
        m = s.model()
        for i in range(size):
            print(m.evaluate(Select(x, i)),"->", m.evaluate(Select(z, i)))

if __name__ == '__main__':
    args = parse_standard_args()
    t = SortBench(3, 1, args)
    validate()
    t.run()
