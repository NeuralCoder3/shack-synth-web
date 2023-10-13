#! /usr/bin/env python3

from z3 import *
from synth import *

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


class Sort:
    def __init__(self, regs, swap=1):
        self.regs = regs
        self.swap = swap
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
        swaps = []
        # compare
        for a in range(self.regs):
            for b in range(self.regs):
                if a < b:
                    # compare two registers, write the result in the flags
                    cmp = Func(f'cmp_{a}_{b}', \
                        Store(
                            Store(x, self.regs+self.swap, If(Select(x, a)<Select(x, b), 1, 0)),
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
                                Store(x, a, x[b]),
                                x
                            )
                        )
                    )
                    
                    cmovgs.append(
                        Func(f'cmovg_{a}_{b}',
                            If(Select(x, self.regs+self.swap+1) == 1,
                                Store(x, b, x[a]),
                                x
                            )
                        )
                    )

        
        self.cmps = cmps
        self.swaps = swaps
        self.cmovls = cmovls
        self.cmovgs = cmovgs
        self.Id = Func('Id', x)

class SortBench(TestBase):
    def __init__(self, width, args):
        super().__init__(**vars(args))
        self.size = width
        self.sort    = Sort(self.size)
        self.ops = []
        self.ops += self.sort.swaps
        # self.ops += [self.sort.Id]

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
        oob = self.size+1+2
        sorted.append(Select(y, oob) == Select(x, oob)) # bind y to be a mutation of x to avoid constants
        # sorted.append(Distinct([Select(y, i) for i in range(self.size)]))
        # sorted.append(Select(y, 0) <= Select(y, 1))
        
        pred = [] # x[0] ... x[width-1] are a permutation of 1..width-1
        pred.append(Distinct([Select(x, i) for i in range(self.size)])) # all n numbers are different
        pred.append(And([And(1 <= Select(x, i), Select(x, i) <= self.size) for i in range(self.size)])) # numbers are in range 1..n
        pred.append(And([Select(x, i) == 0 for i in range(self.size, self.size+1+2)])) # swap and flag registers are zero
        
        spec = Spec('sort',
                    # [ Implies(And(pred), And(sorted)) ],
                    [ And(sorted) ], # goal/postcondition
                    [ y ], # output
                    [ x ], # input
                    [ And(pred) ] # precondition
        )
        return self.do_synth('sort', spec, self.ops, desc='sort using swap', max_const=0) # Note: max const does not prevent a return constant

if __name__ == '__main__':
    args = parse_standard_args()
    t = SortBench(3, args)
    t.run()
