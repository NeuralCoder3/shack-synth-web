#! /usr/bin/env python3

from z3 import *
from synth import *


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
                    cmp = Func(f'cmp_{a}_{b}', \
                                # Store( \
                                #         Store(x, self.regs+self.swap, 1 if x[a]<x[b] else 0), \
                                #     self.regs+self.swap, 1 if x[a]>x[b] else 0) \
                        Store(
                            Store(x, self.regs+self.swap, If(x[a]<x[b], 1, 0)),
                            self.regs+self.swap+1, If(x[a]>x[b], 1, 0)
                        )
                    )
                    cmps.append(cmp)

                    # for i in range(2):
                    if True:
                        swaps.append(
                            # Func(f'swap_{a}_{b}_{i}', 
                            Func(f'swap_{a}_{b}', 
                                # Store(Store(x, a, x[b]), b, x[a]) if x[a] > x[b] else x
                                # If(x[a] > x[b],
                                #     Store(Store(x, a, x[b]), b, x[a]),
                                #     x
                                # )
                                If(Select(x, a) > Select(x, b),
                                    Store(Store(x, a, Select(x, b)), b, Select(x, a)),
                                    x
                                )
                            )
                        )
                
                if a != b:
                    cmovls.append(
                        Func(f'cmovl_{a}_{b}',
                            # Store(x, a, x[b]) if x[self.regs+self.swap] == 1 else x
                            If(x[self.regs+self.swap] == 1,
                                Store(x, a, x[b]),
                                x
                            )
                        )
                    )
                    
                    cmovgs.append(
                        Func(f'cmovg_{a}_{b}',
                            # Store(x, b, x[a]) if x[self.regs+self.swap+1] == 1 else x
                            If(x[self.regs+self.swap+1] == 1,
                                Store(x, b, x[a]),
                                x
                            )
                        )
                    )

        

        # x, y = BitVecs('x y', width)
        # shift_precond = And([y >= 0, y < width])
        # div_precond = y != 0
        # z = BitVecVal(0, width)
        # o = BitVecVal(1, width)

        # l = cmps + swaps + cmovls + cmovgs
        l = swaps
        
        self.cmps = cmps
        self.swaps = swaps
        self.cmovls = cmovls
        self.cmovgs = cmovgs
        self.Id = Func('Id', x)

        for op in l:
            setattr(self, f'{op.name}_', op)

class SortBench(TestBase):
    def __init__(self, width, args):
        super().__init__(**vars(args))
        self.size = width
        self.sort    = Sort(self.size)
        self.ops = self.sort.swaps
        self.ops += [self.sort.Id]
        # self.ops = [
        #     self.sort.swap_,
        # ]

    def do_synth(self, name, spec, ops, desc='', **args):
        return super().do_synth(name, spec, ops, desc,
                                # theory='QF_FD', **args)
                                theory='ALL', **args)

    # def nlz(self, x):
    #     w   = self.width
    #     res = BitVecVal(w, w)
    #     for i in range(w - 1):
    #         res = If(And([ Extract(i, i, x) == 1,
    #                  Extract(w - 1, i + 1, x) == BitVecVal(0, w - 1 - i) ]), w - 1 - i, res)
    #     return If(Extract(w - 1, w - 1, x) == 1, 0, res)

    def test_p01(self):
        # x = BitVec('x', self.width)
        x = Array('x', IntSort(), IntSort())
        # x = Store(x, self.size    , 0) # swap
        # x = Store(x, self.size+1  , 0) # flag less
        # x = Store(x, self.size+1+1, 0) # flag greater
        
        # either require as formula that y[0]<y[1]<y[2] (one could theoretically be zero)
        # or restrict x stronger to be a permutation of 1..width-1 and require y[0]=1 ... y[width-1]=width-1
        y = Array('y', IntSort(), IntSort())
        sorted = []
        for i in range(self.size):
            sorted.append(Select(y, i) == i+1)
        #     pass
        #     sorted.append(y[i] == i+1)
        
        
        # sorted.append(Select(y, self.size) == 0)
        oob = self.size+1+2
        sorted.append(Select(y, oob) == Select(x, oob))
        sorted.append(Distinct([Select(y, i) for i in range(self.size)]))
        # sorted.append(Select(y, 0) <= Select(y, 1))
        
        z = Store(Store(Store(x, 0, 1), 1, 2), 2, 3)
        z = Store(z, oob, Select(x, oob))
        # store arbitrary in swap, flags
        
        # for i in range(self.size):
        #     y = Store(y, i, i+1)
        pred = [] # x[0] ... x[width-1] are a permutation of 1..width-1
        # for i in range(self.size):
        #     ors = []
        #     for j in range(self.size):
        #         ors.append(x[i] == j+1)
        #     pred.append(Or(ors))
        
        # pred.append(distinct([x[i] for i in range(self.size)]))
        # pred.append(And([And(1 <= x[i], x[i] <= self.size) for i in range(self.size)]))
        # pred.append(x[self.size] == 0)
        # pred.append(x[self.size+1] == 0)
        # pred.append(x[self.size+1+1] == 0)
        
        pred.append(Distinct([Select(x, i) for i in range(self.size)]))
        pred.append(And([And(1 <= Select(x, i), Select(x, i) <= self.size) for i in range(self.size)]))
        pred.append(And([Select(x, i) == 0 for i in range(self.size, self.size+1+2)]))
        
        
        # pred.append(x[0] == 2)
        spec = Func('p01', y)
        # spec = Func('p01', y, precond=And(pred))
        print(self.ops)
        spec = Spec('sort',
                    # [ Implies(And(pred), And(sorted)) ],
                    [ And(sorted) ],
                    # [ y==x ],
                    # [ y==z ],
                    # [ Implies(And(pred),y==z) ],
                    # [ y==Store(x,0,52) ],
                    # [ y==Store(x,0,1) ],
                    # [ And(sorted) ],
                    [ y ],
                    [ x ],
                    [ And(pred) ]
        )
        return self.do_synth('sort', spec, self.ops, desc='sort using swap', max_const=0)

if __name__ == '__main__':
    args = parse_standard_args()
    t = SortBench(3, args)
    # t.nlz(0)
    t.run()
