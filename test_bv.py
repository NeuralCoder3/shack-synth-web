#! /usr/bin/env python3

from z3 import *
from synth import *

class BvBench(TestBase):
    def __init__(self, width, args):
        super().__init__(**vars(args))
        self.width = width
        self.bv    = Bv(width)
        self.ops = [
            self.bv.add_,
            self.bv.sub_,
            self.bv.and_,
            self.bv.or_,
            self.bv.xor_,
            self.bv.neg_,
            self.bv.not_,
            self.bv.ashr_,
            self.bv.lshr_,
            self.bv.shl_,
            self.bv.ult_,
            self.bv.uge_,
            self.bv.slt_,
            self.bv.sge_,
        ]
        self.one = BitVecVal(1, self.width)
        self.zero = BitVecVal(0, self.width)

    def do_synth(self, name, spec, ops, desc='', **args):
        return super().do_synth(name, spec, ops, desc,
                                theory='QF_FD', **args)

#     def nlz(self, x):
#         w = self.width
#         wm = (1 << w) - 1
#         m = -(2 ** (w - 1))
#         v = 2 ** (w - 1)
#         # for i in range(w):
#             # print(w - i, bin((m >> i) & wm), bin(v >> i))
#         res = BitVec('res', )
#         return And([
#             Implies(x & ((m >> i) & wm) == x & (v >> i), res == i) \
#             for i in range(self.width)
#         ])




    def test_p01(self):
        x = BitVec('x', self.width)
        spec = Func('p01', x & (x - 1))
        print(spec.is_deterministic())
        return self.do_synth('p01', spec, self.ops, desc='turn off rightmost bit')

    def test_p02(self):
        x = BitVec('x', self.width)
        o = BitVec('o', self.width)
        pt = Or([x == (1 << i) for i in range(self.width)])
        spec = Spec('p02', If(pt, o == self.zero, o > self.zero), [ o ], [ x ])
        print(spec.is_deterministic())
        return self.do_synth('p02', spec, self.ops, max_const=1, desc='unsigned test if power of 2')

    def test_p03(self):
        x = BitVec('x', self.width)
        spec = Func('p03', x & -x)
        return self.do_synth('p03', spec, self.ops, \
                             desc='isolate rightmost 1-bit')

    def test_p04(self):
        x = BitVec('x', self.width)
        spec = Func('p04', x ^ (x - 1))
        return self.do_synth('p04', spec, self.ops, \
                             desc='mask rightmost 1-bits')

    def test_p05(self):
        x = BitVec('x', self.width)
        spec = Func('p05', x | (x - 1))
        return self.do_synth('p05', spec, self.ops, \
                             desc='right-propagate rightmost 1-bit')

    def test_p06(self):
        x = BitVec('x', self.width)
        spec = Func('p06', x | (x + 1))
        return self.do_synth('p06', spec, self.ops, \
                             desc='turn on rightmost 0-bit')

    def test_p07(self):
        x = BitVec('x', self.width)
        spec = Func('p07', x & (~x + 1))
        return self.do_synth('p07', spec, self.ops, \
                             desc='isolate rightmost 0-bit')

    def test_p08(self):
        x = BitVec('x', self.width)
        spec = Func('p08', ~x & (x - 1))
        return self.do_synth('p08', spec, self.ops, \
                             desc='mask for trailing 0s')

    def test_p09(self):
        x = BitVec('x', self.width)
        spec = Func('p09', If(x < 0, -x, x))
        return self.do_synth('p09', spec, self.ops, desc='abs function')

    def test_p10(self):
        x = BitVec('x', self.width)
        spec = Func('p09', If(x < 0, -x, x))
        return self.do_synth('p09', spec, self.ops, desc='abs function')

    def test_p13(self):
        x = BitVec('x', self.width)
        m1 = BitVecVal(-1, self.width)
        p1 = BitVecVal(1, self.width)
        spec = Func('p13', If(x < 0, m1, If(x > 0, p1, 0)))
        return self.do_synth('p13', spec, self.ops, desc='sign function')

    def test_p14(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p14', Int2BV((BV2Int(x) + BV2Int(y)) / 2, self.width))
        return self.do_synth('p14', spec, self.ops, \
                             desc='floor of avg of two ints without overflow', max_const=1)

    def test_p15(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p15', Int2BV((BV2Int(x) + BV2Int(y) - 1) / 2 + 1, self.width))
        ops = [ self.bv.or_, self.bv.xor_, self.bv.sub_, self.bv.lshr_ ]
        return self.do_synth('p15', spec, ops, \
                             desc='ceil of avg of two ints without overflow', max_const=1)
    def test_p16(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p16', If(x >= y, x, y))
        ops = [ self.bv.or_, self.bv.xor_, self.bv.sub_, self.bv.lshr_ ]
        return self.do_synth('p16', spec, self.ops, \
                             desc='max of two ints', max_const=3)
    def test_p17(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p17', (((x - 1) | x) + 1) & x)
        return self.do_synth('p17', spec, self.ops, \
                             desc='turn off the rightmost string of 1-bits', \
                             max_const=2)

    def test_p18(self):
        one = BitVecVal(1, self.width)
        zero = BitVecVal(0, self.width)
        x = BitVec('x', self.width)
        spec = Func('p18', If(Or([x == (1 << i) for i in range(self.width)]), zero, one))
        return self.do_synth('p18', spec, self.ops, \
                             desc='check if power of 2')


    def test_p23(self):
        def create_spec(x):
            res = BitVecVal(0, 8)
            for i in range(self.width):
                res = ZeroExt(7, Extract(i, i, x)) + res
            return res

        x = BitVec('x', self.width)
        spec = Func('p23', create_spec(x))
        ops = [ self.bv.add_, self.bv.sub_, self.bv.and_, self.bv.lshr_ ]
        return self.do_synth('p23', spec, ops, \
                             desc='population count', \
                             max_const=7)

if __name__ == '__main__':
    args = parse_standard_args()
    t = BvBench(8, args)
    # t.nlz(0)
    t.run()