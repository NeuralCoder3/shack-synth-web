#! /usr/bin/env python3

import random
import itertools

from itertools import combinations as comb
from itertools import permutations as perm

from z3 import *

def get_var(ty, args):
    if args in get_var.vars:
        v = get_var.vars[args]
    elif ty:
        v = ty('_'.join(map(str, args)))
        get_var.vars[args] = v
    else:
        assert False
    return v
get_var.vars = {}

class Op:
    def __init__(self, name: str, opnd_tys: list, res_ty, phi):
        self.name     = name
        self.phi      = phi 
        self.opnd_tys = opnd_tys
        self.res_ty   = res_ty
        self.arity    = len(self.opnd_tys)
        self.comm     = None

    def __str__(self):
        return self.name

    def is_commutative(self):
        if self.comm is None:
            ins = [ get_var(ty, (self.name, 'in', 'comm', i)) for i, ty in enumerate(self.opnd_tys) ]
            fs = [ self.phi(a) != self.phi(b) for a, b in comb(perm(ins), 2) ] 
            s = Solver()
            s.add(Or(fs))
            self.comm = s.check() == unsat
        return self.comm

class Prg:
    def __init__(self, input_names, insns, outputs):
        """Creates a program.

        Attributes:
        input_names: list of names of the inputs
        insns: List of instructions.
            This is a list of pairs where each pair consists
            of an Op and a list of integers where each integer
            indicates the variable number of the operand.
        outputs: List of variable numbers that constitute the output.
        """
        self.input_names = input_names
        self.insns = insns
        self.outputs = outputs

    def var_name(self, i):
        return self.input_names[i] if i < len(self.input_names) else f'x{i}'

    def __len__(self):
        return len(self.insns)

    def __str__(self):
        n_inputs = len(self.input_names)
        jv = lambda args: ', '.join(map(lambda n: self.var_name(n), args))
        res = '\n'.join(f'x{i + n_inputs} = {op.name}({jv(args)})' for i, (op, args) in enumerate(self.insns))
        # res += '; ' if len(res) > 0 else ''
        # for i, (op, args) in enumerate(self.insns):
            #res +=
        return res + f'\nreturn({jv(self.outputs)})'

class Synth:
    def __init__(self, n_insns, input_names, funcs: list[Op], ops: list[Op]):
        self.input_names = input_names
        self.n_inputs = len(input_names)
        self.n_insns = n_insns
        self.funcs = funcs
        self.ops = ops

        # get types of input operands. 
        # all functions need to agree on this.
        assert len(funcs) > 0
        self.in_tys = funcs[0].opnd_tys
        for s in funcs[1:]:
            assert self.in_tys == s.opnd_tys
        self.length = len(self.in_tys) + n_insns + 1

        max_arity = max(map(lambda op: op.arity, ops))
        self.arities = [ 0 ] * self.n_inputs + [ max_arity ] * n_insns + [ len(funcs) ]
        self.out_tys = [ op.res_ty for op in funcs ]

    def var_insn_op(self, insn):
        return get_var(Int, ('insn', insn, 'op'))

    def var_insn_opnds(self, insn):
        for opnd in range(self.arities[insn]):
            yield get_var(Int, ('insn', insn, 'opnd', opnd))

    def var_insn_opnds_val(self, insn, tys, instance):
        for opnd, ty in enumerate(tys):
            yield get_var(ty, ('insn', insn, 'opnd', opnd, ty.__name__, instance))

    def var_insn_res(self, insn, ty, instance):
        return get_var(ty, ('insn', insn, 'res', ty.__name__, instance))

    def var_input_res(self, insn, instance):
        return self.var_insn_res(insn, self.in_tys[insn], instance)

    def add_constr_wfp(self, solver: Solver):
        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for insn in range(self.length):
            for v in self.var_insn_opnds(insn):
                solver.add(0 <= v)
                solver.add(v < insn)

        # add constraints that says that each produced value is used
        # for prod in range(self.n_insns, self.length):
        #     opnds = [ prod == v for cons in range(prod + 1, self.length) for v in self.var_insn_opnds(cons) ]
        #     if len(opnds) > 1:
        #         solver.add(Or(opnds))

        # for all instructions that get an op
        for insn in range(self.n_inputs, self.length - 1):
            o = self.var_insn_op(insn)
            # constrain the op variable to the number of ops
            solver.add(0 <= o)
            solver.add(o < len(self.ops))
            # if operator is commutative, the operands can be linearly ordered
            # these constraints don't restrict the solution space but might
            # shrink the search space
            op_var = self.var_insn_op(insn)
            for op_id, op in enumerate(self.ops):
                opnds = list(self.var_insn_opnds(insn))
                if op.is_commutative():
                    c = [ l < u for l, u in zip(opnds[:op.arity - 1], opnds[1:]) ]
                    solver.add(Implies(op_var == op_id, And(c)))

    def out_insn(self):
        return self.length - 1

    def is_op_insn(self, insn):
        return insn >= self.n_inputs and insn < self.length - 1

    def add_constr_conn(self, solver, insn, tys, instance):
        for l, v in zip(self.var_insn_opnds(insn), \
                        self.var_insn_opnds_val(insn, tys, instance)):
            # for other each instruction preceding it
            for other in range(insn):
                # print(v.sort(), l.sort())
                r = self.var_insn_res(other, Bool, instance)
                solver.add(Implies(l == other, v == r))

    def add_constr_instance(self, solver, instance):
        # for all instructions that get an op
        for insn in range(self.n_inputs, self.length - 1):
            # add constraints to select the proper operation
            op_var = self.var_insn_op(insn)
            for op_id, op in enumerate(self.ops):
                res = self.var_insn_res(insn, op.res_ty, instance)
                opnds = list(self.var_insn_opnds_val(insn, op.opnd_tys, instance))
                eq = res == op.phi(opnds)
                solver.add(Implies(op_var == op_id, eq))
            # connect values of operands to values of corresponding results
            for op in self.ops:
                self.add_constr_conn(solver, insn, op.opnd_tys, instance)    

        # add connection constraints for output instruction
        self.add_constr_conn(solver, self.out_insn(), self.out_tys, instance)

    def add_constr_input_values(self, solver, instance, counter_example):
        # add input value constraints
        assert len(counter_example) == self.n_inputs
        for inp, val in zip(range(self.n_inputs), counter_example):
            if not val is None:
                res = self.var_input_res(inp, instance)
                solver.add(res == val)

    def add_constr_sol_for_verif(self, solver, model):
        for insn in range(self.length):
            if self.is_op_insn(insn):
                v = self.var_insn_op(insn)
                solver.add(v == model[v])
            for opnd in self.var_insn_opnds(insn):
                solver.add(opnd == model[opnd])

    def add_constr_spec(self, solver, instance, f=lambda x: x):
        # all result variables of the inputs
        input_vals = [ self.var_input_res(i, instance) \
                       for i in range(self.n_inputs) ]
        # the operand value variables of the output instruction
        out_opnds = self.var_insn_opnds_val(self.out_insn(), self.out_tys, instance)
        # constraints that express the specifications
        spec = [o == s.phi(input_vals) for o, s in zip(out_opnds, self.funcs)]
        solver.add(f(And(spec)))

    def sample(self):
        s = Solver()
        ins = [ get_var(self.in_tys[i], ('sample', 'in', i)) for i in range(self.n_inputs) ]
        for i, func in enumerate(self.funcs):
            res = get_var(func.res_ty, ('sample', 'out', i))
            s.add(res == func.phi(ins))
        s.check()
        m = s.model()
        return [ m[v] for v in ins ]

    def __call__(self, debug=0):
        def d(*args):
            nonlocal debug
            if debug > 0:
                print(*args)

        def dd(*args):
            nonlocal debug
            if debug > 1:
                print(*args)

        def ddd(*args):
            nonlocal debug
            if debug > 2:
                print(*args)

        # setup the synthesis constraint
        synth = Solver()
        self.add_constr_wfp(synth)

        # setup the verification constraint
        verif = Solver()
        self.add_constr_instance(verif, 'verif')
        self.add_constr_spec(verif, 'verif', Not)

        # sample the specification once for an initial set of input samples
        counter_example = self.sample()

        d('size', self.n_insns)
        i = 0
        while True:
            d('counter example', i, counter_example)

            self.add_constr_instance(synth, i)
            self.add_constr_input_values(synth, i, counter_example)
            self.add_constr_spec(synth, i)

            ddd('synth', i, synth)

            if synth.check() == sat:
                # if sat, we found location variables
                m = synth.model()
                dd('model: ', m)
                # push a new verification solver state
                verif.push()
                # add constraints that set the location variables
                # in the verification constraint
                self.add_constr_sol_for_verif(verif, m)
                ddd('verif', i, verif)

                if verif.check() == sat:
                    # there is a counterexample, reiterate
                    m = verif.model()
                    var = lambda inp : m[self.var_input_res(inp, 'verif')]
                    counter_example = [ var(inp) for inp in range(self.n_inputs) ]
                    verif.pop()
                    i += 1
                else:
                    # we found no counterexample, the program is therefore correct
                    d('no counter example found')
                    insns = []
                    for insn in range(self.n_inputs, self.length - 1):
                        op = self.ops[m[self.var_insn_op(insn)].as_long()]
                        opnds = [ m[v].as_long() for v in self.var_insn_opnds(insn) ][:op.arity]
                        insns += [ (op, opnds) ]
                    out_idx = self.length - 1
                    outputs = [ m[res].as_long() for res in self.var_insn_opnds(out_idx) ]
                    return Prg(self.input_names, insns, outputs)
            else:
                d('synthesis failed')
                return None

def synth(length, input_names, specs, ops, debug=False):
    """Synthesize a program that implements a given specification.

    Args:
        length: Length of the program.
        input_names (list(str)): A list of names of the input variables
        specs (list(Op)): List of specifications of functions to synthesize
        ops (list(Op)): List of available operators that can be used for instructions.

    Returns:
        A program (Prg) if synthesis was successful or None otherwise.
    """
    return Synth(length, input_names, specs, ops)(debug)

def synth_smallest(max_length, input_names, specs, ops, debug=False):
    """Synthesize the smallest program that implements a given specification.

    Use like synth except for max_length which gives an upper bound on
    the program length. Internally, this function calls synth for lengths
    from 1 to max_length + 1 and returns the first (smallest) program found.
    """
    for sz in range(0, max_length + 1):
        if prg := synth(sz, input_names, specs, ops, debug):
            return prg
    return None

Bool1 = [ Bool ]
Bool2 = [ Bool ] * 2
Bool3 = [ Bool ] * 3
Bool4 = [ Bool ] * 4

true0  = Op('true0',  []   , Bool, lambda ins: True)
false0 = Op('false0', []   , Bool, lambda ins: False)
id1    = Op('id1',    Bool1, Bool, lambda ins: ins[0])

not1  = Op('not',     Bool2, Bool, lambda ins: Not(ins[0]))         #7404
nand2 = Op('nand2',   Bool2, Bool, lambda ins: Not(And(ins)))       #7400
nor2  = Op('nor2',    Bool2, Bool, lambda ins: Not(Or(ins)))        #7402
and2  = Op('and2',    Bool2, Bool, And)                             #7408
or2   = Op('or2',     Bool2, Bool, Or)                              #7432
xor2  = Op('xor2',    Bool2, Bool, lambda ins: Xor(ins[0], ins[1])) #7486
        
nand3 = Op('nand3',   Bool3, Bool, lambda ins: Not(And(ins)))       #7410
nor3  = Op('nor3',    Bool3, Bool, lambda ins: Not(Or(ins)))        #7427
and3  = Op('and3',    Bool3, Bool, And)                             #7411
        
nand4 = Op('nand4',   Bool4, Bool, lambda ins: Not(And(ins)))       #7420
and4  = Op('and4',    Bool4, Bool, And)                             #7421
nor4  = Op('nor4',    Bool4, Bool, lambda ins: Not(Or(ins)))        #7429
        
mux2  = Op('mux2',    Bool2, Bool, lambda i: Or(And(i[0], i[1]), And(Not(i[0]), i[2])))
eq2   = Op('eq2',     Bool2, Bool, lambda i: i[0] == i[1])

def create_random_formula(inputs, size, ops, seed=0x5aab199e):
    random.seed(a=seed, version=2)
    assert size > 0
    def create(size):
        nonlocal inputs, ops, seed
        assert size > 0
        if size == 1:
            return random.choice(inputs)
        elif size == 2:
            op = random.choice([op for op, n in ops if n == 1])
            return op(create(1))
        else:
            size -= 1
            op, arity = random.choice(ops)
            assert arity <= 2
            if arity == 1:
                return op(create(size))
            else:
                assert arity == 2
                szl = random.choice(range(size - 1)) + 1
                szr = size - szl
                return op(create(szl), create(szr))
    return create(size)

def create_random_dnf(inputs, seed=0x5aab199e):
    # sample function results
    random.seed(a=seed, version=2)
    clauses = []
    for vals in itertools.product(*[range(2)] * len(inputs)):
        if random.choice(range(2)):
            clauses += [ And([ inp if pos else Not(inp) for inp, pos in zip(inputs, vals) ]) ]
    return Or(clauses)

def random_test(n_vars, size, create_formula, debug=0):
    params = [ get_var(Bool, ('var', i)) for i in range(n_vars) ]
    ops  = [ and2, or2, xor2, not1 ]
    spec = Op('rand', [ Bool ] * n_vars, Bool, create_formula)
    print(create_formula(params))
    prg  = synth_smallest(size, [ f'v{i}' for i in range(n_vars)], [spec], ops, debug)
    print(prg)

def test_rand(size=40, n_vars=10, debug=0):
    rops = [ (And, 2), (Or, 2), (Xor, 2), (Not, 1) ]
    f    = lambda x: create_random_formula(x, size, rops)
    random_test(n_vars, size, f, debug)

def test_rand_dnf(size=40, n_vars=10, debug=0):
    f = lambda x: create_random_dnf(x)
    random_test(n_vars, size, f, debug)

def test_and(debug=0):
    spec = Op('and', Bool2, Bool, And)
    print('and:')
    prg = synth_smallest(1, [ 'a', 'b'], [spec], [spec], debug)
    print(prg)

def test_xor(debug=0):
    spec = Op('xor2', Bool2, Bool, lambda i: Xor(i[0], i[1]))
    ops  = [ and2, nand2, or2, nor2 ]
    print('xor:')
    prg = synth_smallest(10, [ 'x', 'y' ], [ spec ], ops, debug)
    print(prg)

def test_mux(debug=0):
    spec = Op('mux2', Bool3, Bool, lambda i: Or(And(i[0], i[1]), And(Not(i[0]), i[2])))
    ops  = [ and2, xor2 ]
    print('mux:')
    prg = synth_smallest(3, [ 's', 'x', 'y' ], [ spec ], ops, debug)
    print(prg)

def test_zero(debug=0):
    spec = Op('zero', [ Bool ] * 8, Bool, lambda i: Not(Or(i)))
    ops  = [ and2, nand2, or2, nor2, nand3, nor3, nand4, nor4 ]
    print('one byte all zero test:')
    prg = synth_smallest(10, [ f'x{i}' for i in range(8) ], [ spec ], ops, debug)
    print(prg)

def test_add(debug=0):
    cy  = Op('cy',  Bool3, Bool, lambda i: Or(And(i[0], i[1]), And(i[1], i[2]), And(i[0], i[2])))
    add = Op('add', Bool3, Bool, lambda i: Xor(i[0], Xor(i[1], i[2])))
    ops = [ nand2, nor2, and2, or2, xor2 ]
    print('1-bit full adder:')
    prg = synth_smallest(10, [ 'x', 'y', 'c' ], [ add, cy ], ops, debug)
    print(prg)

def test_identity(debug=0):
    spec = Op('magic', Bool, 1, lambda ins: And(Or(ins[0])))
    ops = [ nand2, nor2, and2, or2, xor2, id1]
    print('Identity: ')
    prg = synth_smallest(10, Bool, [ 'x' ], [ spec ], ops, debug)
    print(prg)

def test_constant(debug=0):
    spec = Op('magic', Bool, 3, lambda ins: Or(Or(ins[0], ins[1], ins[2]), Not(ins[0])))
    ops = [ true0, false0, nand2, nor2, and2, or2, xor2, id1]
    print('Constant True: ')
    prg = synth_smallest(10, Bool, [ 'x', 'y', 'z' ], [ spec ], ops, debug)
    print(prg)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(prog="synth")
    parser.add_argument('-d', '--debug', type=int, default=0)
    args = parser.parse_args()

    test_rand_dnf(40, 4, args.debug)
    test_rand(50, 5, args.debug)
    test_and(args.debug)
    test_mux(args.debug)
    test_xor(args.debug)
    test_zero(args.debug)
    test_add(args.debug)
    test_identity(args.debug)
    test_constant(args.debug)