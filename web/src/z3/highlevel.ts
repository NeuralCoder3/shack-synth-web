import * as z3 from 'z3-solver';

declare global {
    interface Window { 
        z3Promise: ReturnType<typeof z3.init>; 
        // ctx: z3.Context<"main">;
    }
}
window.z3Promise = z3.init();

type Name = "main";
let Z3M = await window.z3Promise;
let Context = Z3M.Context;
const Z3 = Z3M.Z3;
export const ctx = Context("main");

console.log("Z3 loaded");

// window.ctx = ctx;

/*
translation notes:
- types as z3.Bool, z3.AnyExpr
- handle contexts formally but use global context object instead of creating new ones
- handle context names in Context and AnyExpr as Name
- use ctx.Operation for operations like And, Or, etc.
- check is a promise -> async function and await result


References:

./node_modules/z3-solver/build/high-level/high-level.js
for how high-level uses low-level

./node_modules/z3-solver/build/high-level/types.d.ts
Type Interface for access

node_modules/z3-solver/build/low-level/wrapper.__GENERATED__.d.ts
node_modules/z3-solver/build/low-level/types.__GENERATED__.d.ts
low-level Z3 functions


Custom Extension to scopes:
automatic via patch-package
*/

/*
  Transpilation Bridge Layer:
*/

function combine<T>(arr: T[], len: number): T[][] {
    if (len === 0) {
        return [[]];
    }
    if (arr.length === 0) {
        return [];
    }
    const [head, ...tail] = arr;
    const withHead = combine(tail, len - 1).map(x => [head, ...x]);
    const withoutHead = combine(tail, len);
    return [...withHead, ...withoutHead];
}

function permute<T>(arr: T[]): T[][] {
    if (arr.length === 0) {
        return [[]];
    }
    return arr.flatMap((x, i) => {
        const rest = arr.slice(0, i).concat(arr.slice(i + 1));
        return permute(rest).map(x => [arr[i], ...x]);
    });
}

interface Showable {
    toString(): string;
}

function zip<T, U>(a: T[], b: U[]): [T, U][] {
    return a.map((e, i) => [e, b[i]]);
}

function timer(): () => number {
    const start = Date.now();
    return () => Date.now() - start;
}

function withTimer<T>(f: (elapsed: () => number) => T): T {
    let t = timer();
    let res = f(t);
    return res;
}


/*
  Medium Level Framework Transpilation Layer
*/
// TODO: test
function asLong(expr: z3.Expr): number {
    const sexpr = expr.sexpr();
    if (sexpr.startsWith("#b")) {
        return parseInt(sexpr.slice(2), 2);
    }
    if (sexpr.startsWith("#x")) {
        return parseInt(sexpr.slice(2), 16);
    }
    const num = parseInt(sexpr.replace("(", '').replace(")", "").replace(" ", ""));
    if (isNaN(num)) {
        throw new Error('Invalid number: ' + sexpr);
    }
    return num;
}

// TODO: test
function asBool(expr: z3.Expr): boolean {
    const sexpr = expr.sexpr();
    const b = sexpr.includes('true');
    return b;
}

function mapGetByStrKey<T, U>(map: Map<T, U>, key: T): U {
    const strKey = String(key);
    const entry = [...map.entries()].find(([k, v]) => String(k) === strKey);
    if (entry === undefined) {
        throw new Error('Key not found: ' + strKey + ' of type ' + key + ' (: ' + typeof key + ')');
    }
    return entry[1];
}




// Transpilation result

function _collect_vars<Name extends string = 'main'>(expr: z3.AnyExpr<Name>)
    : Set<z3.AnyExpr<Name>> {
    let vars = new Set<z3.AnyExpr<Name>>();
    function collect(expr: z3.AnyExpr<Name>) {
        if (expr.children().length === 0 && expr.decl().kind() === z3.Z3_decl_kind.Z3_OP_UNINTERPRETED) {
            vars.add(expr);
        } else {
            for (let child of expr.children()) {
                collect(child);
            }
        }
    }
    collect(expr);
    return vars;
}

export class Spec {
    name: string;
    ctx: z3.Context<Name>;
    arity: number;
    inputs: z3.Expr[];
    outputs: z3.Expr[];
    phis: z3.Bool[];
    preconds: z3.Bool[];
    vars: Set<z3.Expr>;

    constructor(
        name: string,
        phis: z3.Bool[],
        outputs: z3.Expr[],
        inputs: z3.Expr[],
        preconds: z3.Bool[] | null = null
    ) {
        // Input validations
        if (phis.length === 0) {
            throw new Error('Need at least one output');
        }
        if (phis.length !== outputs.length) {
            throw new Error('Number of outputs must match number of specifications');
        }
        if (preconds !== null && preconds.length !== outputs.length) {
            throw new Error('Number of preconditions must match');
        }

        this.ctx = phis[0].ctx; // Assuming ctx is an attribute of the first phi
        this.name = name;
        this.arity = inputs.length;
        this.inputs = inputs;
        this.outputs = outputs;
        this.phis = phis;
        this.preconds = preconds ? preconds : Array.from({ length: outputs.length }, () => this.ctx.Bool.val(true));
        // union(vars(phi) for phi in phis)
        this.vars = phis.reduce((acc, phi) => new Set([...acc, ..._collect_vars(phi)]), new Set<z3.Expr>());

        const allVars = [...outputs, ...inputs];
        if (new Set(allVars).size !== allVars.length) {
            throw new Error('Outputs and inputs must be unique');
        }
        // if (![...this.vars].every(varExpr => allVars.includes(varExpr))) {
        // if ([...this.vars].some(varExpr => !allVars.includes(varExpr))) {
        if ([...this.vars].some(varExpr => !allVars.map(String).includes(String(varExpr)))) {
            throw new Error(`Phi must use only out and in variables: ${[...this.vars]} vs ${allVars}`);
        }

        for (const [pre, phi, _out] of this.preconds.map((pre, i) => [pre, this.phis[i], this.outputs[i]])) {
            // if (![..._collect_vars(pre)].every(varExpr => this.inputs.includes(varExpr))) {
            if (![..._collect_vars(pre)].every(varExpr => this.inputs.map(String).includes(String(varExpr)))) {
                throw new Error('Precondition must use input variables only');
            }
            // if (![..._collect_vars(phi)].every(varExpr => allVars.includes(varExpr))) {
            if (![..._collect_vars(phi)].every(varExpr => allVars.map(String).includes(String(varExpr)))) {
                throw new Error(`i-th spec must use only i-th out and input variables ${phi}`);
            }
        }
    }

    toString(): string {
        return this.name;
    }

    translate<N extends string>(ctx: z3.Context<N>): Spec {
        // const ins = this.inputs.map(x => x.translate(ctx));
        // const outs = this.outputs.map(x => x.translate(ctx));
        // const pres = this.preconds.map(x => x.translate(ctx));
        // const phis = this.phis.map(x => x.translate(ctx));
        const ins = this.inputs.map(x => x);
        const outs = this.outputs.map(x => x);
        const pres = this.preconds.map(x => x);
        const phis = this.phis.map(x => x);
        return new Spec(this.name, phis, outs, ins, pres);
    }

    // Cached properties
    // could use https://stackoverflow.com/questions/74201358/whatss-the-best-way-to-cache-a-getter-without-decorators
    get outTypes(): z3.Sort[] {
        return this.outputs.map(v => v.sort);
    }

    get inTypes(): z3.Sort[] {
        return this.inputs.map(v => v.sort);
    }

    // get isTotal(): boolean {
    async isTotal(): Promise<boolean> {
        // const ctx = this.ctx;
        const solver = new ctx.Solver();
        const spec = this.translate(ctx);
        // solver.add(Or(spec.preconds.map(p => Not(p))));
        solver.add(ctx.Or(...spec.preconds.map(p => p.not())));
        return (await solver.check() === 'unsat');
    }

    // get isDeterministic(): boolean {
    async isDeterministic(): Promise<boolean> {
        // const ctx = new Context();
        const solver = new ctx.Solver();
        const spec = this.translate(ctx);
        const ins = spec.inTypes.map(ty => ctx.FreshConst(ty));
        const outs = spec.outTypes.map(ty => ctx.FreshConst(ty));
        const [, phis] = spec.instantiate(outs, ins);
        solver.add(ctx.And(...spec.preconds));
        for (const p of spec.phis) {
            solver.add(p);
        }
        for (const p of phis) {
            solver.add(p as z3.Bool);
        }
        solver.add(ctx.And(...spec.inputs.map((a, i) => a === ins[i])));
        solver.add(ctx.Or(...spec.outputs.map((a, i) => a !== outs[i])));
        return await solver.check() === 'unsat';
    }

    instantiate(outs: z3.Expr[], ins: z3.Expr[]): [z3.Bool[], z3.Bool[]] {
        const selfOuts = this.outputs;
        const selfIns = this.inputs;
        if (outs.length !== selfOuts.length || ins.length !== selfIns.length) {
            throw new Error('Invalid number of outputs or inputs');
        }
        if (!outs.every((x, i) => x.ctx === selfOuts[i].ctx) || !ins.every((x, i) => x.ctx === selfIns[i].ctx)) {
            throw new Error('Context mismatch');
        }
        const selfVars = [...selfOuts, ...selfIns];
        const vars = [...outs, ...ins];
        const phis = this.phis.map(phi => ctx.substitute(phi,
            ...selfVars.map((x, i) => [x, vars[i]] as [z3.Expr, z3.Expr])) as z3.Bool);
        const pres = this.preconds.map(p => ctx.substitute(p,
            ...selfIns.map((x, i) => [x, ins[i]] as [z3.Expr, z3.Expr])) as z3.Bool);
        return [pres, phis];
    }
}

export class Func extends Spec {
    precond: z3.Bool;
    func: z3.Expr;

    constructor(name: string, phi: z3.Expr, precond: z3.Bool = ctx.Bool.val(true), inputs: z3.Expr[] = []) {
        const inputVars = _collect_vars(phi);

        // If no inputs are specified, take identifiers in lexicographical order
        if (inputs.length === 0) {
            inputs = [...inputVars].sort((a, b) => String(a).localeCompare(String(b)));
        }

        // Check if precondition uses only variables that are in phi
        if (![..._collect_vars(precond)].every(varExpr => inputVars.has(varExpr))) {
            throw new Error('Precondition uses variables that are not in phi');
        }

        const resType = phi.sort; // Assuming phi has a sort method
        const out = ctx.FreshConst(resType);

        // super(name, [ctx.Eq(ctx.FreshConst(resType), phi)], [ctx.FreshConst(resType)], inputs, [precond]);
        super(name, [out.eq(phi)], [out], inputs, [precond]);

        this.precond = precond;
        this.func = phi;
    }

    // Cached property
    // get isDeterministic(): boolean {
    async isDeterministic(): Promise<boolean> {
        return true;
    }

    translate<N extends string>(ctx: z3.Context<N>): Func {
        // const ins = this.inputs.map(i => i.translate(ctx));
        // return new Func(this.name, this.func.translate(ctx), this.precond.translate(ctx), ins);
        const ins = this.inputs.map(i => i);
        return new Func(this.name, this.func, this.precond, ins);
    }

    // Cached property
    get outType(): z3.Sort {
        return this.outTypes[0];
    }

    // Check if the function is commutative
    // get isCommutative(): boolean {
    async isCommutative(): Promise<boolean> {
        // If the operator inputs have different sorts, it cannot be commutative
        if (new Set(this.inputs.map(v => v.sort)).size > 1 || this.inputs.length > 3) {
            return false;
        }

        // const ctx = new Context();
        // const precond = this.precond.translate(ctx);
        // const func = this.func.translate(ctx);
        // const ins = this.inputs.map(x => x.translate(ctx));
        const precond = this.precond;
        const func = this.func;
        const ins = this.inputs.map(x => x);
        const subst = (f: z3.Expr, i: z3.Expr[]) => ctx.substitute(f, ...ins.map((x, j) => [x, i[j]] as [z3.Expr, z3.Expr]));

        const fs = combine(permute(ins), 2).map(([a, b]) => {
            return ctx.And(...[
                subst(precond, a) as z3.Bool,
                subst(precond, b) as z3.Bool,
                ctx.Not(ctx.Eq(subst(func, a), subst(func, b)))
            ]);
        });

        const solver = new ctx.Solver();
        solver.add(ctx.Or(...fs));
        return await solver.check() === 'unsat';
    }
}

type Op = Func;
type Insns = [boolean, number][];
type Outputs = [boolean, number][];
type OutputMap = { [key: number]: string[] };
export class Prg {
    outputNames: string[];
    inputNames: string[];
    insns: [Op, Insns][];
    outputs: Outputs;
    outputMap: OutputMap;

    constructor(outputNames: string[], inputNames: string[], insns: [Op, Insns][], outputs: Outputs) {
        this.outputNames = outputNames;
        this.inputNames = inputNames;
        this.insns = insns;
        this.outputs = outputs;
        this.outputMap = {};

        // Create a map for output variables
        for (let i = 0; i < outputs.length; i++) {
            const [isConst, v] = outputs[i];
            if (!isConst) {
                this.outputMap[v] = this.outputMap[v] || [];
                this.outputMap[v].push(outputNames[i]);
            }
        }
    }

    varName(i: number): string {
        if (i < this.inputNames.length) {
            return this.inputNames[i];
        } else if (i in this.outputMap) {
            return this.outputMap[i][0];
        } else {
            return `x${i}`;
        }
    }

    get length(): number {
        return this.insns.length;
    }

    toString(): string {
        const allNames = [...this.inputNames, ...this.outputNames, ...Object.values(this.outputMap).map(names => names[0])];
        const maxLen = Math.max(...allNames.map(s => s.length));
        const nInputs = this.inputNames.length;
        const jv = (args: Insns) => args.map(([c, v]) => c ? v : this.varName(v)).join(', ');
        let res: string[] = [];

        for (const [i, names] of Object.entries(this.outputMap)) {
            const index = parseInt(i);
            if (index < nInputs) {
                res.push(...names.map(name => `${name.padEnd(maxLen)} = ${this.inputNames[index]}`));
            }
        }

        for (let i = 0; i < this.insns.length; i++) {
            const [op, args] = this.insns[i];
            const y = this.varName(i + nInputs);
            res.push(`${y.padEnd(maxLen)} = ${op.name}(${jv(args)})`);
        }

        for (const names of Object.values(this.outputMap)) {
            for (let i = 1; i < names.length; i++) {
                res.push(`${names[i].padEnd(maxLen)} = ${names[0]}`);
            }
        }

        return res.join('\n');
    }

    printGraphviz(file: any): void {
        const constants: { [key: number]: string } = {};

        function printArg(node: number | string, i: number, isConst: boolean, v: number | string): void {
            if (isConst) {
                if (!(v in constants)) {
                    constants[v as number] = `const${Object.keys(constants).length}`;
                    file.write(`  ${constants[v as number]} [label="${v}"];\n`);
                }
                v = constants[v as number];
            }
            file.write(`  ${node} -> ${v} [label="${i}"];\n`);
        }

        const nInputs = this.inputNames.length;
        file.write(`digraph G {\n`);
        file.write(`  rankdir=BT\n`);
        file.write(`  {\n`);
        file.write(`    rank = same;\n`);
        file.write(`    edge[style=invis];\n`);
        file.write(`    rankdir = LR;\n`);

        for (let i = 0; i < nInputs; i++) {
            file.write(`    ${i} [label="${this.inputNames[i]}"];\n`);
        }

        file.write(`    ${Array.from({ length: nInputs }, (_, i) => i).join(' -> ')};\n`);
        file.write(`  }\n`);

        for (let i = 0; i < this.insns.length; i++) {
            const [op, args] = this.insns[i];
            const node = i + nInputs;
            file.write(`  ${node} [label="${op.name}",ordering="out"];\n`);
            for (let j = 0; j < args.length; j++) {
                const [isConst, v] = args[j];
                printArg(node, j, isConst, v);
            }
        }

        file.write(`  return [label="return",ordering="out"];\n`);

        for (let i = 0; i < this.outputs.length; i++) {
            const [isConst, v] = this.outputs[i];
            printArg('return', i, isConst, v);
        }

        file.write(`}\n`);
    }
}

export class EnumBase<T, U> {
    cons: T[];
    itemToCons: Map<U, T>;
    consToItem: Map<T, U>;

    constructor(items: U[], cons: T[]) {
        if (items.length !== cons.length) {
            throw new Error('Number of items and constructors must match');
        }
        this.cons = cons;
        this.itemToCons = new Map();
        this.consToItem = new Map();
        for (let i = 0; i < items.length; i++) {
            const item = items[i];
            const con = cons[i];
            this.itemToCons.set(item, con);
            this.consToItem.set(con, item);
        }
    }

    get length(): number {
        return this.cons.length;
    }
}


// Note: EnumSort does not exists in types.d.ts or highlevel
// however, z3-built.js contains _Z3_mk_enumeration_sort in 11737

// EnumSortEnum class
// class EnumSortEnum<T extends Showable> extends EnumBase<z3.Z3_func_decl, T> {
//     sort: z3.Z3_sort; // Type of sort depends on the library being used
export class EnumSortEnum<T extends Showable> extends EnumBase<[z3.FuncDecl, z3.FuncDecl], T> {
    sort: z3.Sort; // Type of sort depends on the library being used

    constructor(name: string, items: T[], ctx: z3.Context) {
        // Assuming EnumSort and BitVecSort are defined elsewhere
        const {
            rv: sort,
            enum_consts: cons,
            enum_testers: testers
        } = Z3.mk_enumeration_sort(ctx.ptr,
            Z3.mk_string_symbol(ctx.ptr, name),
            items.map(i => Z3.mk_string_symbol(ctx.ptr, i.toString()))
        );
        // it would be better to create FuncDeclImpl, and SortImpl instances
        // but the classes are not visible to the outside (internally created in high-level->createApi->createContext)
        // increment reference count
        // Z3.inc_ref(ctx.ptr, sort);
        // for (let i = 0; i < items.length; i++) {
        //     Z3.inc_ref(ctx.ptr, cons[i]);
        //     Z3.inc_ref(ctx.ptr, testers[i]);
        // }
        const consFunc = cons.map((c, i) => ctx._toAst(c) as z3.FuncDecl);
        const testerFunc = testers.map((c, i) => ctx._toAst(c) as z3.FuncDecl);
        const combined = consFunc.map((c, i) => [c, testerFunc[i]] as [z3.FuncDecl, z3.FuncDecl]);
        super(items, combined);
        this.sort = ctx._toSort(sort);
    }

    // TODO: test
    getFromModelVal(val: z3.Expr): T {
        // find (val,_) in consToItem
        for (const [k, v] of this.consToItem) {
            const k_str = k[0].sexpr().toString();
            const val_str = val.sexpr().toString();
            if (k_str === val_str
                || k_str.indexOf("declare-fun " + val.sexpr().toString()) !== -1
            ) {
                return v;
            }
        }

        console.error("We have the following consToItem keys:");
        console.error([...this.consToItem.keys()].map(k => k[0].sexpr().toString()));
        throw new Error('Invalid enum value: ' + String(val));
    }

    // getFromModelVal(val: [z3.FuncDecl,z3.FuncDecl]): T {
    //     if (!this.consToItem.has(val)) {
    //         throw new Error('Invalid enum value');
    //     }
    //     return this.consToItem.get(val) as T;
    // }

    addRangeConstr(solver: z3.Solver, variable: z3.Arith): void {
        return;
    }
}

function _bv_sort(n: number, ctx: z3.Context): z3.BitVecSort {
    const bits = Math.max(1, Math.floor(Math.log2(n)) + 1);
    return ctx.BitVec.sort(bits);
}

// class BitVecEnum<T> extends EnumBase<number, T> {
//     sort: z3.Sort; // Type of sort depends on the library being used

//     constructor(name: string, items: T[], ctx: z3.Context) {
//         // Assuming EnumSort and BitVecSort are defined elsewhere
//         const cons = items.map((_, i) => i);
//         super(items, cons);
//         this.sort = _bv_sort(items.length, ctx);
//     }

//     getFromModelVal(val: number): T {
//         if (!this.consToItem.has(val)) {
//             throw new Error('Invalid enum value');
//         }
//         return this.consToItem.get(val) as T;
//     }

//     addRangeConstr(solver: z3.Solver, variable: z3.Arith): void {
//         solver.add(variable.le(this.cons.length - 1));
//     }
// }

function _eval_model(solver: z3.Solver, vars: z3.Expr[]): z3.Expr[] {
    const model = solver.model();
    return vars.map(v => model.eval(v, true));
}

export class SpecWithSolver {
    ctx: z3.Context;
    spec: Spec;
    ops: Func[];
    opEnum: EnumSortEnum<Func>;
    tyEnum: EnumSortEnum<z3.Sort>;
    verif: z3.Solver;
    eval: z3.Solver;
    inputs: z3.Expr[];
    outputs: z3.Expr[];

    constructor(spec: Spec, ops: Func[], ctx: z3.Context) {
        this.ctx = ctx;
        this.spec = spec.translate(ctx);
        this.ops = ops.map(op => op.translate(ctx));

        // Prepare operator enum sort
        this.opEnum = new EnumSortEnum('Operators', this.ops, ctx);

        // Create map of types to their id
        const types = new Set<z3.Sort>();
        for (const op of this.ops) {
            // types.add(...op.outTypes, ...op.inTypes);
            // types.add(...op.inTypes);
            // types.add(...op.outTypes);
            op.inTypes.forEach(ty => types.add(ty));
            op.outTypes.forEach(ty => types.add(ty));
        }
        this.tyEnum = new EnumSortEnum('Types', Array.from(types), ctx);

        // Prepare verification solver
        this.verif = new ctx.Solver();
        this.eval = new ctx.Solver();
        this.inputs = this.spec.inputs;
        this.outputs = this.spec.outputs;

        // this.verif.add(ctx.Or(...this.spec.preconds.map((pre, i) => ctx.And(pre, ctx.Not(this.spec.phis[i])))));
        this.verif.add(ctx.Or(
            ...zip(this.spec.preconds, this.spec.phis).map(([pre, phi]) => ctx.And(pre, phi.not()))
        ));
        this.spec.phis.forEach(phi => this.eval.add(phi));
    }

    async evalSpec(inputVals: z3.Expr[]): Promise<z3.Expr[]> {
        const s = this.eval;
        s.push();
        for (let i = 0; i < this.inputs.length; i++) {
            // s.add(this.inputs[i] === inputVals[i]);
            s.add(this.inputs[i].eq(inputVals[i]));
        }
        const res = await s.check();
        if (res !== 'sat') {
            throw new Error('Spec evaluation failed: Unsatisfiable');
        }
        const evaluated = _eval_model(s, this.outputs);
        s.pop();
        return evaluated;
    }

    async sampleN(n: number): Promise<z3.Expr[][]> {
        const result: z3.Expr[][] = [];
        const s = this.eval;
        s.push();
        for (let i = 0; i < n; i++) {
            if (await s.check() === 'unsat') {
                if (result.length === 0) {
                    throw new Error('must have sampled the spec at least once');
                }
                break;
            }
            // const model = s.model();
            const ins = _eval_model(s, this.inputs);
            result.push(ins);
            s.add(ctx.Or(...ins.map((v, j) => v.neq(ins[j]))));
        }
        s.pop();
        return result;
    }

    async synth_n(
        nInsns: number,
        debug: number = 0,
        maxConst: number | null = null,
        initSamples: z3.Expr[][] = [],
        outputPrefix: string | null = null,
        theory: string | null = null,
        resetSolver: boolean = true,
        optNoDeadCode: boolean = true,
        optNoCSE: boolean = true,
        optConst: boolean = true,
        optCommutative: boolean = true,
        optInsnOrder: boolean = true
    ): Promise<[Prg | null, any[]]> {
        // Define inner functions and variables

        // Define debug function
        function d(level: number, ...args: any[]) {
            if (debug >= level) {
                console.log(...args);
            }
        }

        // Define other inner functions as necessary

        // Implement the main logic of the synth_n method
        let ops = this.ops;
        let ctx = this.ctx;
        let spec = this.spec;
        let inTys = spec.inTypes;
        let outTys = spec.outTypes;
        let nInputs = inTys.length;
        let nOutputs = outTys.length;
        let outInsn = nInputs + nInsns;
        let length = outInsn + 1;

        let maxArity = Math.max(...ops.map(op => op.arity));
        let arities = [...Array(nInputs).fill(0), ...Array(nInsns).fill(maxArity), nOutputs];
        // console.log("arities",arities);
        d(3, 'arities:', arities);

        // Define variable getters and other helper functions
        const tySort = this.tyEnum.sort;
        const opSort = this.opEnum.sort;
        const lnSort = _bv_sort(length, ctx);
        const blSort = ctx.Bool.sort();

        const evalIns = this.inputs;
        const evalOuts = this.outputs;
        const verif = this.verif;

        const self = this;

        // memoized
        function getVar(ty: z3.Sort, name: string): z3.Expr {
            if (ctx !== ty.ctx) {
                throw new Error('Context mismatch');
            }
            return ctx.Const(name, ty);
        }

        // memoized
        function tyName(ty: z3.Sort): string {
            return ty.toString().replace(/[ ,()\.]/g, '_');
        }

        function varInsnOp(insn: string): z3.Expr {
            return getVar(opSort, `insn_${insn}_op`);
        }

        function* varInsnOpndsIsConst(insn: number): Generator<z3.Bool, void, unknown> {
            for (let opnd = 0; opnd < arities[insn]; opnd++) {
                yield getVar(blSort, `insn_${insn}_opnd_${opnd}_is_const`) as z3.Bool;
            }
        }

        function* varInsnOpOpndsConstVal(insn: number, opndTys: z3.Sort[]): Generator<z3.Expr, void, unknown> {
            for (let opnd = 0; opnd < opndTys.length; opnd++) {
                yield getVar(opndTys[opnd], `insn_${insn}_opnd_${opnd}_${tyName(opndTys[opnd])}_const_val`);
            }
        }

        function* varInsnOpnds(insn: number, arities: number[]): Generator<z3.BitVec, void, unknown> {
            for (let opnd = 0; opnd < arities[insn]; opnd++) {
                yield getVar(lnSort, `insn_${insn}_opnd_${opnd}`) as z3.BitVec;
            }
        }

        function* varInsnOpndsVal(insn: number, tys: z3.Sort[], instance: string): Generator<z3.Expr, void, unknown> {
            for (let opnd = 0; opnd < tys.length; opnd++) {
                yield getVar(tys[opnd], `insn_${insn}_opnd_${opnd}_${tyName(tys[opnd])}_${instance}`);
            }
        }

        function* varOutsVal(instance: string): Generator<z3.Expr, void, unknown> {
            for (let opnd of varInsnOpndsVal(outInsn, outTys, instance)) {
                yield opnd;
            }
        }

        // function* varInsnOpndsType(insn: number, arities: number[]): Generator<z3.Expr, void, unknown> {
        //     for (let opnd = 0; opnd < arities[insn]; opnd++) {
        //         yield getVar(tySort, `insn_${insn}_opnd_type_${opnd}`);
        //     }
        // }
        function varInsnOpndsType(insn: number, arities: number[]): z3.Expr[] {
            const res = [];
            for (let opnd = 0; opnd < arities[insn]; opnd++) {
                // yield getVar(tySort, `insn_${insn}_opnd_type_${opnd}`);
                res.push(getVar(tySort, `insn_${insn}_opnd_type_${opnd}`));
            }
            return res;
        }

        function varInsnRes(insn: number, ty: any, instance: string): z3.Expr {
            return getVar(ty, `insn_${insn}_res_${tyName(ty)}_${instance}`);
        }

        function varInsnResType(insn: number): z3.Expr {
            return getVar(tySort, `insn_${insn}_res_type`);
        }

        function varInputRes(insn: number, instance: string): z3.Expr {
            return varInsnRes(insn, inTys[insn], instance);
        }

        function isOpInsn(insn: number): boolean {
            return insn >= nInputs && insn < length - 1;
        }

        function addConstrWfp(solver: z3.Solver): void {
            // acyclic: line numbers of uses are lower than line number of definition
            // i.e.: we can only use results of preceding instructions
            for (let insn = 0; insn < length; insn++) {
                for (let v of varInsnOpnds(insn, arities)) {
                    solver.add(v.ule(insn - 1));
                }
            }

            // pin operands of an instruction that are not used (because of arity)
            // to the last input of that instruction
            for (let insn = nInputs; insn < length - 1; insn++) {
                let opnds = [...varInsnOpnds(insn, arities)];
                for (let [op, [opCtor, opTest]] of self.opEnum.itemToCons.entries()) {
                    let unused = opnds.slice(op.arity);
                    for (let opnd of unused) {
                        // solver.add(Implies(varInsnOp(insn) == opId, opnd == opnds[op.arity - 1]));
                        // solver.add(ctx.Implies(varInsnOp(insn.toString()).eq(opId), opnd.eq(opnds[op.arity - 1])));
                        solver.add(ctx.Implies(opTest.call(varInsnOp(insn.toString())).eq(true), opnd.eq(opnds[op.arity - 1])));
                    }
                }
            }

            // Add a constraint for the maximum amount of constants if specified.
            // The output instruction is exempt because we need to be able
            // to synthesize constant outputs correctly.
            let maxConstRan = [...Array(length - nInputs - 1).keys()].map(i => i + nInputs);
            if (maxConst !== null && maxConstRan.length > 0) {
                // solver.add(AtMost([...maxConstRan.flatMap(insn =>
                //     [...varInsnOpndsIsConst(insn)].map(v => v)), maxConst]));
                // solver.add(ctx.AtMost([...maxConstRan.flatMap(insn =>
                //     [...varInsnOpndsIsConst(insn)].map(v => v)), maxConst]));

                // context has no AtMost
                // we encode it as a sum of booleans <= maxConst
                const bools = maxConstRan.flatMap(insn => [...varInsnOpndsIsConst(insn)]);
                const ints = bools.map(b => ctx.If(b, 1, 0));
                solver.add(ctx.Sum(ctx.Int.val(0), ...ints).le(ctx.Int.val(maxConst)));
            }

            // if we have at most one type, we don't need type constraints
            if (self.tyEnum.length <= 1) {
                return;
            }

            // for all instructions that get an op
            // add constraints that set the type of an instruction's operand
            // and the result type of an instruction
            let types = self.tyEnum.itemToCons;
            const typesGet = (ty: z3.Sort): [z3.FuncDecl, z3.FuncDecl] => {
                return mapGetByStrKey(types, ty);
            }
            // function typesGet(ty: z3.Sort): [z3.FuncDecl, z3.FuncDecl] {
            //     // return types.get(opTy)!;
            //     const out_ty_enum = [...types.entries()].find(([k,v]) => String(k) === String(ty))![1];
            //     return out_ty_enum;
            // }
            for (let insn = nInputs; insn < length - 1; insn++) {
                self.opEnum.addRangeConstr(solver, varInsnOp(insn.toString()) as z3.Arith);
                for (let [op, [opCtor, opTest]] of self.opEnum.itemToCons.entries()) {
                    // add constraints that set the result type of each instruction
                    // solver.add(Implies(varInsnOp(insn) == opId,
                    //     varInsnResType(insn) == types[op.outType]));
                    // solver.add(ctx.Implies(opTest.call(varInsnOp(insn.toString())).eq(true),
                    //     types.get(op.outType)![1].call(varInsnResType(insn)).eq(true)));
                    // varInsnResType(insn).eq(types.get(op.outType))));
                    // const out_ty_enum = [...types.entries()].find(([k,v]) => String(k) === String(op.outType))![1];
                    solver.add(ctx.Implies(opTest.call(varInsnOp(insn.toString())).eq(true),
                        typesGet(op.outType)[1].call(varInsnResType(insn)).eq(true)));

                    // add constraints that set the type of each operand
                    // for (let [opTy, v] of zip(op.inTypes, varInsnOpndsType(insn, arities))) {
                    //     solver.add(Implies(varInsnOp(insn) == opId, v == types[opTy]));
                    // }
                    for (let [opTy, v] of op.inTypes.map((opTy, i) => [opTy, varInsnOpndsType(insn, arities)[i]] as [z3.Sort, z3.Expr])) {
                        solver.add(ctx.Implies(opTest.call(varInsnOp(insn.toString())).eq(true),
                            // v.eq(types.get(opTy)![1])
                            // types.get(opTy)![1].call(v).eq(true)
                            typesGet(opTy)[1].call(v).eq(true)
                        ));
                    }

                }
            }

            // define types of inputs
            for (let [inp, ty] of inTys.map((ty, i) => [i, ty] as [number, z3.Sort])) {
                // solver.add(varInsnResType(inp) == types[ty]);
                // solver.add(types.get(ty)![1].call(varInsnResType(inp)).eq(true));
                solver.add(typesGet(ty)[1].call(varInsnResType(inp)).eq(true));
            }

            // define types of outputs
            // for (let [v, ty] of zip(varInsnOpndsType(outInsn, arities), outTys)) {
            //     solver.add(v == types[ty]);
            // }
            for (let [v, ty] of zip(varInsnOpndsType(outInsn, arities), outTys)) {
                // varInsnOpndsType(outInsn, arities).map((v, i) => [v, outTys[i]] as [z3.Expr, z3.Sort])) {
                // solver.add(types.get(ty)![1].call(v).eq(true));
                solver.add(typesGet(ty)[1].call(v).eq(true));
            }

            // constrain types of outputs
            for (let insn = nInputs; insn < length; insn++) {
                for (let other = 0; other < insn; other++) {
                    // for (let [opnd, c, ty] of zip(varInsnOpnds(insn, arities),
                    //     varInsnOpndsIsConst(insn, arities), varInsnOpndsType(insn, arities))) {
                    //     solver.add(Implies(Not(c), Implies(opnd == other,
                    //         ty == varInsnResType(other))));
                    // }
                    for (let [[opnd, c], ty] of
                        zip(
                            zip([...varInsnOpnds(insn, arities)], [...varInsnOpndsIsConst(insn)]),
                            varInsnOpndsType(insn, arities))) {
                        // if(opnd.sort !== other.sort) {
                        //     throw new Error('Sort mismatch in addConstrWfp: opnd ('+opnd.sort+') and other ('+other.sort+')');
                        // }
                        const other_bv = ctx.BitVec.val(other, opnd.sort);
                        // solver.add(Implies(Not(c), Implies(opnd == other, \
                        //     ty == var_insn_res_type(other))))

                        // solver.add(ctx.Implies(ctx.Not(c),
                        //     // ctx.Implies(opnd.eq(other),
                        //     ctx.Implies(opnd.eq(other_bv),
                        //         // types.get(ty.sort)![1].call(ty).eq(true))));
                        //         // typesGet(ty.sort)[1].call(ty).eq(true))));
                        //         typesGet(ty as z3.Sort)[1].call(ty).eq(true))));

                        // TODO: maybe need lookup in types
                        solver.add(ctx.Implies(ctx.Not(c),
                            ctx.Implies(opnd.eq(other_bv),
                                varInsnResType(other).eq(ty))));
                    }
                }
                self.tyEnum.addRangeConstr(solver, varInsnResType(insn) as z3.Arith);
            }
        }

        function addConstrOpt(solver: z3.Solver) {
            // TODO: skiped for now (line 568-612)
        }

        function iterOpndInfo(insn: number, tys: z3.Sort[], instance: string):
            [
                z3.Sort,
                z3.BitVec,
                z3.Expr,
                z3.Bool,
                z3.Expr
            ][] {
            const opnds = [...varInsnOpnds(insn, arities)];
            const opndsVal = [...varInsnOpndsVal(insn, tys, instance)];
            const isConsts = [...varInsnOpndsIsConst(insn)];
            const opOpndsConstVal = [...varInsnOpOpndsConstVal(insn, tys)];

            // if (opnds.length !== tys.length || opndsVal.length !== tys.length || isConsts.length !== tys.length || opOpndsConstVal.length !== tys.length) {
            //     throw new Error('Invalid input length. Got opnds: '+opnds.length+', tys: '+tys.length+', opndsVal: '+opndsVal.length+', isConsts: '+isConsts.length+', opOpndsConstVal: '+opOpndsConstVal.length);
            // }

            // return tys.map((ty, i) => 
            //     [ty, opnds[i], opndsVal[i], isConsts[i], opOpndsConstVal[i]] as [z3.Sort, z3.BitVec, z3.Expr, z3.Bool, z3.Expr]);

            const common_length = Math.min(tys.length, opnds.length, opndsVal.length, isConsts.length, opOpndsConstVal.length);
            return [...Array(common_length).keys()].map(i =>
                [tys[i], opnds[i], opndsVal[i], isConsts[i], opOpndsConstVal[i]] as [z3.Sort, z3.BitVec, z3.Expr, z3.Bool, z3.Expr]);

        }

        function addConstrConn(solver: any, insn: number, tys: any[], instance: string): void {
            for (let [ty, l, v, c, cv] of iterOpndInfo(insn, tys, instance)) {
                // if the operand is a constant, its value is the constant value
                // solver.add(Implies(c, v == cv));
                solver.add(c.implies(v.eq(cv)));
                // else, for each instruction preceding it ...
                for (let other = 0; other < insn; other++) {
                    let r = varInsnRes(other, ty, instance);
                    // ... the operand is equal to the result of the instruction
                    // solver.add(Implies(Not(c), Implies(l == other, v == r)));
                    const other_bv = ctx.BitVec.val(other, l.sort);
                    // solver.add(c.not().implies(l.eq(other)).implies(v.eq(r)));
                    // solver.add(c.not().implies(l.eq(other_bv)).implies(v.eq(r)));
                    solver.add(
                        ctx.Implies(
                            c.not(),
                            ctx.Implies(
                                l.eq(other_bv),
                                v.eq(r)
                            )
                        )
                    );
                }
            }
        }

        // create a new instance of state variables
        function addConstrInstance(solver: z3.Solver, instance: string): void {
            // for all instructions that get an op
            for (let insn = nInputs; insn < length - 1; insn++) {
                // add constraints to select the proper operation
                let opVar = varInsnOp(insn.toString());
                // for (let [op, opId] of Object.entries(self.opEnum.itemToCons)) {
                for (let [op, [opCtor, opTest]] of self.opEnum.itemToCons.entries()) {
                    let res = varInsnRes(insn, op.outType, instance);
                    let opnds = [...varInsnOpndsVal(insn, op.inTypes, instance)];
                    let [[precond], [phi]] = op.instantiate([res], opnds);
                    // solver.add(Implies(opVar == opId, And([precond, phi])));
                    solver.add(ctx.Implies(opTest.call(opVar).eq(true), ctx.And(...[precond, phi])));
                }
                // connect values of operands to values of corresponding results
                for (let op of ops) {
                    addConstrConn(solver, insn, op.inTypes, instance);
                }
            }
            // add connection constraints for output instruction
            addConstrConn(solver, outInsn, outTys, instance);
        }

        // assert that i-th instance of state variables equal outVals given input values inVals
        function addConstrIoSample(solver: any, instance: string, inVals: z3.Expr[], outVals: z3.Expr[]): void {
            // add input value constraints
            // assert(inVals.length == nInputs && outVals.length == nOutputs);
            if (inVals.length !== nInputs || outVals.length !== nOutputs) {
                throw new Error('Invalid input values');
            }
            for (let inp = 0; inp < inVals.length; inp++) {
                // assert(inVals[inp] !== null);
                if (inVals[inp] === null) {
                    throw new Error('Invalid input value');
                }
                let res = varInputRes(inp, instance);
                // solver.add(res == inVals[inp]);
                solver.add(res.eq(inVals[inp]));
            }
            for (let [out, val] of zip([...varOutsVal(instance)], outVals)) {
                // assert(val !== null);
                if (val === null) {
                    throw new Error('Invalid output value');
                }
                // solver.add(out == val);
                solver.add(out.eq(val));
            }
        }

        function addConstrIoSpec(solver: any, instance: string, inVals: any[]): void {
            // add input value constraints
            // assert(inVals.length == nInputs);
            // assert(inVals.every(val => val !== null));
            if (inVals.length !== nInputs || inVals.some(val => val === null)) {
                throw new Error('Invalid input values');
            }
            for (let inp = 0; inp < inVals.length; inp++) {
                // solver.add(inVals[inp] == varInputRes(inp, instance));
                solver.add(inVals[inp].eq(varInputRes(inp, instance)));
            }
            let outs = [...varOutsVal(instance)];
            let [preconds, phis] = spec.instantiate(outs, inVals);
            for (let [pre, phi] of zip(preconds, phis)) {
                // solver.add(Implies(pre, phi));
                solver.add(pre.implies(phi));
            }
        }

        function addConstrSolForVerif(model: z3.Model): void {
            for (let insn = 0; insn < length; insn++) {
                let tys = null;
                if (isOpInsn(insn)) {
                    let v = varInsnOp(insn.toString());
                    // verif.add(model[v] == v);
                    // verif.add(model.eval(v).eq(v));
                    verif.add(v.eq(model.eval(v)));
                    let val = model.eval(v, true);
                    // reassociate backward the split between enum ctor and tester
                    // see other uses of getFromModelVal
                    let op = self.opEnum.getFromModelVal(val);
                    tys = op.inTypes;
                } else {
                    tys = outTys;
                }

                // set connection values
                for (let [_, opnd, v, c, cv] of iterOpndInfo(insn, tys, 'verif')) {
                    if (c === undefined) {
                        throw new Error('Invalid c');
                    }
                    // let isConst = isTrue(model[c]) ?? false;
                    // let isConst = model.eval(c).eq(true);
                    // let isConst = asBool(model.eval(c).eq(true));
                    let isConst = asBool(model.eval(c));
                    // let isConst_res = model.eval(c,true);
                    // let isConst = isConst_res === undefined ? false : isConst_res.eq(true);

                    // verif.add(isConst == c);
                    // verif.add(isConst.eq(c));
                    verif.add(c.eq(isConst));
                    if (isConst) {
                        // verif.add(model[cv] == v);
                        verif.add(model.eval(cv).eq(v));
                    } else {
                        // verif.add(model[opnd] == opnd);
                        verif.add(model.eval(opnd).eq(opnd));
                    }
                }
            }
        }

        function addConstrSpecVerif(): void {
            let verifOuts = [...varOutsVal('verif')];
            // assert(verifOuts.length == evalOuts.length);
            // assert(verifOuts.length == spec.preconds.length);
            if (verifOuts.length !== evalOuts.length || verifOuts.length !== spec.preconds.length) {
                throw new Error('Invalid output values');
            }
            for (let inp = 0; inp < evalIns.length; inp++) {
                // verif.add(varInputRes(inp, 'verif') == evalIns[inp]);
                verif.add(varInputRes(inp, 'verif').eq(evalIns[inp]));
            }
            for (let [v, e] of zip(verifOuts, evalOuts)) {
                // verif.add(v == e);
                verif.add(v.eq(e));
            }
        }

        function createPrg(model: z3.Model): Prg {
            function* prepOpnds(insn: number, tys: z3.Sort[]): Generator<[boolean, number], void, unknown> {
                for (let [_, opnd, v, c, cv] of iterOpndInfo(insn, tys, 'verif')) {
                    // let isConst = isTrue(model[c]) ?? false;
                    // console.log("model[c] = ", model.eval(c));
                    // let isConst = model.eval(c).eq(true);
                    // const isConst_res = model.get(c);
                    // const isConst = isConst_res === undefined ? false : asBool(isConst_res);
                    let isConst = asBool(model.eval(c));
                    // yield (isConst, isConst ? model[cv] : model[opnd].asLong());
                    // model.eval(cv).sexpr()
                    // TODO: the model completion should (probably) not be necessary here
                    yield [isConst, asLong(isConst ? model.eval(cv) : model.eval(opnd, true))] as [boolean, number];
                }
            }

            let insns: [Func, Insns][] = [];
            for (let insn = nInputs; insn < length - 1; insn++) {
                let val = model.eval(varInsnOp(insn.toString()), true);
                // reassociate backward the split between enum ctor and tester
                // see other uses of getFromModelVal
                let op = self.opEnum.getFromModelVal(val);
                let opnds = [...prepOpnds(insn, op.inTypes)];
                insns.push([op, opnds] as [Func, Insns]);
            }
            let outputs = [...prepOpnds(outInsn, outTys)];
            let outputNames = spec.outputs.map(v => String(v));
            let inputNames = spec.inputs.map(v => String(v));
            return new Prg(outputNames, inputNames, insns, outputs);
        }

        function writeSmt2(solver: z3.Solver, ...args: any[]): void {
            if (outputPrefix !== null) {
                let filename = `${outputPrefix}_${args.join("_")}.smt2`;
                // fs.writeFileSync(filename, solver.toSmt2());
                console.log("TODO SMT2");
            }
        }

        // function writeSmt2(solver: any, ...args: any[]): void {
        //     if (!(solver instanceof z3.Solver)) {
        //         let s = new Solver(ctx);
        //         s.add(solver);
        //         solver = s;
        //     }
        //     if (outputPrefix !== null) {
        //         let filename = `${outputPrefix}_${args.join("_")}.smt2`;
        //         fs.writeFileSync(filename, solver.toSmt2());
        //     }
        // }


        // setup the synthesis solver
        let synthSolver: z3.Solver;
        if (theory) {
            // synthSolver = SolverFor(theory, { ctx: ctx });
            synthSolver = new ctx.Solver(theory);
        } else {
            // synthSolver = new Tactic('psmt', { ctx: ctx }).solver();
            // synthSolver = new ctx.Tactic('psmt').
            synthSolver = new ctx.Solver();
        }
        // let synth = resetSolver ? new Goal({ ctx: ctx }) : synthSolver;
        // resetSolver = false;
        // let synth = synthSolver;
        let synth = resetSolver ? new ctx.Solver() : synthSolver;
        d(3, 'add wfp constraints to synth');
        addConstrWfp(synth);
        addConstrOpt(synth);

        let stats: any[] = [];
        let samples = initSamples.length > 0 ? initSamples : await this.sampleN(1);
        // assert(samples.length > 0, 'need at least 1 initial sample');
        if (samples.length <= 0) {
            throw new Error('need at least 1 initial sample');
        }
        d(3, 'used input samples:', samples);
        d(3, 'input samples as sexpr:', String(samples));
        let useOutputSamples = (await spec.isDeterministic()) && (await spec.isTotal());
        d(3, 'use output samples:', useOutputSamples);

        let i = 0; // processed samples
        while (true) {
            let stat: any = {};
            stats.push(stat);
            let oldI = i;

            for (let sample of samples) {
                let sampleStr = String(sample);
                let sampleOut = sampleStr.length < 50 ? sampleStr : sampleStr.slice(0, 50) + '...';
                d(1, 'sample', i, sampleOut);
                addConstrInstance(synth, i.toString());
                if (useOutputSamples) {
                    let outVals = await this.evalSpec(sample);
                    d(3, 'output values:', String(outVals));
                    addConstrIoSample(synth, i.toString(), sample, outVals);
                } else {
                    addConstrIoSpec(synth, i.toString(), sample);
                }
                i++;
            }

            let samplesStr = i - oldI > 1 ? `${i - oldI}` : `${oldI}`;
            d(5, 'synth', samplesStr, synth);
            // writeSmt2(synth, 'synth', nInsns, i);
            let smt2 = [...synth.assertions()].map((a) => a.sexpr());
            d(7, 'synth smt2:', smt2.join('\n'));
            if (resetSolver) {
                synthSolver.reset();
                // synthSolver.add(synth);
                for (let c of synth.assertions()) {
                    synthSolver.add(c);
                }
            }
            let res: z3.CheckSatResult;
            let synthTime: number | undefined;
            await withTimer(async (elapsed) => {
                res = await synthSolver.check();
                synthTime = elapsed();
                // d(3, synthSolver.statistics());
                // d(2, `synth time: ${synthTime / 1e9:.3f}`);
                const time_str = (synthTime / 1e9).toFixed(3);
                d(2, `synth time: ${time_str}`);
                stat['synth'] = synthTime;
            });

            if ((res!) === "sat") {
                // if sat, we found location variables
                let m = synthSolver.model();
                let prg = createPrg(m);
                stat['prg'] = String(prg).replace(/\n/g, '; ');

                d(4, 'model: ', m);
                d(2, 'program:', stat['prg']);

                // push a new verification solver state
                verif.push();
                // Add constraints that represent the instructions of
                // the synthesized program
                addConstrInstance(verif, 'verif');
                // Add constraints that relate the specification to
                // the inputs and outputs of the synthesized program
                addConstrSpecVerif();
                // add constraints that set the location variables
                // in the verification constraint
                addConstrSolForVerif(m);

                d(5, 'verif', samplesStr, verif);
                // writeSmt2(verif, 'verif', nInsns, samplesStr);
                let smt2 = [...verif.assertions()].map((a) => a.sexpr());
                d(7, 'verif smt2:', smt2.join('\n'));
                let verifTime: number;
                await withTimer(async (elapsed) => {
                    res = await verif.check();
                    verifTime = elapsed();
                });
                stat['verif'] = verifTime!;
                d(2, `verif time ${(verifTime! / 1e9).toFixed(3)}`);

                // found input for current program
                // such that the base verifier contradiction is satisfied 
                // (see above: \/ (pre /\ ~phi))
                if (res === "sat") {
                    // there is a counterexample, reiterate
                    samples = [_eval_model(this.verif, this.inputs)];
                    d(4, 'verification model', verif.model());
                    // d(4, 'verif sample', samples[0]);
                    d(4, 'verif sample', String(samples[0]));
                    verif.pop();
                } else {
                    verif.pop();
                    // we found no counterexample, the program is therefore correct
                    d(1, 'no counter example found');
                    return [prg, stats];
                }
            } else {
                // assert(res == unsat);
                if ((res!) !== "unsat") {
                    throw new Error('Synthesis failed. Got unexpected result from solver: ' + res!);
                }
                d(1, `synthesis failed for size ${nInsns}`);
                return [null, stats];
            }
        }
    }
}


export async function synth(spec: Spec, ops: Func[], iter_range: number[], n_samples: number = 1): Promise<[Prg | null, any[]]> {
    let all_stats: any[] = [];
    let ctx = spec.ctx;
    const spec_solver = new SpecWithSolver(spec, ops, ctx);
    const init_samples = await spec_solver.sampleN(n_samples);
    for (let n_insns of iter_range) {
        const res = await withTimer(async (elapsed) => {
            let [prg, stats] = await spec_solver.synth_n(n_insns, 10, null, init_samples);
            all_stats.push({
                "time": elapsed(),
                "iterations": stats
            });
            if (prg !== null) {
                return [prg, all_stats] as [Prg, any[]];
            }
            return null;
        });
        if (res !== null) {
            return res;
        }
    }
    return [null, all_stats];
}





console.log('')
console.log('### running the high-level API')
// let { Context } = await window.z3Promise;
//   let { Solver, Int } = Context('main');
const { Solver, Int } = ctx;
let solver = new Solver();
let x = Int.const('x');
solver.add(x.add(5).eq(9));
console.log(await solver.check());
console.log('x is', solver.model().get(x).toString());
const xval = solver.model().eval(x, true);
const xnum = asLong(xval);
console.log("x:", xval, xnum);
const b = x.ge(7);
const bval = solver.model().eval(b, true);
const bnum = asBool(bval);
console.log("b:", bval, bnum);

console.log("Collect vars");
console.log(Array.from(_collect_vars(x.add(5).eq(9))).map(x => x.toString()));
const y = Int.const('y');
console.log(Array.from(_collect_vars(x.add(y).eq(9))).map(x => x.toString()));


{
    // test_constant (L1112)
    console.log("");
    // const x = Int.const('x');
    // const y = Int.const('y');
    const x = ctx.BitVec.const('x', 32);
    const y = ctx.BitVec.const('y', 32);
    const mul = new Func("mul", x.mul(y));
    const spec = new Func("const", x.add(x));

    const [prg, stats] = await synth(spec, [mul], [1]);

    console.log("prg:", prg);
    console.log(String(prg));
}

// // })().catch(e => {
// //     console.error(e);
// // });
