import React from 'react';
import ReactDOM from 'react-dom/client';
import './index.css';
import App from './App';
import reportWebVitals from './reportWebVitals';



import * as z3 from 'z3-solver';

declare global {
  interface Window { z3Promise: ReturnType<typeof z3.init>; }
}
window.z3Promise = z3.init();
(async () => {
  // use the low-level API:
  // console.log('### running the low-level API')
  let { Z3 } = await window.z3Promise;
  let config = Z3.mk_config();
  let ctx = Z3.mk_context_rc(config);
  Z3.del_config(config);
  // let command = `
  //   (declare-const a Int)
  //   (declare-fun f (Int Bool) Int)
  //   (assert (< a 10))
  //   (assert (< (f a true) 100))
  //   (check-sat)
  //   (get-model)
  // `;
  // console.log(await Z3.eval_smtlib2_string(ctx, command));
  // Z3.del_context(ctx);


  function _collect_vars(expr : z3.Z3_ast) 
  : Set<z3.Z3_ast> {
    console.log("Checking",expr, "(",Z3.ast_to_string(ctx,expr),")");
    let vars = new Set<z3.Z3_ast>();
    function collect(expr : z3.Z3_ast) {
    //   if (expr.children().length === 0 && expr.decl().kind() === z3.Z3_decl_kind.Z3_OP_UNINTERPRETED) {
    //     vars.add(expr);
    //   } else {
    //     for (let child of expr.children()) {
    //       collect(child);
    //     }
    //   }


        if(!Z3.is_app(ctx,expr))
            return;
        const app = Z3.to_app(ctx,expr);
        const child_count = Z3.get_app_num_args(ctx,app);
        // console.log("Collecting",expr, "(",Z3.ast_to_string(ctx,expr),")","with",child_count,"children");
        console.log("Collecting",expr, "with",child_count,"children");
        if (child_count === 0 && 
            Z3.get_decl_kind(ctx,Z3.get_app_decl(ctx,app)) === z3.Z3_decl_kind.Z3_OP_UNINTERPRETED) {
            vars.add(expr);
        }else {
            for (let i = 0; i < child_count; i++) {
                console.log("Collecting child",i,"of",child_count,"for",expr,":" ,Z3.get_app_arg(ctx,app,i));
                const child = Z3.get_app_arg(ctx,app,i);
                if (child===expr) {
                    console.log("Skipping child",i,"of",child_count,"for",expr,":" ,Z3.get_app_arg(ctx,app,i));
                    continue;
                }
                collect(Z3.get_app_arg(ctx,app,i));
            }
        }

    }
    collect(expr);
    return vars;
  }





// Name extends string
class Spec{
    name: string;
    ctx: z3.Z3_context
    arity: number;
    inputs: z3.Z3_ast[];
    outputs: z3.Z3_ast[];
    phis: z3.Z3_ast[];
    preconds: z3.Z3_ast[];
    vars: Set<z3.Z3_ast>;

    constructor(
        name: string,
        phis: z3.Z3_ast[],
        outputs: z3.Z3_ast[],
        inputs: z3.Z3_ast[],
        preconds: z3.Z3_ast[] | null = null
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

        // this.ctx = phis[0].ctx; // Assuming ctx is an attribute of the first phi
        this.ctx = ctx;
        this.name = name;
        this.arity = inputs.length;
        this.inputs = inputs;
        this.outputs = outputs;
        this.phis = phis;
        this.preconds = preconds ? preconds : Array.from({ length: outputs.length }, () => Z3.mk_true(ctx));
        // union(vars(phi) for phi in phis)
        this.vars = phis.reduce((acc, phi) => new Set([...acc, ..._collect_vars(phi)]), new Set<z3.Z3_ast>());

        const allVars = [...outputs, ...inputs];
        if (new Set(allVars).size !== allVars.length) {
            throw new Error('Outputs and inputs must be unique');
        }
        if (![...this.vars].every(varExpr => allVars.includes(varExpr))) {
            throw new Error(`Phi must use only out and in variables: ${[...this.vars]} vs ${allVars}`);
        }

        for (const [pre, phi, _out] of this.preconds.map((pre, i) => [pre, this.phis[i], this.outputs[i]])) {
            if (![..._collect_vars(pre)].every(varExpr => this.inputs.includes(varExpr))) {
                throw new Error('Precondition must use input variables only');
            }
            if (![..._collect_vars(phi)].every(varExpr => allVars.includes(varExpr))) {
                throw new Error(`i-th spec must use only i-th out and input variables ${phi}`);
            }
        }
    }

    toString(): string {
        return this.name;
    }

    translate<N extends string>(ctx: z3.Z3_context): Spec {
        // const ins = this.inputs.map(x => x.translate(ctx));
        // const outs = this.outputs.map(x => x.translate(ctx));
        // const pres = this.preconds.map(x => x.translate(ctx));
        // const phis = this.phis.map(x => x.translate(ctx));
        const ins = this.inputs.map(x => Z3.translate(this.ctx,x,ctx));
        const outs = this.outputs.map(x => Z3.translate(this.ctx,x,ctx));
        const pres = this.preconds.map(x => Z3.translate(this.ctx,x,ctx));
        const phis = this.phis.map(x => Z3.translate(this.ctx,x,ctx));
        // const ins = this.inputs.map(x => x);
        // const outs = this.outputs.map(x => x);
        // const pres = this.preconds.map(x => x);
        // const phis = this.phis.map(x => x);
        return new Spec(this.name, phis, outs, ins, pres);
    }

    // Cached properties
    // could use https://stackoverflow.com/questions/74201358/whatss-the-best-way-to-cache-a-getter-without-decorators
    get outTypes(): z3.Z3_sort[] {
        return this.outputs.map(v => Z3.get_sort(this.ctx,v));
    }

    get inTypes(): z3.Z3_sort[] {
        return this.inputs.map(v => Z3.get_sort(this.ctx,v));
    }

    // get isTotal(): boolean {
    async isTotal(): Promise<boolean> {
        // const ctx = this.ctx;
        // const solver = new ctx.Solver();
        const solver = Z3.mk_solver(ctx);
        const spec = this.translate(ctx);
        // solver.add(Or(spec.preconds.map(p => Not(p))));
        // solver.add(ctx.Or(...spec.preconds.map(p => p.not())));
        Z3.solver_assert(ctx,solver,Z3.mk_or(ctx,spec.preconds));
        // return (await solver.check() === 'unsat');
        // Z3_L_FALSE
        return await Z3.solver_check(ctx,solver) === -1;
    }

    // get isDeterministic(): boolean {
    async isDeterministic(): Promise<boolean> {
        // const ctx = new Context();
        // const solver = new ctx.Solver();
        const solver = Z3.mk_solver(ctx);
        const spec = this.translate(ctx);
        // const ins = spec.inTypes.map(ty => ctx.FreshConst(ty));
        // const outs = spec.outTypes.map(ty => ctx.FreshConst(ty));
        const ins = spec.inTypes.map(ty => Z3.mk_fresh_const(ctx,"",ty));
        const outs = spec.outTypes.map(ty => Z3.mk_fresh_const(ctx,"",ty));
        const [, phis] = spec.instantiate(outs, ins);
        // solver.add(ctx.And(...spec.preconds));
        Z3.solver_assert(ctx,solver,Z3.mk_and(ctx,spec.preconds));
        for (const p of spec.phis) {
            // solver.add(p);
            Z3.solver_assert(ctx,solver,p);
        }
        for (const p of phis) {
            // solver.add(p as z3.Bool);
            Z3.solver_assert(ctx,solver,p);
        }
        // solver.add(ctx.And(...spec.inputs.map((a, i) => a === ins[i])));
        // solver.add(ctx.Or(...spec.outputs.map((a, i) => a !== outs[i])));
        Z3.solver_assert(ctx,solver,Z3.mk_and(ctx,spec.inputs.map((a, i) => Z3.mk_eq(ctx,a,ins[i]))));
        Z3.solver_assert(ctx,solver,Z3.mk_or(ctx,spec.outputs.map((a, i) => Z3.mk_not(ctx,Z3.mk_eq(ctx,a,outs[i])))));
        // return await solver.check() === 'unsat';
        return await Z3.solver_check(ctx,solver) === -1;
    }

    instantiate(outs: z3.Z3_ast[], ins: z3.Z3_ast[]): [z3.Z3_ast[], z3.Z3_ast[]] {
        const selfOuts = this.outputs;
        const selfIns = this.inputs;
        if (outs.length !== selfOuts.length || ins.length !== selfIns.length) {
            throw new Error('Invalid number of outputs or inputs');
        }
        if (!outs.every((x, i) => Z3.get_sort(this.ctx,x) === Z3.get_sort(this.ctx,selfOuts[i])) || !ins.every((x, i) => Z3.get_sort(this.ctx,x) === Z3.get_sort(this.ctx,selfIns[i]))) {
            throw new Error('Type mismatch');
        }
        // if (!outs.every((x, i) => x.ctx === selfOuts[i].ctx) || !ins.every((x, i) => x.ctx === selfIns[i].ctx)) {
        //     throw new Error('Context mismatch');
        // }
        const selfVars = [...selfOuts, ...selfIns];
        const vars = [...outs, ...ins];
        // const phis = this.phis.map(phi => ctx.substitute(phi, 
        //     ...selfVars.map((x, i) => [x, vars[i]] as [z3.Expr, z3.Expr])));
        const phis = this.phis.map(phi => Z3.substitute(this.ctx,phi, selfVars, vars));
        // const pres = this.preconds.map(p => ctx.substitute(p, 
        //     ...selfIns.map((x, i) => [x, ins[i]] as [z3.Expr, z3.Expr])));
        const pres = this.preconds.map(p => Z3.substitute(this.ctx,p, selfIns, ins));
        return [pres, phis];
    }
}

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

class Func extends Spec {
    precond: z3.Z3_ast;
    func: z3.Z3_ast;

    constructor(name: string, phi: z3.Z3_ast, precond: z3.Z3_ast = Z3.mk_true(ctx), inputs: z3.Z3_ast[] = []) {
        const inputVars = _collect_vars(phi);
        
        // If no inputs are specified, take identifiers in lexicographical order
        if (inputs.length === 0) {
            inputs = [...inputVars].sort((a, b) => String(a).localeCompare(String(b)));
        }

        // Check if precondition uses only variables that are in phi
        if (![..._collect_vars(precond)].every(varExpr => inputVars.has(varExpr))) {
            throw new Error('Precondition uses variables that are not in phi');
        }

        // const resType = phi.sort; // Assuming phi has a sort method
        const resType = Z3.get_sort(ctx,phi);

        // super(name, [ctx.Eq(ctx.FreshConst(resType), phi)], [ctx.FreshConst(resType)], inputs, [precond]);
        super(name, [Z3.mk_eq(ctx,Z3.mk_fresh_const(ctx,"",resType), phi)], [Z3.mk_fresh_const(ctx,"",resType)], inputs, [precond]);

        this.precond = precond;
        this.func = phi;
    }

    // Cached property
    // get isDeterministic(): boolean {
    async isDeterministic(): Promise<boolean> {
        return true;
    }

    translate<N extends string>(ctx: z3.Z3_context): Func {
        // const ins = this.inputs.map(i => i.translate(ctx));
        // return new Func(this.name, this.func.translate(ctx), this.precond.translate(ctx), ins);

        const ins = this.inputs.map(i => Z3.translate(this.ctx,i,ctx));
        return new Func(this.name, Z3.translate(this.ctx,this.func,ctx), Z3.translate(this.ctx,this.precond,ctx), ins);

        // const ins = this.inputs.map(i => i);
        // return new Func(this.name, this.func, this.precond, ins);
    }

    // Cached property
    get outType(): z3.Z3_sort {
        return this.outTypes[0];
    }

    // Check if the function is commutative
    // get isCommutative(): boolean {
    async isCommutative(): Promise<boolean> {
        // If the operator inputs have different sorts, it cannot be commutative
        // if (new Set(this.inputs.map(v => v.sort)).size > 1 || this.inputs.length > 3) {
        if (new Set(this.inputs.map(v => Z3.get_sort(ctx,v))).size > 1 || this.inputs.length > 3) {
            return false;
        }

        // const ctx = new Context();
        // const precond = this.precond.translate(ctx);
        // const func = this.func.translate(ctx);
        // const ins = this.inputs.map(x => x.translate(ctx));
        const precond = this.precond;
        const func = this.func;
        const ins = this.inputs.map(x => x);
        // const subst = (f: z3.Expr, i: z3.Expr[]) => ctx.substitute(f, ...ins.map((x, j) => [x, i[j]] as [z3.Expr, z3.Expr]));
        const subst = (f: z3.Z3_ast, i: z3.Z3_ast[]) => Z3.substitute(ctx,f, this.inputs, i);

        const fs = combine(permute(ins), 2).map(([a, b]) => {
            // return ctx.And(...[
            //     subst(precond, a) as z3.Bool, 
            //     subst(precond, b) as z3.Bool, 
            //     ctx.Not(ctx.Eq(subst(func, a), subst(func, b)))
            // ]);
            return Z3.mk_and(ctx,[
                subst(precond, a) as z3.Z3_ast, 
                subst(precond, b) as z3.Z3_ast, 
                Z3.mk_not(ctx,Z3.mk_eq(ctx,subst(func, a), subst(func, b)))
            ]);
        });

        // const solver = new ctx.Solver();
        // solver.add(ctx.Or(...fs));
        const solver = Z3.mk_solver(ctx);
        const fsOr = Z3.mk_or(ctx,fs);
        // return await solver.check() === 'unsat';
        Z3.solver_assert(ctx,solver,fsOr);
        return await Z3.solver_check(ctx,solver) === -1;
    }
}

type Op = any;
type Insns = [boolean, number][];
type Outputs = [boolean, number][];
type OutputMap = { [key: number]: string[] };
class Prg {
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

class EnumBase<T, U> {
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
class EnumSortEnum extends EnumBase<z3.Z3_func_decl, any> {
    sort: any; // Type of sort depends on the library being used

    constructor(name: string, items: any[], ctx: z3.Z3_context) {
        // Assuming EnumSort and BitVecSort are defined elsewhere
        // const [sort, cons] = ctx.EnumSort(name, items.map(i => i.toString()), ctx=ctx);
        // const [sort, cons, testers] 
        const {
          rv: sort,
          enum_consts: cons,
          enum_testers: testers
        } = Z3.mk_enumeration_sort(ctx,
          Z3.mk_string_symbol(ctx,name),
          items.map(i => i.toString()));
        super(items, cons);
        this.sort = sort;
    }

    getFromModelVal(val: z3.Z3_func_decl): any {
        return this.consToItem.get(val);
    }

    addRangeConstr(solver: any, variable: z3.Z3_ast): void {
        Z3.solver_assert(ctx,solver,
          Z3.mk_le(ctx, variable, 
            Z3.mk_int(ctx,this.cons.length-1, Z3.mk_int_sort(ctx))));
    }
}




let x = Z3.mk_const(ctx,Z3.mk_string_symbol(ctx,"x"),Z3.mk_int_sort(ctx));
let y = Z3.mk_const(ctx,Z3.mk_string_symbol(ctx,"y"),Z3.mk_int_sort(ctx));
let z = Z3.mk_const(ctx,Z3.mk_string_symbol(ctx,"z"),Z3.mk_int_sort(ctx));
// const x_plus_y = Z3.mk_add(ctx,[x,y]);
// const z_plus_xy = Z3.mk_add(ctx,[z,x_plus_y]);
// const z_plus_xy = Z3.mk_add(ctx,[z,x,y]);
const z_plus_xy = Z3.mk_add(ctx,[z,x,Z3.mk_numeral(ctx,"5",Z3.mk_int_sort(ctx))]);
// const a_plus_5 = Z3.mk_add(ctx,[x_plus_y,Z3.mk_int(ctx,5,Z3.mk_int_sort(ctx))]);

console.log("Collect vars");
console.log("plus: ",Array.from(_collect_vars(z_plus_xy)).map(x => Z3.ast_to_string(ctx,x)));
console.log("x: ",Array.from(_collect_vars(x)).map(x => Z3.ast_to_string(ctx,x)));
// y = Z3.mk_const(ctx,Z3.mk_string_symbol(ctx,"y"),Z3.mk_int_sort(ctx));
console.log("y: ",Array.from(_collect_vars(y)).map(x => Z3.ast_to_string(ctx,x)));
console.log("z: ",Array.from(_collect_vars(z)).map(x => Z3.ast_to_string(ctx,x)));
// console.log(Array.from(_collect_vars(x_plus_y)).map(x => Z3.ast_to_string(ctx,x)));
// console.log(Array.from(_collect_vars(a_plus_5)).map(x => Z3.ast_to_string(ctx,x)));
// console.log(Array.from(_collect_vars(x)).map(x => Z3.ast_to_string(ctx,x)));
// console.log(Array.from(_collect_vars(x)).map(x => x.toString()));


  
  // console.log('')
  // console.log('### running the high-level API')
  // // let { Context } = await window.z3Promise;
  // let { Solver, Int } = Context('main');
  // let solver = new Solver();
  // let x = Int.const('x');
  // solver.add(x.add(5).eq(9));
  // console.log(await solver.check());
  // console.log('x is', solver.model().get(x).toString());

  // console.log("Collect vars");
  // console.log(Array.from(_collect_vars(x.add(5).eq(9))).map(x => x.toString()));
  // const y = Int.const('y');
  // console.log(Array.from(_collect_vars(x.add(y).eq(9))).map(x => x.toString()));

})().catch(e => {
  console.error(e);
});










const root = ReactDOM.createRoot(
  document.getElementById('root') as HTMLElement
);
root.render(
  <React.StrictMode>
    <App />
  </React.StrictMode>
);

// If you want to start measuring performance in your app, pass a function
// to log results (for example: reportWebVitals(console.log))
// or send to an analytics endpoint. Learn more: https://bit.ly/CRA-vitals
reportWebVitals();
