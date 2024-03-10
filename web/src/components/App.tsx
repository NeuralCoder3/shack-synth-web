import React, { useState } from 'react';
// import logo from './logo.svg';
import './App.css';
import FunctionLibrary from './FunctionLibrary';
import { Function } from './interfaces';
import FunctionComponent from './FunctionComponent';

import '../parser';
import { parse } from '../parser';
import { AST } from '../parser_interface';
import * as z3 from 'z3-solver';
import * as synth from '../z3/highlevel';

const parse_typed = (s: string) => {
  const parsed : AST = parse(s);
  return parsed;
}


function astToZ3(ast: AST) {
  const var_map: { [key: string]: z3.Expr } = {};
  const ctx = synth.ctx;
  const get_var = (name: string, type:z3.Sort) => {
    if (var_map[name] === undefined) {
      // var_map[name] = ctx.Const(name, type);
      var_map[name] = ctx.Int.const(name);
    }
    return var_map[name];
  };
  function translate(ast: AST): z3.Arith {
    if (ast.type === "Num") {
      return ctx.Int.val(ast.value);
    }
    if (ast.type === "Var") {
      return get_var(ast.value, ctx.Int.sort()) as z3.Arith;
    }
    if (ast.type === "BinOp") {
      const left = translate(ast.left);
      const right = translate(ast.right);
      switch (ast.op) {
        case "+":
          return left.add(right);
        case "-":
          return left.sub(right);
        case "*":
          return left.mul(right);
        case "/":
          return left.div(right);
      }
    }
    throw new Error("Unknown AST type");
  }
  return translate(ast);
}



function App() {
  const [functions, setFunctions] = useState<Function[]>([
    // { name: 'Function 1', formula: 'x + y' },
    { name: 'mul', formula: 'x * y' },
  ]);

  const handleFunctionChange = (newFunctions: Function[]) => {
    setFunctions(newFunctions);
  };

  const [mainFunction, setMainFunction] = useState<Function>({ name: 'Goal', formula: 'x + x' });

  const [result, setResult] = useState<string>('');

  const solve = async () => {
    console.log('Solve');
    const ast = parse_typed(mainFunction.formula);
    console.log(ast);
    const z3_ast = astToZ3(ast);
    console.log(z3_ast.sexpr());

    const spec = new synth.Func(mainFunction.name, z3_ast);

    const z3_funcs = functions.map(({ name, formula }) => {
      const ast = parse_typed(formula);
      const z3_ast = astToZ3(ast);
      return new synth.Func(name, z3_ast);
    });

    const [prg,stats] = await synth.synth(spec, z3_funcs, [steps]);
    console.log(prg);
    setResult(String(prg));
  };

  const [steps, setSteps] = useState<number>(1);

  return (
    <div>
      <h1>Function Library</h1>
      <FunctionLibrary
        functions={functions}
        onAdd={() => handleFunctionChange([...functions, { name: '', formula: '' }])}
        onChange={handleFunctionChange}
      />
      <h1>Main Function</h1>
      <FunctionComponent
        func={mainFunction}
        onChange={setMainFunction}
        onRemove={null}
      />
      <h1>Parameters</h1>
      <div>
      <label>
        Steps:
        <input type="number" value={steps} onChange={(e) => setSteps(Number(e.target.value))} />
      </label>
      <br />
      <button onClick={solve}>Solve</button>
      </div>
      {
        result && (
          <div>
            <h1>Result</h1>
            <pre>{result}</pre>
          </div>
        )
      }
    </div>
    // <div className="App">
    //   <header className="App-header">
    //     {/* <p>
    //       Edit <code>src/index.tsx</code> and save to reload.
    //       Check the console for the output of the Z3 solver.
    //     </p> */}
    //   </header>
    // </div>
  );
}

export default App;
