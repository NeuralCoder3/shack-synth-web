import React from 'react';
import ReactDOM from 'react-dom/client';
import './index.css';
import App from './App';
import reportWebVitals from './reportWebVitals';



import * as z3 from 'z3-solver';
console.log("HI2");
declare global {
  interface Window { z3Promise: ReturnType<typeof z3.init>; }
}
window.z3Promise = z3.init();
(async () => {
  console.log('### running the low-level API')
  let { Z3 } = await window.z3Promise;
  let config = Z3.mk_config();
  let ctx = Z3.mk_context_rc(config);
  Z3.del_config(config);
  let command = `
    (declare-const a Int)
    (declare-fun f (Int Bool) Int)
    (assert (< a 10))
    (assert (< (f a true) 100))
    (check-sat)
    (get-model)
  `;
  console.log(await Z3.eval_smtlib2_string(ctx, command));
  Z3.del_context(ctx);


  
  console.log('')
  console.log('### running the high-level API')
  let { Context } = await window.z3Promise;
  let { Solver, Int } = Context('main');
  let solver = new Solver();
  let x = Int.const('x');
  solver.add(x.add(5).eq(9));
  console.log(await solver.check());
  console.log('x is', solver.model().get(x).toString());


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
