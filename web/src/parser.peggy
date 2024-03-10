// Simple Arithmetics Grammar
// ==========================
//
// Accepts expressions like "2 * (3 + 4)" and computes their value.

// import {BinOp} from 'parser_interface'

{
    // console.log("Simple Arithmetics Grammar");


    function BinOp(op: "+" | "-" | "*" | "/", left: AST, right: AST): BinOp {
        return { type: "BinOp", op, left, right };
    }

    function Num(value: number): Num {
        return { type: "Num", value };
    }

    function Var(value: string): Var {
        return { type: "Var", value };
    }

}


Expression
  = head:Term tail:(_ ("+" / "-") _ Term)* {
      return tail.reduce(function(result, element) {
        if (element[1] === "+") { return BinOp("+", result, element[3]); }
        if (element[1] === "-") { return BinOp("-", result, element[3]); }
      }, head);
    }

Term
  = head:Factor tail:(_ ("*" / "/") _ Factor)* {
      return tail.reduce(function(result, element) {
        if (element[1] === "*") { return BinOp("*", result, element[3]); }
        if (element[1] === "/") { return BinOp("/", result, element[3]); }
      }, head);
    }

Factor
  = "(" _ expr:Expression _ ")" { return expr; }
  / Integer
  / Identifier

Integer "integer"
  = _ [0-9]+ { return Num(parseInt(text(), 10)); }

Identifier "identifier"
  = _ [a-zA-Z]+ { return Var(text()); }

_ "whitespace"
  = [ \t\n\r]*