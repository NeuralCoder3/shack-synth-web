// AST types
interface PrimAST {
    type: string;
}

export interface BinOp extends PrimAST {
    type: "BinOp";
    op: "+" | "-" | "*" | "/";
    left: AST;
    right: AST;
}

export interface Num extends PrimAST {
    type: "Num";
    value: number;
}

export interface Var extends PrimAST {
    type: "Var";
    value: string;
}

export type AST = BinOp | Num | Var;

export function collect_vars(ast: AST): string[] {
    if (ast.type === "Var") {
        return [ast.value];
    } else if (ast.type === "BinOp") {
        return collect_vars(ast.left).concat(collect_vars(ast.right));
    } else {
        return [];
    }
}