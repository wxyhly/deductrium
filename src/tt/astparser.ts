import { TR } from "../lang.js";

export type AST = { type: string, name: string, nodes?: AST[], checked?: AST, err?: any };
export class ASTParser {
    keywords = [":=", "->", "~=", "===", "@ind_Sum", "ind_Sum", "@Sum", "Sum","@ind_S1","ind_S1","S1", "@ind_Prod", "ind_Prod", "@Prod", "Prod"];
    symChar = ".:,()PSLX~*+";
    ast: AST;
    cursor: number = 0;
    tokens: string[];
    token: string;
    stringify(ast: AST): string {
        if(!ast) return TR('表达式丢失');
        const nd = ast.nodes;
        if (ast.type === "->") {
            return `(${this.stringify(nd[0])}→${this.stringify(nd[1])})`;
        } if (ast.type === "===") {
            return `(${this.stringify(nd[0])}===${this.stringify(nd[1])})`;
        }
        if (ast.type === ":") {
            return `(${this.stringify(nd[0])} : ${this.stringify(nd[1])})`;
        }
        if (ast.type === ":=") {
            return `(${this.stringify(nd[0])} := ${this.stringify(nd[1])})`;
        }
        if (ast.type === "~") {
            return `(${this.stringify(nd[0])}~${this.stringify(nd[1])})`;
        }
        if (ast.type === "*") {
            return `(${this.stringify(nd[0])}∘${this.stringify(nd[1])})`;
        }
        if (ast.type === ",") {
            return `(${this.stringify(nd[0])},${this.stringify(nd[1])})`;
        }
        if (ast.type === "+") {
            return `(${this.stringify(nd[0])}+${this.stringify(nd[1])})`;
        }
        if (ast.type === "~=") {
            return `(${this.stringify(nd[0])}≃${this.stringify(nd[1])})`;
        }
        if (ast.type === "X") {
            return `(${this.stringify(nd[0])}×${this.stringify(nd[1])})`;
        }
        if (ast.type === "L") {
            return `(λ${ast.name}:${this.stringify(nd[0])}.${this.stringify(nd[1])})`;
        }
        if (ast.type === "P") {
            return `(Π${ast.name}:${this.stringify(nd[0])},${this.stringify(nd[1])})`;
        }
        if (ast.type === "S") {
            return `(Σ${ast.name}:${this.stringify(nd[0])},${this.stringify(nd[1])})`;
        }
        if (ast.type === "var") {
            return ast.name;
        }
        if (ast.type === "apply") {
            if(ast.nodes[0].name==="U"&&ast.nodes[1].name==="@0") return `U`;
            if(ast.nodes[0].name==="U") return `(${this.stringify(nd[0])}${this.stringify(nd[1])})`;
            return `(${this.stringify(nd[0])} ${this.stringify(nd[1])})`;
        }
    }
    parse(s: string): AST {
        this.cursor = 0;
        this.tokenise(s.replaceAll("Σ", "S").replaceAll("λ", "L").replaceAll("Π", "P").replaceAll("→", "->").replaceAll("×", "X"));
        this.nextSym();
        const ret = this.type();
        if (this.tokens.length !== this.cursor - 1) {
            if (this.token === ":" || this.token === "===" || this.token === ":=") {
                const token = this.token;
                this.nextSym();
                const postfix = this.type();
                if (!postfix) throw TR("不完整的表达式");
                if (this.tokens.length !== this.cursor - 1) {
                    if (token === ":=" && this.token === ":") {
                        // def := expr : type
                        this.nextSym();
                        const type = this.type();
                        if (!type) throw TR("不完整的表达式");
                        return {
                            type: token, name: "", nodes: [ret, {
                                type: ":", name: "", nodes: [postfix, type]
                            }]
                        };
                    }
                    throw TR("未知的语法错误");
                }
                return { type: token, name: "", nodes: [ret, postfix] };
            } else {
                throw TR("未知的语法错误");
            }
        }
        return ret;
    }
    private tokenise(s: string) {
        for (let i = 0; i < this.keywords.length; i++) {
            s = s.replace(new RegExp(this.keywords[i], "g"), " #keyword" + i + " ");
        }
        let word = "";
        const arr: string[] = [];
        for (let i = 0; i < s.length; i++) {
            const c = s[i];
            if (this.symChar.includes(c)) {
                if (word !== "") {
                    arr.push(word); word = "";
                }
                arr.push(c);
                continue;
            }
            if (c === " ") {
                if (word !== "") {
                    arr.push(word); word = "";
                }
                continue;
            }
            word += c;
        }
        if (word !== "") {
            arr.push(word);
        }
        this.tokens = arr.map(token => token.startsWith("#keyword") ? this.keywords[token.slice(8)] : token.replace("：", ":"));
    }
    private prevToken(index: number) {
        return this.tokens[this.cursor - index - 1];
    }
    private nextSym() {
        this.token = this.tokens[this.cursor++];
    }
    private moveCursor(cursor: number) {
        this.cursor = cursor;
        this.token = this.tokens[this.cursor - 1];
    }
    private typeTerm3(): AST {
        let val: AST;
        if (this.acceptSym("(")) {
            val = this.type();
            while (this.token === ",") {
                this.nextSym();
                val = {
                    type: ",", name: "", nodes: [
                        val, this.type()
                    ]
                }
            }
            this.expectSym(")");
        } else if (this.acceptSym("L")) {
            this.expectVar();
            const param = this.prevToken(1);
            this.expectSym(":");
            const paramType = this.type();
            if (!(this.acceptSym(".") || this.acceptSym(","))) throw TR("Lambda未匹配“.”号");
            const fnbody = this.type();
            val = { type: "L", name: param, nodes: [paramType, fnbody] };
        } else if (this.acceptSym("P")) {
            this.expectVar();
            const param = this.prevToken(1);
            this.expectSym(":");
            const paramType = this.type();
            if (!(this.acceptSym(".") || this.acceptSym(","))) throw TR("Pi未匹配“,”号");
            const fnbody = this.type();
            val = { type: "P", name: param, nodes: [paramType, fnbody] };
        } else if (this.acceptSym("S")) {
            this.expectVar();
            const param = this.prevToken(1);
            this.expectSym(":");
            const paramType = this.type();
            this.expectSym(",");
            const fnbody = this.type();
            val = { type: "S", name: param, nodes: [paramType, fnbody] };
        } else if (this.acceptVar()) {
            const name = this.prevToken(1);
            const isapply = this.prevToken(0);
            if (name === "U" && isapply !== "(") {
                val = {
                    type: "apply", name: "", nodes: [
                        { type: "var", name: "U" }, { type: "var", name: "@0" }
                    ]
                };
            } else if (name.startsWith("U") && name !== "U@" && isapply !== "(") {
                val = {
                    type: "apply", name: "", nodes: [
                        { type: "var", name: "U" },
                        { type: "var", name: ("0123456789".includes(name[1]) ? "@" : "") + name.slice(1) }
                    ]
                };
            } else {
                val = { type: "var", name: this.prevToken(1) };
            }
        }
        return val;
    }
    private typeTerm2() {
        let val = this.typeTerm3();
        while (this.token === "*") {
            const token = this.token;
            this.nextSym();
            val = { type: token, name: "", nodes: [val, this.typeTerm3()] };
        }
        return val;
    }
    private typeTerm1() {
        let val = this.typeTerm2();
        while (this.token === "X" || this.token === "~" || this.token === "~=") {
            const token = this.token;
            this.nextSym();
            val = { type: token, name: "", nodes: [val, this.typeTerm2()] };
        }
        return val;
    }
    private typeTerm0() {
        let val = this.typeTerm1();
        while (this.token === "+") {
            const token = this.token;
            this.nextSym();
            val = { type: token, name: "", nodes: [val, this.typeTerm1()] };
        }
        return val;
    }
    private typeTerm() {
        const arr = [this.typeTerm0()];
        while (this.token === "->") {
            this.nextSym();
            arr.push(this.typeTerm0());
        }
        let val = arr.pop();
        let val1: AST;
        while (val1 = arr.pop()) {
            val = { type: "->", name: "", nodes: [val1, val] };
        }
        return val;
    }
    private type(): AST {
        let val = this.typeTerm();
        while (this.token && this.token !== ")" && this.token !== ":" && this.token !== "." && this.token !== "," && this.token !== ":=" && this.token !== "===") {
            val = { type: "apply", name: "", nodes: [val, this.typeTerm()] }
        }
        if (!val) throw TR("表达式不完整");
        return val;
    }


    private acceptVar() {
        if (!this.symChar.includes(this.token) || this.token.length > 1) {
            if (!this.token) return false; //eof
            this.nextSym();
            return true;
        }
        return false;
    }
    private expectVar() {
        if (this.acceptVar()) return true;
        throw TR(`语法错误：未找到变量`);
    }
    private acceptSym(s: string) {
        if (s === this.token) {
            this.nextSym();
            return true;
        }
        return false;
    }
    private expectSym(s: string) {
        if (this.acceptSym(s)) return true;
        throw TR(`语法错误：未找到符号"`)+s+`"`;
    }
}