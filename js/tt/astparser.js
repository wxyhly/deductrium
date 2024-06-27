export class ASTParser {
    keywords = [":=", "->", "~="];
    symChar = ".:,()PSLX~*";
    ast;
    cursor = 0;
    tokens;
    token;
    stringify(ast) {
        const nd = ast.nodes;
        if (ast.type === "->") {
            return `(${this.stringify(nd[0])}→${this.stringify(nd[1])})`;
        }
        if (ast.type === "~") {
            return `(${this.stringify(nd[0])}~${this.stringify(nd[1])})`;
        }
        if (ast.type === "*") {
            return `(${this.stringify(nd[0])}∘${this.stringify(nd[1])})`;
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
            return `(${this.stringify(nd[0])} ${this.stringify(nd[1])})`;
        }
    }
    parse(s) {
        this.cursor = 0;
        this.tokenise(s.replaceAll("Σ", "S").replaceAll("λ", "L").replaceAll("Π", "P").replaceAll("→", "->"));
        this.nextSym();
        const ret = this.type();
        if (this.tokens.length !== this.cursor - 1) {
            if (this.token === ":" || this.token === ":=") {
                const token = this.token;
                this.nextSym();
                const postfix = this.type();
                if (!postfix)
                    throw "不完整的表达式";
                if (this.tokens.length !== this.cursor - 1) {
                    throw "未知的语法错误";
                }
                return { type: token, name: "", nodes: [ret, postfix] };
            }
            else {
                throw "未知的语法错误";
            }
        }
        return ret;
    }
    tokenise(s) {
        for (let i = 0; i < this.keywords.length; i++) {
            s = s.replace(new RegExp(this.keywords[i], "g"), " #keyword" + i + " ");
        }
        let word = "";
        const arr = [];
        for (let i = 0; i < s.length; i++) {
            const c = s[i];
            if (this.symChar.includes(c)) {
                if (word !== "") {
                    arr.push(word);
                    word = "";
                }
                arr.push(c);
                continue;
            }
            if (c === " ") {
                if (word !== "") {
                    arr.push(word);
                    word = "";
                }
                continue;
            }
            word += c;
        }
        if (word !== "") {
            arr.push(word);
        }
        this.tokens = arr.map(token => token.startsWith("#keyword") ? this.keywords[token.slice(8)] : token);
    }
    prevToken(index) {
        return this.tokens[this.cursor - index - 1];
    }
    nextSym() {
        this.token = this.tokens[this.cursor++];
    }
    moveCursor(cursor) {
        this.cursor = cursor;
        this.token = this.tokens[this.cursor - 1];
    }
    typeTerm3() {
        let val;
        if (this.acceptSym("(")) {
            val = this.type();
            while (this.token === ",") {
                this.nextSym();
                val = {
                    type: ",", name: "", nodes: [
                        val, this.type()
                    ]
                };
            }
            this.expectSym(")");
        }
        else if (this.acceptSym("L")) {
            this.expectVar();
            const param = this.prevToken(1);
            this.expectSym(":");
            const paramType = this.type();
            this.expectSym(".");
            const fnbody = this.type();
            val = { type: "L", name: param, nodes: [paramType, fnbody] };
        }
        else if (this.acceptSym("P")) {
            this.expectVar();
            const param = this.prevToken(1);
            this.expectSym(":");
            const paramType = this.type();
            this.expectSym(",");
            const fnbody = this.type();
            val = { type: "P", name: param, nodes: [paramType, fnbody] };
        }
        else if (this.acceptSym("S")) {
            this.expectVar();
            const param = this.prevToken(1);
            this.expectSym(":");
            const paramType = this.type();
            this.expectSym(",");
            const fnbody = this.type();
            val = { type: "S", name: param, nodes: [paramType, fnbody] };
        }
        else if (this.acceptVar()) {
            const name = this.prevToken(1);
            if (name.startsWith("U") && name != "Ulvl") {
                val = {
                    type: "apply", name: "U", nodes: [
                        { type: "var", name: "U" },
                        { type: "var", name: name.slice(1) }
                    ]
                };
            }
            else {
                val = { type: "var", name: this.prevToken(1) };
            }
        }
        return val;
    }
    typeTerm2() {
        let val = this.typeTerm3();
        while (this.token === "*") {
            const token = this.token;
            this.nextSym();
            val = { type: token, name: "", nodes: [val, this.typeTerm3()] };
        }
        return val;
    }
    typeTerm1() {
        let val = this.typeTerm2();
        while (this.token === "X" || this.token === "~" || this.token === "~=") {
            const token = this.token;
            this.nextSym();
            val = { type: token, name: "", nodes: [val, this.typeTerm2()] };
        }
        return val;
    }
    typeTerm() {
        const arr = [this.typeTerm1()];
        while (this.token === "->") {
            this.nextSym();
            arr.push(this.typeTerm1());
        }
        let val = arr.pop();
        let val1;
        while (val1 = arr.pop()) {
            val = { type: "->", name: "", nodes: [val1, val] };
        }
        return val;
    }
    type() {
        let val = this.typeTerm();
        while (this.token && this.token !== ")" && this.token !== ":" && this.token !== "." && this.token !== "," && this.token !== ":=") {
            val = { type: "apply", name: "", nodes: [val, this.typeTerm()] };
        }
        if (!val)
            throw "表达式不完整";
        return val;
    }
    acceptVar() {
        if (!this.symChar.includes(this.token) || this.token.length > 1) {
            if (!this.token)
                return false; //eof
            this.nextSym();
            return true;
        }
        return false;
    }
    expectVar() {
        if (this.acceptVar())
            return true;
        throw `语法错误：未找到变量`;
    }
    acceptSym(s) {
        if (s === this.token) {
            this.nextSym();
            return true;
        }
        return false;
    }
    expectSym(s) {
        if (this.acceptSym(s))
            return true;
        throw `语法错误：未找到符号"${s}"`;
    }
}
//# sourceMappingURL=astparser.js.map