import { TR } from "../lang.js";
export class ASTParser {
    keywords = ["E!", "⊢M", "<>", "Union", "{}", "Equiv"];
    symChar = "VEMUI()@~^<>|&=,;:[]!⊢+-*/{}";
    ast;
    cursor = 0;
    tokens;
    token;
    stringifyTight(ast, bracket = false) {
        const nd = ast.nodes;
        if (ast.type === "fn") {
            if (ast.name === "{")
                return `{${nd.map(n => this.stringify(n)).join(",")}}`;
            return `${ast.name}(${nd.map(n => this.stringifyTight(n)).join(",")})`;
        }
        if (ast.type === "replvar") {
            return ast.name;
        }
        if (ast.type === "meta") {
            const c = `${nd[0].nodes.map(n => this.stringifyTight(n, ast.name === "⊢M")).join(",")}${ast.name}${nd[1].nodes.map(n => this.stringifyTight(n, ast.name === "⊢M")).join(",")}`;
            return bracket ? `(${c})` : c;
        }
        switch (ast.name) {
            case "~":
            case "!": return `${ast.name}${this.stringifyTight(nd[0], true)}`;
            case "V":
            case "E":
            case "E!": return `(${ast.name}${this.stringifyTight(nd[0])}:${this.stringifyTight(nd[1], true)})`;
            default:
                const sym = ast.name;
                const c = `${this.stringifyTight(nd[0], true)}${sym}${this.stringifyTight(nd[1], true)}`;
                return bracket ? `(${c})` : c;
        }
    }
    stringify(ast) {
        const nd = ast.nodes;
        if (ast.type === "fn") {
            if (ast.name === "{")
                return `{${nd.map(n => this.stringify(n)).join(", ")}}`;
            return `${ast.name}(${nd.map(n => this.stringify(n)).join(", ")})`;
        }
        if (ast.type === "replvar") {
            return ast.name;
        }
        if (ast.type === "meta") {
            return `(${nd[0].nodes.map(n => this.stringify(n)).join(", ")} ${ast.name} ${nd[1].nodes.map(n => this.stringify(n)).join(", ")})`;
        }
        switch (ast.name) {
            case "~":
            case "!": return `${ast.name}${this.stringify(nd[0])}`;
            case "V":
            case "E":
            case "E!": return `(${ast.name}${this.stringify(nd[0])}: ${this.stringify(nd[1])})`;
            default:
                return `(${this.stringify(nd[0])} ${ast.name} ${this.stringify(nd[1])})`;
        }
    }
    parse(s) {
        this.cursor = 0;
        this.tokenise(s.replaceAll("∀", "V").replaceAll("∃", "E").replaceAll("∈", "@").replaceAll("¬", "~")
            .replaceAll("→", ">").replaceAll("↔", "<>").replaceAll("⊂", "<").replaceAll("∪", "U").replaceAll("∩", "I")
            .replaceAll("∧", "&").replaceAll("∨", "|").replaceAll("ω", "omega"));
        this.nextSym();
        return this.meta();
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
        throw TR(`语法错误：未找到变量`);
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
        throw TR(`语法错误：未找到符号`) + `"${s}"`;
    }
    itemTerm() {
        if (this.acceptVar()) {
            if (this.acceptSym("(")) {
                const fnName = this.prevToken(2);
                const nodes = [this.meta()];
                while (this.token === ",") {
                    this.nextSym();
                    nodes.push(this.meta());
                }
                this.expectSym(")");
                return { type: "fn", name: fnName, nodes };
            }
            else {
                return { type: "replvar", name: this.prevToken(1) };
            }
        }
        else if (this.acceptSym("(")) {
            let val = this.meta();
            this.expectSym(")");
            return val;
        }
        else if (this.acceptSym("{")) {
            const nodes = [this.meta()];
            while (this.token === ",") {
                this.nextSym();
                nodes.push(this.meta());
            }
            this.expectSym("}");
            return { type: "fn", name: "{", nodes };
        }
        else if (this.acceptSym("-")) {
            // -n in #rp(.,.,., here)
            if (this.acceptVar()) {
                return { type: "replvar", name: "-" + this.prevToken(1) };
            }
            else {
                throw TR("语法错误");
            }
        }
        else {
            throw TR("语法错误");
        }
    }
    boolTerm6() {
        let val = this.itemTerm();
        while (this.token === "*" || this.token === "/" || this.token === "I" || this.token?.match(/^\$\$.+/)) {
            const name = this.token;
            this.nextSym();
            let val2 = this.itemTerm();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    boolTerm5() {
        let val = this.boolTerm6();
        while (this.token === "+" || this.token === "U" || this.token === "-") {
            const name = this.token;
            this.nextSym();
            let val2 = this.boolTerm6();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    boolTerm4() {
        let val = this.boolTerm5();
        while (this.token === "@" || this.token === "=" || this.token === "<" || this.token?.match(/^\$\$.+/)) {
            const name = this.token;
            this.nextSym();
            let val2 = this.boolTerm5();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    boundedVar() {
        if (this.token.match(/^#?#nf$/)) {
            this.nextSym();
            this.expectSym("(");
            const fnName = this.prevToken(2);
            const nodes = [this.meta()];
            while (this.token === ",") {
                this.nextSym();
                nodes.push(this.meta());
            }
            this.expectSym(")");
            return { type: "fn", name: fnName, nodes };
        }
        else {
            this.expectVar();
            return { type: "replvar", name: this.prevToken(1) };
        }
    }
    boolTerm3() {
        if (this.token === "V" || this.token === "E" || this.token === "E!") {
            const name = this.token;
            this.nextSym();
            // this.expectVar();
            return {
                type: "sym", name,
                nodes: [
                    this.boundedVar(),
                    (this.acceptSym(":"), this.boolTerm3()) // ":" is optional
                ]
            };
        }
        else if (this.token === "~") {
            this.nextSym();
            return { type: "sym", name: "~", nodes: [this.boolTerm3()] };
        }
        else if (this.token === "!") {
            this.nextSym();
            return { type: "sym", name: "!", nodes: [this.boolTerm3()] };
        }
        else {
            return this.boolTerm4();
        }
    }
    boolTerm2() {
        let val = this.boolTerm3();
        while (this.token === "&" || this.token === "^") {
            const name = this.token;
            this.nextSym();
            let val2 = this.boolTerm3();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    boolTerm1() {
        let val = this.boolTerm2();
        while (this.token === "|") {
            this.nextSym();
            let val2 = this.boolTerm2();
            val = { type: "sym", name: "|", nodes: [val, val2] };
        }
        return val;
    }
    bool() {
        let val = this.boolTerm1();
        while (this.token === ">" || this.token === "<>") {
            const name = this.token;
            this.nextSym();
            let val2 = this.boolTerm1();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    meta() {
        let conditions = [];
        let rollBackCursor;
        if (this.token !== "⊢M" && this.token !== "⊢" && this.token !== "⊧") {
            // parse meta-condition
            conditions.push(this.bool());
            rollBackCursor = this.cursor;
            while (this.token === ",") {
                this.nextSym();
                conditions.push(this.bool());
            }
        }
        const sym = this.token;
        if (this.token !== "⊢M" && this.token !== "⊢" && this.token !== "⊧") {
            this.moveCursor(rollBackCursor); // rollback to first ","
            return conditions[0]; // not meta, just bool
        }
        this.nextSym();
        let conclusions = [];
        conclusions.push(this.meta());
        while (this.token === ",") {
            this.nextSym();
            conclusions.push(this.meta());
        }
        return {
            type: "meta", name: sym, nodes: [
                { type: "fn", name: "#array", nodes: conditions },
                { type: "fn", name: "#array", nodes: conclusions },
            ]
        };
    }
}
//# sourceMappingURL=astparser.js.map