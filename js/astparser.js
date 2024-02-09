export class ASTParser {
    keywords = ["E!", "⊢M", "<>"];
    symChar = "VEMU()@~^>|&=,;:[]!⊢+";
    ast;
    cursor = 0;
    tokens;
    token;
    parse(s) {
        this.cursor = 0;
        this.tokenise(s);
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
        if (!this.symChar.includes(this.token)) {
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
        else {
            throw "语法错误";
        }
    }
    boolTerm5() {
        let val = this.itemTerm();
        while (this.token === "+" || this.token === "-" || this.token?.match(/^\$\$.+/)) {
            const name = this.token;
            this.nextSym();
            let val2 = this.itemTerm();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    boolTerm4() {
        let val = this.boolTerm5();
        while (this.token === "@" || this.token === "=" || this.token?.match(/^\$\$.+/)) {
            const name = this.token;
            this.nextSym();
            let val2 = this.boolTerm5();
            val = { type: "sym", name, nodes: [val, val2] };
        }
        return val;
    }
    boolTerm3() {
        if (this.token === "~") {
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
        if (this.token === "V" || this.token === "E" || this.token === "E!") {
            const name = this.token;
            this.nextSym();
            this.expectVar();
            return {
                type: "sym", name,
                nodes: [
                    { type: "replvar", name: this.prevToken(1) },
                    (this.acceptSym(":"), this.bool()) // ":" is optional
                ]
            };
        }
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
        if (this.token !== "⊢M" && this.token !== "⊢") {
            // parse meta-condition
            conditions.push(this.bool());
            rollBackCursor = this.cursor;
            while (this.token === ",") {
                this.nextSym();
                conditions.push(this.bool());
            }
        }
        const sym = this.token;
        if (this.token !== "⊢M" && this.token !== "⊢") {
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