import { TR } from "../lang.js";
export class RuleParser {
    symChar = ":,";
    firstChar = "vuc<>#et";
    startNotAllowed = "ad#$";
    tokenise(s) {
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
            word += c;
        }
        if (word !== "") {
            arr.push(word);
        }
        let changed = true;
        while (changed) {
            changed = false;
            for (let i = 0; i < arr.length; i++) {
                if (arr[i].length > 1 && this.firstChar.includes(arr[i][0])) {
                    // split arr[i] into arr[i][0] and arr[i].slice(1)
                    const firstChar = arr[i][0];
                    const rest = arr[i].slice(1);
                    arr.splice(i, 1, firstChar, rest);
                    i += 1;
                    changed = true;
                }
            }
        }
        return arr;
    }
    mergeMTokens(tokens) {
        const result = [];
        let i = 0;
        while (i < tokens.length) {
            if (tokens[i] === "#") {
                let merged = "#";
                i++;
                while (i < tokens.length && tokens[i] !== ",") {
                    merged += tokens[i];
                    i++;
                }
                if (i < tokens.length && tokens[i] === ",") {
                    result.push(merged);
                    i++;
                }
            }
            else {
                if (tokens[i] !== ",")
                    result.push(tokens[i]);
                i++;
            }
        }
        return result;
    }
    parse(s) {
        const arr = this.tokenise(s);
        this.tokens = this.mergeMTokens(arr);
        if (arr.length === 0)
            return;
        this.pos = 0;
        const tree = this.nextRule();
        return tree;
    }
    stringify(tree) {
        if (tree.length === 1)
            return tree[0];
        if (tree[0] === ":" || tree[0][0] === "#") {
            return tree[0] + (tree[0][0] === "#" ? "," : "") + tree.slice(1).map(e => this.stringify(e)).join(",");
        }
        return tree.map(e => this.stringify(e)).join("");
    }
    tokens = [];
    pos = 0;
    nextToken() {
        if (this.pos < this.tokens.length) {
            return this.tokens[this.pos++];
        }
    }
    nextRule() {
        const token = this.nextToken();
        if (!token)
            throw TR("意外的规则名称表达式");
        if (token === ":") {
            return [":", this.nextRule(), this.nextRule()];
        }
        if (token === "#") {
            // todo
            return ["#", this.nextRule(), this.nextRule()];
        }
        if (token.length === 1 && this.firstChar.includes(token)) {
            return [token, this.nextRule()];
        }
        return [token];
    }
}
//# sourceMappingURL=metarule.js.map