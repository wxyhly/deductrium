type RuleTree = (string | RuleTree)[];
export class RuleParser {
    symChar = ":,";
    firstChar = "vuc<>met";
    startNotAllowed = "ad#$";
    private tokenise(s: string) {
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
            word += c;
        }
        if (word !== "") {
            arr.push(word);
        }
        let changed = true;
        while (changed) {
            changed = false;
            for (let i = 0; i < arr.length - 1; i++) {
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
    private mergeMTokens(tokens: string[]): string[] {
        const result: string[] = [];
        let i = 0;
        while (i < tokens.length) {
            if (tokens[i] === "m") {
                let merged = "m";
                i++;
                while (i < tokens.length && tokens[i] !== ",") {
                    merged += tokens[i];
                    i++;
                }
                if (i < tokens.length && tokens[i] === ",") {
                    result.push(merged);
                    i++;
                }
            } else {
                if (tokens[i] !== ",") result.push(tokens[i]);
                i++;
            }
        }
        return result;
    }
    parse(s: string): RuleTree {
        const arr = this.tokenise(s);
        this.tokens = this.mergeMTokens(arr);
        if (arr.length === 0) return;
        return this.nextRule();
    }
    private tokens: string[] = [];
    private pos = 0;
    private nextToken() {
        if (this.pos < this.tokens.length) {
            return this.tokens[this.pos++];
        }
    }
    private nextRule(): RuleTree {
        const token = this.nextToken();
        if (!token) throw "Unexpected end of input";
        if (token === ":") {
            return [":", this.nextRule(), this.nextRule()];
        }
        if (token === "m") {

            return ["m", this.nextRule(), this.nextRule()];
        }
        if (token.length === 1 && this.firstChar.includes(token)) {
            return [token, this.nextRule()];
        }
        return [token];
    }
}