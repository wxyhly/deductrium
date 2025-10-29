import { TR } from "../lang.js";
import { AssertionSystem } from "./assertion.js";
import { AST, ASTMgr, ReplvarMatchTable } from "./astmgr.js";
import { ASTParser } from "./astparser.js";

export type RuleTree = [string, ...RuleTree[]] | [string];
export class RuleParser {
    symChar = ":,";
    firstChar = "vuc<>#e";
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
    private mergeMTokens(tokens: string[]): string[] {
        const result: string[] = [];
        let i = 0;
        while (i < tokens.length) {
            if (tokens[i] === "#") {
                let merged = "#";
                i++;
                while (i < tokens.length && tokens[i] !== "," && tokens[i] !== ":") {
                    merged += tokens[i];
                    i++;
                }
                if ((i < tokens.length && (tokens[i] === "," || tokens[i] === ":")) || i === tokens.length) {
                    result.push(merged);
                    if (tokens[i] === ":") result.push(":");
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
        this.pos = 0;
        const tree = this.nextRule();
        return tree;
    }
    stringify(tree: RuleTree): string {
        if (tree.length === 1) return tree[0] as string;
        if (tree[0][0] === "#") {
            return (tree[0] as string) + "," + tree.slice(1).map(e => this.stringify(e as RuleTree)).join(",");
        }
        if (tree[0] === ":") {
            return tree.slice(1).map((e, i) => (tree.length - 2 === i ? "," : ":") + this.stringify(e as RuleTree)).join("");
        }
        return tree.map(e => this.stringify(e as RuleTree)).join("");
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
        if (!token) throw TR("意外的规则名称表达式");
        if (token === ":") {
            const params: [string, ...RuleTree[]] = [":"];
            while (true) {
                params.push(this.nextRule());
                const sep = this.nextToken();
                if (sep !== ":") {
                    this.pos--;
                    params.push(this.nextRule());
                    break;
                }
            }
            return params;
        }
        if (token === "#") {
            return ["#"];
            // todo
            // return ["#", this.nextRule(), this.nextRule()];
        }
        if (token.length === 1 && this.firstChar.includes(token)) {
            return [token, this.nextRule()];
        }
        return [token];
    }
    replaceNameByName(r: RuleTree, src: string, dst: string) {
        if (r[0] === src && r.length === 1) {
            r[0] = dst; return;
        }
        for (const sub of r.slice(1)) {
            this.replaceNameByName(sub as RuleTree, src, dst);
        }
    }
}

const assert = new AssertionSystem;
const astmgr = new ASTMgr();
const parser = new ASTParser();
export class ConstrainSolver {
    dbg(matchTable: ReplvarMatchTable, constrains: [AST, AST, boolean][] = [], assertions: [AST, boolean][] = []) {
        console.log("====================");
        console.log("Constrains:");
        for (const [l, r] of constrains) {
            console.log(`${parser.stringify(l)}  :==:  ${parser.stringify(r)}`);
        }
        console.log("Matched:");
        Object.entries(matchTable).forEach(([k, v]) => {
            console.log(`${k} => ${parser.stringify(v)}`);
        });
        console.log("Assertions:");
        for (const [ast, isItem] of assertions) {
            console.log(`${parser.stringify(ast)}`);
        }
    }
    matchEq(a: AST, b: AST, isItem: boolean, matchTable: ReplvarMatchTable, constrains: [AST, AST, boolean][], assertions: [AST, boolean][]): boolean {
        if (a.type === "replvar" && a.name.startsWith("$") && b.type === "replvar" && a.name.startsWith("$")) {
            // // 把右边的变量全部换成该变量，换约束
            // for (let i = 0; i < constrains.length; i++) {
            //     astmgr.replace(constrains[i][0], b, a);
            //     astmgr.replace(constrains[i][1], b, a);
            // }
            // // 把右边的变量全部换成该变量，换mt
            // if (matchTable[b.name]) {
            //     if (matchTable[a.name]) {
            //         constrains.push([matchTable[b.name], matchTable[a.name], isItem]);
            //     } else {
            //         matchTable[a.name] = matchTable[b.name];
            //     }
            //     delete matchTable[b.name];
            // }
        }
        // remove #nf to match, and store it into assertion
        let nfParams: [AST, AST[], Set<string>];
        if (nfParams = assert.getNfParams(a) as [AST, AST[], Set<string>]) {
            assertions.push([a, isItem]);
            a = a.nodes[0];
        }
        if (nfParams = assert.getNfParams(b) as [AST, AST[], Set<string>]) {
            assertions.push([b, isItem]);
            b = b.nodes[0];
        }
        if (a.type === "replvar" && a.name.startsWith("$")) {
            if (!matchTable[a.name]) {
                matchTable[a.name] = b;
            } else if (!astmgr.equal(matchTable[a.name], b)) {
                constrains.push([matchTable[a.name], b, isItem]);
            }
            return true;
        }
        if (b.type === "replvar" && b.name.startsWith("$")) {
            if (!matchTable[b.name]) {
                matchTable[b.name] = a;
            } else if (!astmgr.equal(matchTable[b.name], a)) {
                constrains.push([matchTable[b.name], a, isItem]);
            }
            return true;
        }

        if (a.type !== b.type) return false;
        if (a.type === "sym" || a.type === "fn") {
            if (a.name !== b.name) return false;
            if (a.nodes.length !== b.nodes.length) return false;
            for (let i = 0; i < a.nodes.length; i++) {
                const res = this.matchEq(a.nodes[i], b.nodes[i], assert.getSubAstType(a, i, isItem), matchTable, constrains, assertions);
                if (res === false) return false;
            }
            return true;
        }
    }
    /*
组合元定理的匹配思路：先把条件和结论所有变量重命名，令条件的结论跟结论的条件相等，用solveConstrain解算变量约束关系
通过matchEq找到变量应该等于的表达式，得到一堆可能矛盾的变量约束集(ReplvarMatchTable)。下面求解约束：
    :处理循环与不一致
    若变量等于的式子相同(astmgr.Eq)，丢弃一条
    若变量等于不同的变量，丢弃这条，把右边的变量全部换成该变量
    若变量等于的式子不同（此时都是表达式），则继续通过matchEq加入表达式相等的约束，并删除后来的式子，重新回到:处理循环与不一致（设置个迭代深度，8次）
    
    :生成替换顺序表
    找到一个只在等式左边出现的变量，若找不到，报错（不允许出现无穷循环替换）
    找到后，把其它条中所有的该变量用这条公式替换，把这条约束放入最终的replaceTable
    若所有约束都放入了最终的replaceTable，结束，否则继续:生成替换顺序表

*/
    solveConstrain(constrains: [AST, AST, boolean][], assertions: [AST, boolean][]) {
        const matchTable: ReplvarMatchTable = {};
        let depth = 0;
        while (constrains.length > 0) {
            if (depth++ > 8) throw TR("无法解算变量约束，可能存在循环替换");
            let [left, right, isItem] = constrains.shift();
            if (astmgr.equal(left, right)) {
                // 丢弃
                continue;
                // } else if (left.type === "replvar" && right.type === "replvar" && left.name.startsWith("$") && right.name.startsWith("$")) {
                //     // 把右边的变量全部换成该变量
                //     for (let i = 0; i < constrains.length; i++) {
                //         astmgr.replace(constrains[i][0], right, left);
                //         astmgr.replace(constrains[i][1], right, left);
                //     }
                // } else if (left.type === "replvar" && left.name.startsWith("$")) {
                //     matchTable[left.name] = right;
                // } else if (right.type === "replvar" && right.name.startsWith("$")) {
                //     matchTable[right.name] = left;
            } else {
                // 都是表达式，则继续加入表达式相等的约束
                const res = this.matchEq(left, right, isItem, matchTable, constrains, assertions);
                if (res === false) throw TR("无法解算变量约束，可能存在不一致替换");
            }
        }
        return matchTable;
    }
    getNfAssertionsOfVarsInAST(ast: AST, isItem: boolean, scope: AST, res: { [name: string]: [AST, boolean] } = {}) {
        if (ast.type === "replvar" && ast.name.startsWith("$")) {
            res[ast.name] ??= [{ type: "replvar", name: "$ " }, isItem];
            res[ast.name][0] = astmgr.clone({ type: "fn", name: scope.name, nodes: [res[ast.name][0], ...scope.nodes.slice(1)] });
            assert.expand(res[ast.name][0], isItem);
            return;
        }
        if (assert.getNfParams(ast)) {
            scope ??= { type: "replvar", name: "$ " };
            scope = astmgr.clone({ type: "fn", name: ast.name, nodes: [scope, ...ast.nodes.slice(1)] });
            assert.expand(scope, true);

            this.getNfAssertionsOfVarsInAST(ast.nodes[0], isItem, scope, res);
            return res;
        }
        ast.nodes.forEach((n, idx) => this.getNfAssertionsOfVarsInAST(n, assert.getSubAstType(ast, idx, isItem), scope, res));
        return res;
    }
    addAssertions(mt: ReplvarMatchTable, assertions: [AST, boolean][]) {
        const res: { [name: string]: [AST, boolean] } = {};
        assertions.map(([ast, isItem]) => this.getNfAssertionsOfVarsInAST(ast, isItem, null, res));
        for (const [k, [v, isItem]] of Object.entries(res)) {
            const mtv = mt[k];
            if (mtv) {
                const nf_v = astmgr.clone(v);
                astmgr.replace(nf_v, { type: "replvar", name: "$ " }, mtv);
                assert.expand(nf_v, isItem);
                this.getNfAssertionsOfVarsInAST(nf_v, isItem, null, res)
            }
        }
        for (const [k, [v, isItem]] of Object.entries(res)) {
            astmgr.replace(v, { type: "replvar", name: "$ " }, { type: "replvar", name: k });
        }
        return res;
    }
}


/*

[.cs]>:#:<a1,cmp
[.t]<<:>:<a1,<a2,[.cs]
[.ne]>:#:.i,<<::a1,c<a3,c<a3
[.ni]:.ne,<a3
[.a30]>:::.ne,.t:.ni,.t,<a3
[.mn]:::::c.i:a1,ccmp,c<.a30,<a2:.i,mp,<a3
*/