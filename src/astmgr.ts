export type AST = { type: string, name: string, nodes?: AST[] };
export type ASTMatchResult = { [varname: string]: AST } | false;

export class ASTMgr {
    clone(ast: AST): AST {
        const newast: AST = {
            type: ast.type, name: ast.name
        };
        if (ast.nodes) {
            newast.nodes = ast.nodes.map(p => this.clone(p));
        }
        return newast;
    }
    assign(ast: AST, value: AST) {
        const v = this.clone(value);
        ast.type = v.type;
        ast.name = v.name;
        ast.nodes = v.nodes;
    }
    equal(ast1: AST, ast2: AST) {
        if (ast1 === ast2) return true;
        if (ast1.name !== ast2.name) return false;
        if (ast1.type !== ast2.type) return false;
        if (ast1.nodes?.length !== ast2.nodes?.length) return false;
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.equal(ast1.nodes[i], ast2.nodes[i])) return false;
            }
        }
        return true;
    }
    match(ast: AST, searchValue: AST, replNameRule: RegExp): ASTMatchResult {
        let result: ASTMatchResult = {};
        if (searchValue.name.match(replNameRule)) {
            result[searchValue.name] = ast;
            return result;
        }
        if (ast.nodes?.length !== searchValue.nodes?.length) return false;
        if (ast.type !== searchValue.type || ast.name !== searchValue.name) return false;
        if (ast.nodes?.length) {
            for (let i = 0; i < ast.nodes.length; i++) {
                result = this.mergeMatchResults(result,
                    this.match(ast.nodes[i], searchValue.nodes[i], replNameRule)
                );
                if (!result) return false;
            }
        }
        return result;
    }
    mergeMatchResults(res: ASTMatchResult, res2: ASTMatchResult) {
        if (!(res && res2)) return false;
        for (const [varname, matchedAst] of Object.entries(res2)) {
            res[varname] ??= matchedAst;
            if (!this.equal(res[varname], matchedAst)) {
                return false;
            }
        }
        return res;
    }
    replace(ast: AST, searchValue: AST, replaceValue: AST, preventCircularReplace?: boolean, replNameRule?: RegExp) {
        if (replNameRule) {
            const matchResult = this.match(ast, searchValue, replNameRule);
            if (matchResult) {
                const newReplaceValue = this.clone(replaceValue);
                this.replaceByMatchResult(newReplaceValue, matchResult);
                this.assign(ast, newReplaceValue);
                if (preventCircularReplace) { ast.type = "$" + ast.type; }
                return;
            }
        } else if (this.equal(ast, searchValue)) {
            this.assign(ast, replaceValue);
            if (preventCircularReplace) { ast.type = "$" + ast.type; }
            return;
        }
        if (ast.nodes?.length && !ast.type.startsWith("$")) {
            for (const n of ast.nodes) this.replace(n, searchValue, replaceValue, preventCircularReplace, replNameRule);
        }
        return;
    }
    private finishReplace(ast: AST) {
        if (ast.type.startsWith("$")) ast.type = ast.type.slice(1);
        if (ast.nodes?.length) {
            for (const n of ast.nodes) this.finishReplace(n);
        }
    }
    replaceByMatchResult(ast: AST, matchResult: ASTMatchResult) {
        if (!matchResult) throw "模式匹配失败";
        for (const [varname, matchedAst] of Object.entries(matchResult))
            this.replace(ast, { type: "replvar", name: varname }, matchedAst, true);
        this.finishReplace(ast);
    }
    replaceDeep(ast: AST, searchValue: AST, replaceValue: AST, replNameRule?: RegExp) {
        const nast = this.clone(ast);
        while (true) {
            this.replace(nast, searchValue, replaceValue, false, replNameRule);
            if (this.equal(nast, ast)) {
                this.assign(ast, nast); return;
            } else {
                this.assign(ast, nast);
            }
        }
    }
    getAllReplNames(ast: AST, replNameRule: RegExp): Set<string> {
        const replNames = new Set<string>;
        if (ast.name.match(replNameRule)) {
            replNames.add(ast.name);
            return replNames;
        }
        if (ast.nodes) for (const n of ast.nodes) this.getAllReplNames(n, replNameRule).forEach(v => replNames.add(v));
        return replNames;
    }
}