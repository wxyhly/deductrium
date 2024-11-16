export class ASTMgr {
    clone(ast) {
        const newast = {
            type: ast.type, name: ast.name
        };
        if (ast.nodes) {
            newast.nodes = ast.nodes.map(p => this.clone(p));
        }
        return newast;
    }
    assign(ast, value) {
        const v = this.clone(value);
        ast.type = v.type;
        ast.name = v.name;
        ast.nodes = v.nodes;
    }
    equal(ast1, ast2) {
        if (ast1 === ast2)
            return true;
        if (ast1.name !== ast2.name)
            return false;
        if (ast1.type !== ast2.type)
            return false;
        if (ast1.nodes?.length !== ast2.nodes?.length)
            return false;
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.equal(ast1.nodes[i], ast2.nodes[i]))
                    return false;
            }
        }
        return true;
    }
    // get all replvars, replNames is a given set to be added in
    getVarNames(ast, varNames, reg) {
        if (ast.type === "replvar" && (reg ? ast.name.match(reg) : true))
            varNames.add(ast.name);
        if (ast.nodes)
            for (const n of ast.nodes) {
                this.getVarNames(n, varNames, reg).forEach(v => varNames.add(v));
            }
        return varNames;
    }
    // replaceVarNamesInAst(ast: AST, filterReg: RegExp, replaceSrc: RegExp, replaceDst: string) {
    //     if (ast.type === "replvar" && ast.name.match(filterReg)) {
    //         ast.name = ast.name.replace(replaceSrc, replaceDst);
    //     }
    //     if (ast.nodes?.length) {
    //         for (const n of ast.nodes) {
    //             this.replaceVarNamesInAst(n, filterReg, replaceSrc, replaceDst);
    //         }
    //     }
    // }
    // exact replace, without matching $.*s
    // nth: null or -1 for replaceAll, others for replace nth(start from 0) 
    replace(ast, searchValue, replaceValue, preventCircularReplace, nth, matchedTimes = 0) {
        nth ??= -1;
        if (this.equal(ast, searchValue)) {
            if (nth === -1 || (nth === matchedTimes)) {
                this.assign(ast, replaceValue);
                if (preventCircularReplace) {
                    ast.type = "$" + ast.type;
                }
            }
            return matchedTimes + 1;
        }
        if (ast.nodes?.length && !ast.type.startsWith("$")) {
            for (const n of ast.nodes) {
                matchedTimes = this.replace(n, searchValue, replaceValue, preventCircularReplace, nth, matchedTimes);
            }
        }
        return matchedTimes;
    }
    finishReplace(ast) {
        if (ast.type.startsWith("$"))
            ast.type = ast.type.slice(1);
        if (ast.nodes?.length) {
            for (const n of ast.nodes)
                this.finishReplace(n);
        }
    }
    replaceByMatchTable(ast, matchResult) {
        for (const [varname, matchedAst] of Object.entries(matchResult)) {
            this.replace(ast, { type: "replvar", name: varname }, matchedAst, true);
        }
        this.finishReplace(ast);
    }
}
//# sourceMappingURL=astmgr.js.map