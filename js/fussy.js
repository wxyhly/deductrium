import { ASTMgr } from "./astmgr";
const T = 1;
const F = -1;
const U = 0;
const astmgr = new ASTMgr;
const logicSyms = ["<>", ">", "~", "&", "|"];
const quantSyms = ["E", "E!", "V"];
function not(b3) {
    return (-b3);
}
function and(b1, b2) {
    if (b1 === T && b2 === T)
        return T;
    if (b1 === F)
        return F;
    if (b2 === F)
        return F;
    return U;
}
function eq(name1, name2) {
    if (name1 === name2)
        return T;
    if (name1.match(/^\#/) || name2.match(/^\#/))
        return F;
    if (name1.match(/^\$/) || name2.match(/^\$/))
        return U;
    return F;
}
export class FussySystem {
    getVarName(ast) {
        if (ast.type === "replvar")
            return ast.name;
        const params = this.getNfParams(ast);
        if (params) {
            return this.getVarName(params[0]);
        }
        return false;
    }
    getNfParams(ast) {
        if (ast.type !== "fn")
            return false;
        if (ast.name.match(/^#v*nf$/)) {
            const quants = [];
            const vars = new Set;
            let i = 1;
            for (; ast.name[i] === "v"; i++) {
                let repeated = false;
                for (const q of quants) {
                    if (astmgr.equal(q, ast.nodes[i])) {
                        repeated = true;
                        break;
                    }
                }
                if (repeated)
                    continue;
                quants.push(ast.nodes[i]);
            }
            for (; i < ast.nodes.length; i++) {
                vars.add(this.getVarName(ast.nodes[i]));
            }
            return [ast.nodes[0], quants, vars];
        }
        return false;
    }
    getQuantParams(ast) {
        if (ast.type !== "sym")
            return false;
        if (quantSyms.includes(ast.name)) {
            return [ast.nodes[0], ast.nodes[1]];
        }
        return false;
    }
    getCrpParams(ast) {
        if (ast.type !== "fn")
            return false;
        if (ast.name !== "#crp")
            return false; //todo: vcrp??
        return ast.nodes;
    }
    ignoreAst(ast) {
        if (ast.type === "fn" && ast.name.startsWith("#"))
            return true;
        return false;
    }
    eqQ(q1, q2) {
        for (const x of q1) {
            let found = false;
            for (const y of q2) {
                if (astmgr.equal(x, y)) {
                    found = true;
                    break;
                }
            }
            if (!found)
                return false;
        }
        for (const x of q2) {
            let found = false;
            for (const y of q1) {
                if (astmgr.equal(x, y)) {
                    found = true;
                    break;
                }
            }
            if (!found)
                return false;
        }
        return true;
    }
    removeFn(ast) {
        if (ast.type !== "fn" && !ast.name.startsWith("#"))
            throw "can't remove function from non #fn ast";
        astmgr.assign(ast, ast.nodes[0]);
    }
    addNf(ast, qs, vs) {
        if (!vs.size)
            return;
        const nodes = [ast];
        for (let i = 0; i < qs.length; i++) {
            let repeated = false;
            const x = qs[i];
            for (let j = i + 1; j < qs.length; j++) {
                const y = qs[j];
                if (astmgr.equal(x, y)) {
                    repeated = true;
                    break;
                }
            }
            if (!repeated)
                nodes.push(x);
        }
        const wrappeed = {
            type: "fn",
            name: "#".padEnd(nodes.length, "v") + "nf",
            nodes
        };
        for (const v of vs) {
            nodes.push({ type: "replvar", name: v });
        }
        astmgr.assign(ast, wrappeed);
    }
    nf(name, ast, quants = [], nameIsNot) {
        const astName = this.getVarName(ast);
        // ast is var
        if (astName) {
            if (nameIsNot && nameIsNot.has(name))
                return T;
            const isEq = eq(name, astName);
            if (isEq === F)
                return T;
            // if no quant
            if (!quants?.length)
                return not(isEq);
            // if one quant
            if (quants.length === 1)
                return not(this.nf(name, quants[0]));
            // if more quants
            // nf(ast; q1, q2; name) = nf(nf(ast; q1; name); q2; name)
            const q1 = quants.slice(0);
            const q2 = q1.pop();
            return and(this.nf(name, ast, q1), this.nf(name, ast, [q2]));
        }
        // ast is not var
        const quantParam = this.getQuantParams(ast);
        //ast is quant
        if (quantParam) {
            const [q, sub] = quantParam;
            return this.nf(name, sub, [q, ...quants]);
        }
        const nfParams = this.getNfParams(ast);
        // ast is nf
        if (nfParams) {
            const [sub, sq, sv] = nfParams;
            if (this.eqQ(sq, quants)) {
                // n(a;b;c) = n(n(a;b;c);b;c)
                if (sv.has(name))
                    return T;
                return this.nf(name, sub, quants);
            }
            // todo: whether others can be determined?
            return U;
        }
        const ignore = this.ignoreAst(ast);
        // ast is complex fns which cant be mapped in nor decided
        if (ignore)
            return U;
        // ast is logic symbol, can be mapped in
        let res = T;
        if (ast.nodes?.length)
            for (const n of ast.nodes) {
                const subB = this.nf(name, n, quants);
                if (subB === F)
                    return F; // short circuit for "and"
                res = and(res, subB);
            }
        return res;
    }
    crp(ast, src, dst, varLists) {
        // item always can be replaced
        if (this.astIsItem(ast, varLists))
            return T;
        // if src=dst, id T
        if (this.astEq(src, dst) === T)
            return T;
        const srcName = this.getVarName(src);
        // if nothing can be replaced, id, T
        if (srcName && this.nf(srcName, ast) === T)
            return T;
        const eqsrc = this.astEq(src, ast);
        // if src is ast, result is dst, T
        if (eqsrc === T)
            return T;
        // crp(Vx:$1,$2($1),y) , eqsrc: U
        const getQuant = this.getQuantParams(ast);
        if (getQuant) {
            const q = this.getVarName(getQuant[0]);
            // crp(Vq:..,q,...) => T
            if (srcName === q)
                return T;
            const qIsNot = this.getVarIsNotList(getQuant[0]);
            // k(q)
            const qNfInSrc = this.nf(q, src, [], qIsNot);
            if (qNfInSrc === T || (srcName && this.nf(srcName, getQuant[0]))) {
                // crp(Vq:q+k+z,k,z) =>T
                // crp(Vq:q+k+z,k,q) =>F
                return and(this.nf(q, dst), this.crp(getQuant[1], src, dst, varLists));
            }
            // crp(Vq:q+k+w,q+k,z) =>F
            return qNfInSrc;
            // todo: crp(Vq:q+q+w,q+q,z) =>T , notfree, rp is id.
        }
        const getNf = this.getNfParams(ast);
        if (getNf) {
            // todo ??
        }
        const ignore = this.ignoreAst(ast);
        if (!ignore && ast.nodes?.length) {
            let res = T;
            for (const n of ast.nodes) {
                const subres = this.crp(n, src, dst, varLists);
                if (subres === F)
                    return F;
                res = and(res, subres);
            }
            return res;
        }
        return U;
    }
    getReplVarsType(ast, res = {}, isItem) {
        if (ast.type === "replvar") {
            res[ast.name] ??= isItem;
            if (res[ast.name] !== isItem)
                throw `变量${ast.name}不能同时为项和公式`;
        }
        for (const [idx, n] of ast.nodes.entries()) {
            this.getReplVarsType(n, res, this.getSubAstType(ast, idx, isItem));
        }
        return res;
    }
    astIsItem(ast, varLists) {
        if (ast.type === "replvar") {
            const v = varLists[ast.name];
            if (v === true)
                return true;
            if (v === false)
                return false;
            throw "cannot reached";
        }
        if (ast.type === "sym") {
            if (logicSyms.includes(ast.name))
                return false;
            if (quantSyms.includes(ast.name))
                return false;
            return true;
        }
        if (ast.type === "fn") {
            if (ast.name.match(/^#v*nf/) || ast.name.match(/^#c?rp/)) {
                return this.astIsItem(ast.nodes[0], varLists);
            }
        }
    }
    getVarIsNotList(varAst, isNot = new Set) {
        if (varAst.type === "replvar")
            return isNot;
        const nfp = this.getNfParams(varAst);
        if (!nfp)
            return isNot;
        this.getVarIsNotList(nfp[0], isNot);
        if (!nfp[1]?.length) {
            for (const n of nfp[2])
                isNot.add(n);
        }
        return isNot;
    }
    astEq(ast1, ast2) {
        if (astmgr.equal(ast1, ast2))
            return T;
        if (ast1.type === "replvar" && ast2.type === "replvar") {
            return eq(ast1.name, ast2.name);
        }
        if (ast1.type !== "replvar" && ast2.type !== "replvar") {
            if (ast1.name !== ast2.name)
                return F;
            if (ast1.nodes?.length !== ast2.nodes?.length)
                return F;
            if (!ast1.nodes)
                return true;
            let res = T;
            for (let i = 0; i < ast1.nodes.length; i++) {
                const subres = this.astEq(ast1.nodes[i], ast2.nodes[i]);
                if (subres === F)
                    return F;
                res = and(res, subres);
            }
            return res;
        }
        if (ast1.type === "replvar") {
            if (ast1.name.match(/^\$/)) {
                if (this.nf(ast1.name, ast2) === U)
                    return U;
                return F;
            }
            return F;
        }
        if (ast2.type === "replvar") {
            if (ast2.name.match(/^\$/)) {
                if (this.nf(ast1.name, ast2) === U)
                    return U;
                return F;
            }
            return F;
        }
    }
    // only according to ast's structure, give its nth child's type
    getSubAstType(ast, idx, parentType) {
        if (ast.type === "sym") {
            if (quantSyms.includes(ast.name))
                return idx === 0;
            return !logicSyms.includes(ast.name);
        }
        if (ast.type === "fn") {
            if (ast.name.match(/^#v*nf/) || ast.name.match(/^#c?rp/)) {
                // #v*nf( isitem, true, true ....);
                // #c?rp( isitem, true, true ....);
                return idx === 0 ? parentType : true;
            }
            return parentType;
        }
    }
    expand(ast, varLists, isItem) {
        varLists ??= this.getReplVarsType(ast, varLists, isItem);
        // first, check all subnodes are consist and expand them
        for (const [idx, n] of ast.nodes.entries()) {
            this.expand(n, varLists, this.getSubAstType(ast, idx, isItem));
        }
        // ast is atomvar
        if (ast.type === "replvar")
            return true;
        const nfParams = this.getNfParams(ast);
        // ast is nf
        if (nfParams) {
            const [sub, quants, vars] = nfParams;
            // self check
            for (const v of vars) {
                const res = this.nf(v, sub, quants);
                if (res === T)
                    vars.delete(v);
                if (res === F)
                    return false;
            }
            this.removeFn(ast);
            const quantParam = this.getQuantParams(sub);
            // sub is quant
            if (quantParam) {
                const [quant, subsub] = quantParam;
                this.addNf(subsub, [quant, ...quants], vars);
                if (!this.expand(subsub, varLists, false))
                    return false;
            }
            const subnfParams = this.getNfParams(sub);
            // sub is nf
            if (subnfParams) {
                const [subsub, sq, sv] = subnfParams;
                if (this.eqQ(sq, quants)) {
                    // n(a;b1,b2;c) = n(n(a;b1;c);b2;c)
                    for (const name of sv) {
                        vars.add(name);
                    }
                    this.removeFn(sub);
                    this.addNf(ast, quants, vars);
                    return this.expand(ast, varLists, isItem);
                }
                // todo: whether others can be determined?
                this.addNf(ast, quants, vars);
                return true;
            }
            const ignore = this.ignoreAst(sub);
            // sub is complex fns which cant be mapped in nor decided
            if (ignore) {
                this.addNf(ast, quants, vars);
                return true;
            }
            // nf(a>b) => nf(a) > nf(b)
            const subAstType = this.getSubAstType(ast, 0, isItem); // all same, just give 0
            if (sub.nodes?.length)
                for (const n of sub.nodes) {
                    this.addNf(n, quants, vars);
                    if (!this.expand(n, varLists, subAstType))
                        return false;
                }
        }
        const crpParams = this.getCrpParams(ast);
        // ast is crp
        if (crpParams) {
            const tf = this.crp(crpParams[0], crpParams[1], crpParams[2], varLists);
            if (tf === T)
                this.removeFn(ast);
            if (tf === F)
                return false;
        }
    }
    // replNameReg: rule for replace var
    match(ast, pattern, replNameReg, result = {}, assertions) {
        if (pattern.type === "replvar" && pattern.name.match(replNameReg)) {
            result[pattern.name] ??= ast;
            if (!astmgr.equal(result[pattern.name], ast))
                throw `模式匹配失败：无法匹配替代变量${pattern.name}`;
            return;
        }
        if (pattern.type === "fn" && pattern.name.match(/^(#v*nf|crp)/)) {
            this.match(ast, pattern.nodes[0], replNameReg, result, assertions);
            // ignore assertions, but collect them for later check
            assertions.push(pattern);
            return;
        }
        if (ast.type !== pattern.type || ast.name !== pattern.name)
            throw "模式匹配失败";
        if (ast.nodes?.length !== pattern.nodes?.length)
            throw "模式匹配失败";
        if (ast.nodes?.length) {
            for (let i = 0; i < ast.nodes.length; i++) {
                this.match(ast.nodes[i], pattern.nodes[i], replNameReg, result, assertions);
            }
        }
    }
}
//# sourceMappingURL=fussy.js.map