import { TR } from "../lang.js";
import { ASTMgr } from "./astmgr.js";
const astmgr = new ASTMgr;
const logicSyms = ["<>", ">", "~", "&", "|"];
const quantSyms = ["E", "E!", "V"];
const verbSyms = ["@", "=", "<", "<=", ">=", "/|"];
// const verbFns = ["Prime", "Equiv", "Order", "WellOrder", "Rel", "Point", "Line", "Plane", "Between", "Angle"];
const fnSyms = ["U", "I", "S", "+", "-", "*", "X", "/", "\\"];
import { ASTParser } from "./astparser.js";
const parser = new ASTParser;
const T = 1;
const F = -1;
const U = 0;
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
function or(b1, b2) {
    if (b1 === T)
        return T;
    if (b2 === T)
        return T;
    if (b1 === F && b2 === F)
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
export class AssertionSystem {
    fns = new Set;
    verbs = new Set;
    consts = new Set;
    // if ast is var (with asserts) return name, else return false
    getVarName(ast) {
        if (ast.type === "replvar")
            return ast.name;
        const params = this.getNfParams(ast);
        if (params) {
            return this.getVarName(params[0]);
        }
        return false;
    }
    // if ast is fn #v*nf, return [subAst, quantsvars, nofreevars] else return false
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
        let nth = ast.nodes[3]?.name;
        let newnth;
        if (isFinite(Number(nth)))
            newnth = Number(nth) - 1;
        let right = false;
        if (newnth < -1) {
            newnth = -(newnth + 2);
            right = true;
        }
        return [ast.nodes[0], ast.nodes[1], ast.nodes[2], nth ? (newnth ?? nth) : -1, right];
    }
    getRpParams(ast) {
        if (ast.type !== "fn")
            return false;
        if (ast.name !== "#rp")
            return false;
        let nth = ast.nodes[3]?.name;
        let newnth;
        if (isFinite(Number(nth)))
            newnth = Number(nth) - 1;
        let right = false;
        if (newnth < -1) {
            newnth = -(newnth + 2);
            right = true;
        }
        return [ast.nodes[0], ast.nodes[1], ast.nodes[2], nth ? (newnth ?? nth) : -1, right];
    }
    // check if assertions can't be propagated into ast's children nodes
    ignorePropagateAst(ast) {
        if (!ast.nodes?.length)
            return true;
        if (quantSyms.includes(ast.name) && ast.type === "sym")
            return true;
        if (ast.type === "fn" && ast.name.startsWith("#"))
            return true;
        return false;
    }
    // return q1 < q2, regarding arrays q1 q2 as sets
    subsetQuants(q1, q2) {
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
        return true;
    }
    // remove all #fns, return the first child node
    removeFn(ast) {
        if (ast.type !== "fn" && !ast.name.startsWith("#"))
            throw "can't remove function from non #fn ast";
        astmgr.assign(ast, ast.nodes[0]);
    }
    // wrap ast with #v*nf fn, without simplify
    addNf(ast, qs, vs) {
        if (!vs.size)
            return;
        const nodes = [ast];
        qs.sort((a, b) => a.name > b.name ? 1 : a.name === b.name ? 0 : -1);
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
        for (const v of Array.from(vs).sort()) {
            nodes.push({ type: "replvar", name: v });
        }
        astmgr.assign(ast, wrappeed);
    }
    // fussy check whether name is nofree in V* ast, exclusions can be provided for replvar name
    nf(name, ast, quants = [], nameIsNot) {
        const astName = this.getVarName(ast);
        // ast is var
        if (ast.type === "replvar") {
            if (nameIsNot && nameIsNot.has(name))
                return T;
            const isEq = eq(name, astName);
            if (isEq === F)
                return T;
            // if no quant
            if (!quants?.length)
                return not(isEq);
            let res = F;
            for (const q of quants) {
                // if quants, check whether name is in quants, if T, then nf
                res = or(res, not(this.nf(name, q)));
                // we also check whether astVar is bounded by quants, if T, then nf 
                res = or(res, not(this.nf(astName, q, [], this.getVarIsNotList(ast))));
            }
            if (res === T)
                return T;
            // if name is not in quants, and astVar is free, nf <=> not equal
            if (res === F)
                return not(isEq);
            return U;
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
            if (this.subsetQuants(sq, quants)) {
                // n(V1V2 a;;c) > n(V1V2V3V4 a;;c) => n(a;1,2;c) > n(a;1,2,3,4;c)
                if (sv.has(name))
                    return T;
                return this.nf(name, sub, quants);
            }
            // todo: whether others can be determined?
            return U;
        }
        const rpParams = this.getRpParams(ast);
        // ast is rp
        if (rpParams) {
            const [sub, src, dst, nth] = rpParams;
            if (nth === -1 && this.getVarName(src) === name) {
                // n(#rp(n(.,d), s/d, 0), s)
                const dstName = this.getVarName(dst);
                if (dstName && this.nf(dstName, sub, quants, this.getVarIsNotList(dst)) === T) {
                    return T;
                }
                // n(#rp(., s/n(d,s), 0), s)
                if (this.nf(name, dst, quants, this.getVarIsNotList(dst)) === T) {
                    return T;
                }
            }
            // n(#rp(n(.,c), ./n(d,c), .), c) =>
            if (this.nf(name, sub, quants, nameIsNot) === T && this.nf(name, dst, quants, nameIsNot) === T) {
                return T;
            }
            return U;
        }
        // n({x@y|z}) <=> n(y) && vn(z,x)
        if (ast.type === "sym" && (ast.name === "{|" || ast.name === "|}")) {
            return and(this.nf(name, ast.nodes[1], quants, nameIsNot), this.nf(name, ast.nodes[2], [ast.nodes[0], ...quants], nameIsNot));
        }
        const ignore = this.ignorePropagateAst(ast);
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
    // fussy check for #crp (can replace), varTypes is provided outside
    // if nth === -1, replace all
    crp(ast, src, dst, nth, right, varTypes) {
        if (typeof nth === "string" && !nth.match(/^\$/))
            throw TR(`替换表达式中指定的匹配序号`) + nth + TR('必须为整数');
        if (typeof nth === "number" && Math.floor(nth) !== nth)
            throw TR("替换表达式中指定的匹配序号") + nth + TR('必须为整数');
        // item always can be replaced, so no need to check ast == src situation 
        // update: added {x@y|P(x)}, this is not true
        // if (this.getAstType(ast, varTypes)) return T;
        // if src=dst, id T
        if (this.astEq(src, dst) === T)
            return T;
        // todo: verify: if contains assertions, just match them exactly is ok?
        const scopes = this.getSubAstMatchTimes(ast, src, Number(nth), dst, undefined, undefined, right);
        if (!scopes)
            return U; // can't decide
        for (const [idx, scope] of scopes.entries()) {
            // if not match all, just verify nth
            if (typeof nth === "number") {
                if (nth !== -1 && idx !== nth)
                    continue;
                if (nth > idx)
                    break; // short circuit
            }
            let AllF = true;
            let res = T;
            for (const bv of scope) {
                const bvName = this.getVarName(bv);
                const bvIsNot = this.getVarIsNotList(bv);
                const nf = this.nf(bvName, dst, [], bvIsNot);
                res = and(res, nf);
                if (res !== F)
                    AllF = false;
            }
            if (typeof nth === "number") {
                return res;
            }
            else {
                // [U, F] => U
                // [F, F] => F
                // [T, T] => T
                // [T, F] => U
                return res === T ? T : AllF ? F : U;
            }
        }
        // passed all scope checkments
        return T;
    }
    // return a ReplvarTypeTable (or add to a existed one, throw error when conflits) for ast
    getReplVarsType(ast, res = {}, isItem, resfn = {}) {
        if (ast.type === "replvar") {
            res[ast.name] ??= isItem;
            if (res[ast.name] !== isItem)
                throw TR(`变量`) + ast.name + TR('不能同时为项和公式');
            return res;
        }
        if (ast.type === "fn" && !ast.name.startsWith("#")) {
            resfn[ast.name] ??= isItem;
            if (resfn[ast.name] !== isItem)
                throw `Token ` + ast.name + TR('不能同时为函数和谓词');
            // return res;
        }
        for (const [idx, n] of ast.nodes.entries()) {
            this.getReplVarsType(n, res, this.getSubAstType(ast, idx, isItem), resfn);
        }
        return res;
    }
    // return ast's type (item for true, boolean for false)
    getAstType(ast, varLists) {
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
            if (ast.name === "{|" || ast.name === "|}")
                return true;
            return true;
        }
        if (ast.type === "fn") {
            if (ast.name === "{" || ast.name === "(")
                return true;
            if (ast.name.match(/^#v*nf/) || ast.name.match(/^#c?rp/)) {
                return this.getAstType(ast.nodes[0], varLists);
            }
        }
    }
    // if replvar is ast with nf assertions, get excluded values for this replvar
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
    // fussy eq
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
                return T;
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
                // $1 = $2+$3 : U
                const subReplvars = (this.getVarNamesAndIsNots(ast2, {}, /^\$/));
                // $1 = $2+$1 : F
                if (subReplvars[ast1.name])
                    return F;
                // $1 = $2($1) : F
                if (this.nf(ast1.name, ast2) === U)
                    return U;
                return F;
            }
            // x = $1+$2
            return F;
        }
        if (ast2.type === "replvar") {
            if (ast2.name.match(/^\$/)) {
                const subReplvars = (this.getVarNamesAndIsNots(ast1, {}, /^\$/));
                if (subReplvars[ast2.name])
                    return F;
                if (this.nf(ast2.name, ast1) === U)
                    return U;
                return F;
            }
            return F;
        }
    }
    getVarNamesAndIsNots(ast, res, reg, scope = new Set) {
        const varname = this.getVarName(ast);
        if (varname) {
            if (!varname.match(reg))
                return res;
            res[varname] = this.getVarIsNotList(ast, res[varname]);
            for (const s of scope)
                res[varname].add(s);
            return res;
        }
        const nfp = this.getNfParams(ast);
        if (nfp) {
            if (!nfp[1].length) { // if nf with no quant
                for (const s of nfp[2])
                    scope.add(s);
            }
            return this.getVarNamesAndIsNots(nfp[0], res, reg, scope);
        }
        const crp = this.getCrpParams(ast);
        if (crp) {
            return this.getVarNamesAndIsNots(crp[0], res, reg, scope);
        }
        const ignore = this.ignorePropagateAst(ast);
        if (ignore && !this.getQuantParams(ast)) {
            return res; // unknown
        }
        if (ast.nodes)
            for (const n of ast.nodes) {
                this.getVarNamesAndIsNots(n, res, reg, new Set(scope));
            }
        return res;
    }
    // fussy search if subast exist in ast
    // return  matched positions's scopes, false if unknown
    getSubAstMatchTimes(ast, subAst, nth, dst, scope = [], res = [], right) {
        if (scope.length) {
            const vars = this.getVarNamesAndIsNots(subAst, {}, null);
            for (const [v, vIsNot] of Object.entries(vars)) {
                for (const bv of scope) {
                    const nf = this.nf(v, bv, [], vIsNot);
                    if (nf === F)
                        return res; // can't match any bounded vars
                    if (nf === U)
                        return false; // can't decided
                }
            }
        }
        const eq = this.astEq(ast, subAst);
        if (eq === T) {
            res.push(scope);
            return res;
        } // matched whole ast one time
        if (eq === U) {
            if (nth === -1 && (this.astEq(ast, dst)))
                return res;
            return false; // unknown
        }
        // else not equal
        if (!ast.nodes?.length)
            return res; // end of node, find 0
        const qp = this.getQuantParams(ast);
        if (qp) {
            // can't find free y in Vy:xxx
            if (qp[0].name === subAst.name && subAst.type === "replvar")
                return res;
            scope.push(qp[0]);
            return this.getSubAstMatchTimes(qp[1], subAst, nth, dst, scope, res, right);
        }
        if (ast.type === "sym" && (ast.name === "{|" || ast.name === "|}")) {
            if ((!right) === (ast.name === "{|")) {
                // {0@1|2}
                const result = this.getSubAstMatchTimes(ast.nodes[1], subAst, nth, dst, scope.slice(0), res, right);
                // if found exact nth
                if (nth !== -1 && res.length === nth + 1)
                    return res;
                // unknown spread
                if (result === false)
                    return false;
                scope.push(ast.nodes[0]);
                return this.getSubAstMatchTimes(ast.nodes[2], subAst, nth, dst, scope, res, right);
            }
            else {
                // {2|0@1}
                const result = this.getSubAstMatchTimes(ast.nodes[2], subAst, nth, dst, [ast.nodes[0], ...scope], res, right);
                // if found exact nth
                if (nth !== -1 && res.length === nth + 1)
                    return res;
                // unknown spread
                if (result === false)
                    return false;
                return this.getSubAstMatchTimes(ast.nodes[1], subAst, nth, dst, scope, res, right);
            }
        }
        if (right) {
            for (let n = ast.nodes.length - 1; n >= 0; n--) {
                const result = this.getSubAstMatchTimes(ast.nodes[n], subAst, nth, dst, scope.slice(0), res, right);
                // if found exact nth
                if (nth !== -1 && res.length === nth + 1)
                    return res;
                // unknown spread
                if (result === false)
                    return false;
            }
        }
        else {
            for (const n of ast.nodes) {
                // unknown spread
                if (this.getSubAstMatchTimes(n, subAst, nth, dst, scope.slice(0), res, right) === false)
                    return false;
            }
        }
        return res;
    }
    getSubAstMatchTimesAndReplace(ast, subAst, newAst, nth, scope = [], res = [], right) {
        if (nth !== -1 && nth < res.length)
            return res; // completed, this short circuit is neccesary for later unknown $s 
        if (scope.length) {
            const vars = this.getVarNamesAndIsNots(subAst, {}, null);
            for (const [v, vIsNot] of Object.entries(vars)) {
                for (const bv of scope) {
                    const nf = this.nf(v, bv, [], vIsNot);
                    if (nf === F)
                        return res; // can't match any bounded vars
                    if (nf === U)
                        return false; // can't decided
                }
            }
        }
        // x=x, x->y, 1
        const eq = this.astEq(ast, subAst);
        if (eq === T) {
            // here replace happens
            if (nth === res.length || nth === -1) {
                astmgr.assign(ast, newAst);
            }
            res.push(scope);
            return res;
        } // matched whole ast one time
        if (eq === U) {
            // if (nth === -1 && this.astEq(ast, newAst)) return res;
            return false; // unknown
        }
        // else not equal
        if (!ast.nodes?.length)
            return res; // end of node, find 0
        const qp = this.getQuantParams(ast);
        if (qp) {
            const bounded = this.astEq(qp[0], subAst);
            if (bounded === T)
                return res; // can't match bounded var
            if (bounded === U)
                return false;
            scope.push(qp[0]);
            return this.getSubAstMatchTimesAndReplace(qp[1], subAst, newAst, nth, scope, res, right);
        }
        const backup = astmgr.clone(ast);
        if (ast.type === "sym" && (ast.name === "{|" || ast.name === "|}")) {
            const bounded = this.astEq(ast.nodes[0], subAst);
            if (bounded === U)
                return false;
            if ((!right) === (ast.name === "{|")) {
                let subres = this.getSubAstMatchTimesAndReplace(ast.nodes[1], subAst, newAst, nth, scope.slice(0), res, right);
                if (subres === false) {
                    astmgr.assign(ast, backup);
                    return false;
                }
                if (bounded === T)
                    return res; // can't match bounded var
                scope.push(ast.nodes[0]);
                subres = this.getSubAstMatchTimesAndReplace(ast.nodes[2], subAst, newAst, nth, scope, res, right);
                if (subres === false) {
                    astmgr.assign(ast, backup);
                    return false;
                }
            }
            else {
                let subres = this.getSubAstMatchTimesAndReplace(ast.nodes[2], subAst, newAst, nth, [ast.nodes[0], ...scope], res, right);
                if (subres === false) {
                    astmgr.assign(ast, backup);
                    return false;
                }
                if (bounded === T)
                    return res; // can't match bounded var
                subres = this.getSubAstMatchTimesAndReplace(ast.nodes[1], subAst, newAst, nth, scope, res, right);
                if (subres === false) {
                    astmgr.assign(ast, backup);
                    return false;
                }
            }
        }
        else if (right) {
            for (let n = ast.nodes.length - 1; n >= 0; n--) {
                const subres = this.getSubAstMatchTimesAndReplace(ast.nodes[n], subAst, newAst, nth, scope.slice(0), res, right);
                // if unknown, don't spread, just ignore it and replace??
                if (subres === false) {
                    // No! this time all are not sure, undo all changes, remain #rp
                    astmgr.assign(ast, backup);
                    return false;
                }
            }
        }
        else {
            for (const n of ast.nodes) {
                const subres = this.getSubAstMatchTimesAndReplace(n, subAst, newAst, nth, scope.slice(0), res, right);
                // if unknown, don't spread, just ignore it and replace??
                if (subres === false) {
                    // No! this time all are not sure, undo all changes, remain #rp
                    astmgr.assign(ast, backup);
                    return false;
                }
            }
        }
        return res;
    }
    // only according to ast's structure, give its nth child's type
    // this is a helper fn for recursively check sub nodes
    getSubAstType(ast, idx, parentType) {
        if (ast.type === "sym") {
            if (ast.name === "{|")
                return idx <= 1;
            if (ast.name === "|}")
                return true;
            if (quantSyms.includes(ast.name))
                return idx === 0;
            return !logicSyms.includes(ast.name);
        }
        if (ast.type === "fn") {
            if (this.verbs.has(ast.name)) {
                return true;
            }
            if (ast.name.match(/^#v*nf/) || ast.name.match(/^#c?rp/)) {
                // #v*nf( isItem, true, true ....);
                // #c?rp( isItem, true, true ....);
                return idx === 0 ? parentType : true;
            }
            return true;
        }
    }
    // remove all assert fns without checkments
    unwrapAssertions(ast) {
        if (ast.type === "replvar")
            return;
        // we don't remove #rp, this can cause #rp in condition can't be matched
        // but that's okay because you never know what is replaced after #rp fn
        if (ast.type === "fn" && ast.name.startsWith("#") && ast.name !== "#rp") {
            this.removeFn(ast);
            this.unwrapAssertions(ast);
            return;
        }
        for (const n of ast.nodes) {
            this.unwrapAssertions(n);
        }
    }
    // reduce and expand assertions in ast
    expand(ast, isItem, varLists) {
        // astmgr.assign(ast,astmgr.clone(ast)); // avoid inner inter refering
        varLists ??= this.getReplVarsType(ast, {}, isItem);
        // first, check all subnodes are consist and expand them
        if (ast.nodes?.length) {
            for (const [idx, n] of ast.nodes.entries()) {
                this.expand(n, this.getSubAstType(ast, idx, isItem), varLists);
            }
        }
        // ast is atomvar
        if (ast.type === "replvar")
            return;
        const nfParams = this.getNfParams(ast);
        // ast is nf
        if (nfParams) {
            let [sub, quants, vars] = nfParams;
            // self check
            for (const v of vars) {
                let res = this.nf(v, sub, quants);
                if (res === T)
                    vars.delete(v);
                if (res === F)
                    throw TR("断言失败：变量") + v + TR("自由出现");
            }
            // then check if quants can be eliminated
            const toRemove = [];
            for (const q of quants) {
                let allNotEq = true;
                for (const v of vars) {
                    if (this.nf(v, q) !== T) {
                        allNotEq = false;
                        break;
                    }
                }
                if (allNotEq || this.nf(this.getVarName(q), sub, [], this.getVarIsNotList(q)) === T) {
                    toRemove.push(q);
                }
            }
            quants = quants.filter(q => !toRemove.includes(q));
            this.removeFn(ast);
            sub = ast;
            const quantParam = this.getQuantParams(sub);
            // sub is quant
            if (quantParam) {
                const [quant, subsub] = quantParam;
                this.addNf(subsub, [quant, ...quants], vars);
                this.expand(subsub, false, varLists);
                return;
            }
            const subnfParams = this.getNfParams(sub);
            // sub is nf
            if (subnfParams) {
                const [subsub, sq, sv] = subnfParams;
                if (this.subsetQuants(sq, quants)) {
                    // n(a;b1,b2;c) = n(n(a;b1,b2;c);b2;c)
                    for (const name of sv) {
                        vars.add(name);
                    }
                    this.removeFn(sub);
                    this.addNf(ast, quants, vars);
                    return this.expand(ast, isItem, varLists);
                }
                else if (this.subsetQuants(quants, sq)) {
                    for (const name of vars) {
                        sv.add(name);
                    }
                    this.removeFn(sub);
                    this.addNf(sub, sq, sv);
                    return this.expand(ast, isItem, varLists);
                }
                // todo: whether others can be determined?
                this.addNf(ast, quants, vars);
                return;
            }
            if (sub.type === "sym" && (ast.name === "{|" || ast.name === "|}")) {
                this.addNf(sub.nodes[1], quants, vars);
                this.addNf(sub.nodes[2], [sub.nodes[0], ...quants], vars);
                return this.expand(ast, isItem, varLists);
            }
            const ignore = this.ignorePropagateAst(sub);
            // sub is complex fns which cant be mapped in nor decided
            if (ignore) {
                this.addNf(ast, quants, vars);
                return;
            }
            // nf(a>b) => nf(a) > nf(b)
            const subAstType = this.getSubAstType(ast, 0, isItem); // all same, just give 0
            if (sub.nodes?.length)
                for (const n of sub.nodes) {
                    this.addNf(n, quants, vars);
                    this.expand(n, subAstType, varLists);
                }
        }
        const crpParams = this.getCrpParams(ast);
        // ast is crp
        if (crpParams) {
            const tf = this.crp(...crpParams, varLists);
            if (tf === T)
                this.removeFn(ast);
            if (tf === F)
                throw TR("断言失败：#crp执行替换后自由变量将被量词约束");
            // todo
        }
        const rpParams = this.getRpParams(ast);
        // ast is rp
        if (rpParams) {
            const [sub, src, dst, nth, right] = rpParams;
            if (nth === -1 && ast.nodes.length === 4)
                ast.nodes.pop(); //omit #rp(.,./.,0)
            // const tf = this.crp(sub, src, dst, nth, right, varLists);
            // if (tf === F) throw TR("函数#rp执行失败：自由变量将被量词约束");
            if (this.astEq(src, dst) === T) {
                this.removeFn(ast);
                return;
            } // id
            // added special cases on 2025/09/28
            // #rp(a > b,c/d) = #rp(a,c/d) > #rp(b,c/d)
            // #rp(a @ b,c/d) = #rp(a,c/d) @ #rp(b,c/d)
            if (nth === -1 && sub.type === "sym" &&
                (logicSyms.includes(sub.name) || verbSyms.includes(sub.name))) {
                for (const c of sub.nodes) {
                    const wrapped = { type: "fn", name: "#rp", nodes: ast.nodes.slice(0) };
                    wrapped.nodes[0] = c;
                    astmgr.assign(c, wrapped); // wrap inside
                }
                astmgr.assign(ast, sub); // unwrap outside
                this.expand(ast, verbSyms.includes(sub.name), varLists);
                return;
            }
            const srcName = this.getVarName(src);
            if (srcName && this.nf(srcName, sub, [], this.getVarIsNotList(src)) === T) {
                // no free var to replace
                this.removeFn(ast);
                return;
            }
            const subrpParams = this.getRpParams(sub);
            if (subrpParams) {
                // #rp(#rp(#nf(subsub,b), a, b, ~), b, c, 0) === #rp(#nf(subsub,b),a,c,~)
                // #rp(#rp(#nf(subsub,b), a, b, 0), b, c, ~) === #rp(#nf(subsub,b),a,c,~)
                // #rp(#rp(#nf(subsub,s), a, b, 0), s, c, 0) === #rp(#nf(subsub,s),a,#rp(b,s,c),0)
                const [subsub, a, b, snth] = subrpParams;
                if ((nth === -1 || snth === -1)) {
                    if (srcName && this.nf(srcName, subsub, [], this.getVarIsNotList(src))) {
                        // if not replace all, move inner nth to outter
                        if (snth !== -1) {
                            ast.nodes[3] = sub.nodes[3];
                        }
                        if (this.astEq(src, b) === T) {
                            this.removeFn(sub);
                            astmgr.assign(src, a);
                            this.expand(ast, isItem, varLists);
                            return;
                        }
                        else if (nth === -1 && snth === -1) {
                            this.removeFn(sub);
                            astmgr.assign(ast.nodes[2], {
                                type: "fn", name: "#rp", nodes: [
                                    b, src, dst
                                ]
                            });
                            astmgr.assign(ast.nodes[1], a);
                            this.expand(ast, isItem, varLists);
                            return;
                        }
                    }
                }
            }
            if (sub.type === "sym" && (ast.name === "{|" || ast.name === "|}") && nth === -1) {
                // #rp({x@y|z}) === {x@rp(y)|rp(Vx:z)},then (Vx:rp(z)) => rp(z)
                const backup = astmgr.clone(ast);
                const [q, item, prop] = sub.nodes;
                const nodes = ast.nodes;
                nodes[0] = item;
                astmgr.assign(ast, sub); // {|}
                astmgr.assign(ast.nodes[1], { type: "fn", name: "#rp", nodes }); // {x@#rp|}
                nodes[0] = { type: "sym", name: "V", nodes: [q, prop] };
                astmgr.assign(ast.nodes[2], { type: "fn", name: "#rp", nodes }); // {x@|#rp(Vx:)}
                this.expand(ast.nodes[1], true, varLists);
                this.expand(ast.nodes[2], false, varLists);
                if (ast.nodes[2].type === "sym" && ast.nodes[2].name === "V") {
                    // remove Vx
                    astmgr.assign(ast.nodes[2], ast.nodes[2].nodes[1]);
                }
                else {
                    // can't remove Vx, rollback
                    astmgr.assign(ast, backup);
                }
                return;
            }
            const quantParam = this.getQuantParams(sub);
            if (quantParam) {
                // #rp(Vx: ~, nf(.,x)/nf(.,x), .) === Vx: #rp( ~, nf(.,x)/nf(.,x), .)
                const [q, subsub] = quantParam;
                const qName = this.getVarName(q);
                if (this.nf(qName, src, [], this.getVarIsNotList(q)) === T && this.nf(qName, dst, [], this.getVarIsNotList(q)) === T) {
                    const nodes = ast.nodes;
                    nodes[0] = subsub;
                    astmgr.assign(ast, sub);
                    astmgr.assign(ast.nodes[1], { type: "fn", name: "#rp", nodes });
                    this.expand(ast.nodes[1], isItem, varLists);
                    return;
                }
            }
            // if (tf === U) {
            //      return; // else can't expand, keep it
            // }
            const eq = this.astEq(sub, src);
            if (eq === T) {
                astmgr.assign(ast, dst);
                return;
            } // exact match, todo: nth
            if (eq === U)
                return;
            if (typeof nth === "string")
                return;
            const scopes = this.getSubAstMatchTimesAndReplace(sub, src, dst, nth, undefined, undefined, right);
            if (scopes) {
                for (const [idx, scope] of scopes.entries()) {
                    // if not match all, just verify nth
                    if (typeof nth === "number") {
                        if (nth !== -1 && idx !== nth)
                            continue;
                        if (nth > idx)
                            break; // short circuit
                    }
                    let AllF = true;
                    let res = T;
                    for (const bv of scope) {
                        const bvName = this.getVarName(bv);
                        const bvIsNot = this.getVarIsNotList(bv);
                        const nf = this.nf(bvName, dst, [], bvIsNot);
                        res = and(res, nf);
                        if (res !== F)
                            AllF = false;
                    }
                    let crp;
                    if (typeof nth === "number") {
                        crp = res;
                    }
                    else {
                        // [U, F] => U
                        // [F, F] => F
                        // [T, T] => T
                        // [T, F] => U
                        crp = res === T ? T : AllF ? F : U;
                    }
                    if (crp !== T)
                        throw TR("断言失败：#rp执行替换后自由变量将被量词约束");
                }
                astmgr.assign(ast, sub); // unwrap
            }
            ;
            // else keep #rp
        }
    }
    equalWithAssertion(ast1, ast2, assertions) {
        if (ast1 === ast2)
            return true;
        if (ast1.type === "fn" && ast1.name.match(/^#(v*nf|crp)/) && assertions) {
            const a = this.equalWithAssertion(ast1.nodes[0], ast2, assertions);
            assertions[parser.stringifyTight(ast1.nodes[0])] = astmgr.clone(ast1);
            return a;
        }
        if (ast2.type === "fn" && ast2.name.match(/^#(v*nf|crp)/) && assertions) {
            const a = this.equalWithAssertion(ast1, ast2.nodes[0], assertions);
            assertions[parser.stringifyTight(ast2.nodes[0])] = astmgr.clone(ast2);
            return a;
        }
        if (ast1.name !== ast2.name)
            return false;
        if (ast1.type !== ast2.type)
            return false;
        if (ast1.nodes?.length !== ast2.nodes?.length)
            return false;
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.equalWithAssertion(ast1.nodes[i], ast2.nodes[i], assertions))
                    return false;
            }
        }
        return true;
    }
    // replNameReg: rule for replace var
    match(ast, pattern, replNameReg, isItem, result, varTable, astAssertions, patternAssertions) {
        if (ast.type === "fn" && ast.name.match(/^#(v*nf|crp)/) && astAssertions) {
            // ignore assertions in ast, but collect them for later check
            this.match(ast.nodes[0], pattern, replNameReg, isItem, result, varTable, astAssertions, patternAssertions);
            // this way (Dict rather that Array) can avoid repeated assertions in ast
            astAssertions[parser.stringifyTight(ast.nodes[0])] = astmgr.clone(ast);
        }
        if (pattern.type === "replvar" && pattern.name.match(replNameReg)) {
            result[pattern.name] ??= ast;
            this.getReplVarsType(ast, varTable, isItem);
            if (!this.equalWithAssertion(result[pattern.name], ast, astAssertions)) {
                if ((!!this.getRpParams(ast)) !== (!!this.getRpParams(ast))) {
                    throw TR(`替换函数#rp导致模式匹配`) + pattern.name + TR(`时无法顺利进行`) + `: \n` + (parser.stringify(result[pattern.name])) + " <=?=> " + (parser.stringify(ast));
                }
                throw TR(`模式匹配失败：匹配多个替代变量`) + pattern.name + TR(`时值不相同`) + `: \n` + (parser.stringify(result[pattern.name])) + " <=X=> " + (parser.stringify(ast));
            }
            return;
        }
        if (pattern.type === "fn" && pattern.name.match(/^#(v*nf|crp)/)) {
            this.match(ast, pattern.nodes[0], replNameReg, isItem, result, varTable, astAssertions, patternAssertions);
            // ignore assertions in pattern, but collect them for later check
            patternAssertions.push(astmgr.clone(pattern));
            return;
        }
        if (ast.type !== pattern.type || ast.name !== pattern.name) {
            if ((!!this.getRpParams(pattern)) !== (!!this.getRpParams(ast))) {
                throw TR(`替换函数#rp导致模式匹配`) + TR(`时无法顺利进行`) + `: \n` + (parser.stringify(pattern)) + " <=?=> " + (parser.stringify(ast));
            }
            throw TR("模式匹配失败");
        }
        if (ast.nodes?.length !== pattern.nodes?.length)
            throw TR("模式匹配失败");
        if (ast.nodes?.length) {
            for (let i = 0; i < ast.nodes.length; i++) {
                this.match(ast.nodes[i], pattern.nodes[i], replNameReg, this.getSubAstType(ast, i, isItem), result, varTable, astAssertions, patternAssertions);
            }
        }
    }
    // match sub exactly and replace without fussy booleans, return total matched counts
    matchSubAndReplace(ast, pattern, replace, nth, replNameReg, isItem, result, varTable) {
        if (nth >= 0 && !(result <= nth))
            return result;
        try {
            // match root ast
            const matched = {};
            const patternAssertions = [];
            this.match(ast, pattern, replNameReg, isItem, matched, varTable, null, patternAssertions);
            for (const ass of patternAssertions) {
                const cas = astmgr.clone(ass);
                astmgr.replaceByMatchTable(cas, matched);
                this.assertUnwrap(cas, varTable);
            }
            if (nth === -1 || nth === result++) {
                // replace $s in replace param
                const replaced = astmgr.clone(replace);
                astmgr.replaceByMatchTable(replaced, matched);
                // assign to ast
                astmgr.assign(ast, replaced);
                // if (nth !== -1)
                return result; // if (nth !== -1), already replaced one, short circuit, if nth === -1, just replace outter layer to avoid loop
            }
        }
        catch (e) { /** if can't match, just ignore it **/ }
        if (!ast.nodes?.length)
            return result;
        for (let i = 0; i < ast.nodes.length; i++) {
            if ("E!V".includes(ast.name) && i === 0)
                continue; // ignore replacing var name by mistake
            result = this.matchSubAndReplace(ast.nodes[i], pattern, replace, nth, replNameReg, this.getSubAstType(ast, i, isItem), result, varTable);
        }
        return result;
    }
    // m: metarule
    // d: deduction
    // p: proposition or bool
    // v: variable
    // i: item
    checkGrammer(ast, type) {
        if (type === "v") {
            if (!this.getVarName(ast))
                throw TR(`表达式出现在了变量的位置中`);
        }
        if (ast.type === "meta") {
            if (ast.name === "⊢M")
                if (type !== "m")
                    throw TR("元推理符号⊢M只能出现在元推理规则中");
            if (ast.name === "⊢")
                if (type !== "d")
                    throw TR("推理符号⊢只能出现在推理规则中");
            if (ast.name !== "⊢" && ast.name !== "⊢M")
                throw TR("未知的推理符号 ") + ast.name;
            if (ast.nodes?.length !== 2)
                throw TR("元推理/推理符号子节点数目必须为2");
            const [cond, conc] = ast.nodes;
            if (cond.type !== "fn" || cond.name !== "#array")
                throw TR("元推理/推理符号的条件格式必须为数组");
            if (conc.type !== "fn" || conc.name !== "#array")
                throw TR("元推理/推理符号的结论格式必须为数组");
            if (ast.name === "⊢" && conc.nodes?.length !== 1)
                throw TR("推理符号的结论数必须为1");
            if (ast.name === "⊢M" && !conc.nodes?.length)
                throw TR("元推理符号的结论不能为空");
            if (type === "m")
                return; // skip metarule check: check it by hand
            if (cond.nodes?.length) {
                for (const cd of cond.nodes) {
                    try {
                        this.checkGrammer(cd, "p");
                    }
                    catch (e) {
                        throw TR(`条件中`) + e;
                    }
                }
            }
            for (const cc of conc.nodes) {
                try {
                    this.checkGrammer(cc, "p");
                }
                catch (e) {
                    throw TR(`结论中`) + e;
                }
            }
            return;
        }
        if (type === "m")
            throw TR("未找到元推理符号");
        if (type === "d")
            throw TR("未找到推理符号");
        if (ast.type === "sym") {
            if (ast.name === "{|") {
                if (type !== "i")
                    throw TR("意外出现集合表达式");
                this.checkGrammer(ast.nodes[0], "v");
                const varName = this.getVarName(ast.nodes[0]);
                if (this.isConst(varName)) {
                    throw TR(`常数符号`) + varName + TR('禁止出现在量词') + "{?@..| ... }" + TR('的约束变量中');
                }
                this.checkGrammer(ast.nodes[1], "i");
                this.checkGrammer(ast.nodes[2], "p");
                return;
            }
            else if (ast.name === "|}") {
                if (type !== "i")
                    throw TR("意外出现集合表达式");
                this.checkGrammer(ast.nodes[0], "v");
                const varName = this.getVarName(ast.nodes[0]);
                if (this.isConst(varName)) {
                    throw TR(`常数符号`) + varName + TR('禁止出现在量词') + "{ ... |?@..}" + TR('的约束变量中');
                }
                this.checkGrammer(ast.nodes[1], "i");
                this.checkGrammer(ast.nodes[2], "i");
                return;
            }
            else if (quantSyms.includes(ast.name)) {
                if (type !== "p")
                    return TR("意外出现了量词") + ast.name;
                const varName = this.getVarName(ast.nodes[0]);
                if (!varName)
                    throw TR(`非变量表达式出现在了量词`) + ast.name + TR(`的约束变量中`);
                if (this.isConst(varName)) {
                    throw TR(`常数符号`) + varName + TR('禁止出现在量词') + ast.name + TR('的约束变量中');
                }
                this.checkGrammer(ast.nodes[1], "p");
                return;
            }
            if (fnSyms.includes(ast.name)) {
                if (type !== "i")
                    throw TR("意外出现集合表达式");
                this.checkGrammer(ast.nodes[0], "i");
                this.checkGrammer(ast.nodes[1], "i");
                return;
            }
            if (verbSyms.includes(ast.name)) {
                if (type !== "p")
                    throw TR("意外出现谓词符号") + ast.name;
                this.checkGrammer(ast.nodes[0], "i");
                this.checkGrammer(ast.nodes[1], "i");
                return;
            }
            if (logicSyms.includes(ast.name)) {
                if (type !== "p")
                    throw TR("意外出现逻辑连词") + ast.name;
                this.checkGrammer(ast.nodes[0], "p");
                if (ast.nodes[1])
                    this.checkGrammer(ast.nodes[1], "p");
                return;
            }
        }
        if (ast.type === "fn") {
            if (ast.name === "#rp" || ast.name === "#crp") {
                if (ast.nodes?.length !== 3 && ast.nodes?.length !== 4)
                    throw TR('系统函数') + ast.name + TR(`的参数个数必须为三个或四个`);
                this.checkGrammer(ast.nodes[0], type);
                this.checkGrammer(ast.nodes[1], "i");
                this.checkGrammer(ast.nodes[2], "i");
                if (ast.nodes[3])
                    this.checkGrammer(ast.nodes[3], "v");
                return;
            }
            if (ast.name.match(/^#v*nf$/)) {
                if (!(ast.nodes?.length > ast.name.length - 2))
                    throw TR('系统函数') + ast.name + TR(`的参数个数必须至少有`) + (ast.name.length - 1) + TR(`个`);
                this.checkGrammer(ast.nodes[0], type);
                for (let i = 1; i < ast.nodes.length; i++) {
                    try {
                        this.checkGrammer(ast.nodes[i], "v");
                    }
                    catch (e) {
                        throw TR('系统函数') + ast.name + TR(`第${i + 1}个参数中：`) + e;
                    }
                }
                return;
            }
            if (ast.name === "Prime") {
                if (type !== "p")
                    throw TR("意外出现算数谓词表达式");
                if (ast.nodes?.length !== 1)
                    throw TR(`算数谓词 Prime 仅接受一个类型为项的参数`);
                for (const n of ast.nodes)
                    this.checkGrammer(n, "i");
                return;
            }
            if (ast.name === "Equiv") {
                if (type !== "p")
                    throw TR("意外出现双射谓词表达式");
                if (ast.nodes?.length !== 2)
                    throw TR(`双射谓词 Equiv 仅接受两个类型为项的参数`);
                for (const n of ast.nodes)
                    this.checkGrammer(n, "i");
                return;
            }
            if (ast.name === "Order" || ast.name === "WellOrder") {
                if (type !== "p")
                    throw TR("意外出现序关系谓词表达式");
                if (ast.nodes?.length !== 2)
                    throw TR(`序关系谓词${ast.name}仅接受两个类型为项的参数`);
                for (const n of ast.nodes)
                    this.checkGrammer(n, "i");
                return;
            }
            if (ast.name === "Rel") {
                if (type !== "p")
                    throw TR("意外出现二元关系谓词表达式");
                if (ast.nodes?.length !== 3)
                    throw TR(`二元关系谓词 Rel 仅接受3个类型为项的参数`);
                for (const n of ast.nodes)
                    this.checkGrammer(n, "i");
                return;
            }
            if (this.verbs.has(ast.name)) {
                if (type !== "p")
                    throw TR("意外出现谓词表达式");
                return;
            }
            if (this.fns.has(ast.name)) {
                if (type !== "i")
                    throw TR("意外出现集合表达式");
                for (const n of ast.nodes)
                    this.checkGrammer(n, "i");
                return;
            }
        }
        if (ast.type === "replvar" && this.isConst(ast.name)) {
            if (type === "p")
                throw TR("无法将集合常量符号“") + ast.name + TR("”作为原子公式符号");
            return;
        }
        // remained are unknown fns,  types in subnodes are items
        if (ast.nodes?.length) {
            for (const n of ast.nodes)
                this.checkGrammer(n, "i");
        }
    }
    isConst(name) {
        return this.consts.has(name) || name.match(/^[\-\+]?([0-9]|[1-9][0-9]+)(\.[0-9]*)?[qrc]?$/);
    }
    isNameQuantVarIn(name, ast) {
        if (this.getQuantParams(ast)) {
            if (name === this.getVarName(ast.nodes[0]))
                return true;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                if (this.isNameQuantVarIn(name, n))
                    return true;
            }
        }
        return false;
    }
    // if outter fn can't wrap, throw error
    assertUnwrap(ast, varTypes) {
        const nfp = this.getNfParams(ast);
        if (nfp) {
            for (const v of nfp[2]) {
                if (this.nf(v, nfp[0], nfp[1]) !== T)
                    throw TR(`变量`) + v + TR(`自由出现断言失败`);
            }
            return;
        }
        const crp = this.getCrpParams(ast);
        if (crp) {
            if (this.crp(...crp, varTypes) !== T)
                throw TR(`表达式可被替换断言失败`);
            return;
        }
        throw TR("未找到断言函数");
    }
}
//# sourceMappingURL=assertion.js.map