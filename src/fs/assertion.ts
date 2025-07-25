import { TR } from "../lang.js";
import { AST, ASTMgr } from "./astmgr.js";
const astmgr = new ASTMgr;
const logicSyms = ["<>", ">", "~", "&", "|"];
const quantSyms = ["E", "E!", "V"];
const verbSyms = ["@", "=", "<"];
const verbFns = ["Prime", "Equiv", "Order", "WellOrder", "Rel", "Point", "Line", "Plane", "Between", "Angle"];
const fnSyms = ["Pair", "Union", "Pow", "U", "I", "S", "+", "-", "*", "/"];

// type: item for true, boolean for false
export type ReplvarTypeTable = { [varname: string]: boolean };
import { type ReplvarMatchTable } from "./astmgr.js";

type bool3 = 0 | 1 | -1;
const T: bool3 = 1;
const F: bool3 = -1;
const U: bool3 = 0;

function not(b3: bool3): bool3 {
    return (-b3) as bool3;
}
function and(b1: bool3, b2: bool3): bool3 {
    if (b1 === T && b2 === T) return T;
    if (b1 === F) return F;
    if (b2 === F) return F;
    return U;
}
function or(b1: bool3, b2: bool3): bool3 {
    if (b1 === T) return T;
    if (b2 === T) return T;
    if (b1 === F && b2 === F) return F;
    return U;
}
function eq(name1: string, name2: string): bool3 {
    if (name1 === name2) return T;
    if (name1.match(/^\#/) || name2.match(/^\#/)) return F;
    if (name1.match(/^\$/) || name2.match(/^\$/)) return U;
    return F;
}

export class AssertionSystem {
    // if ast is var (with asserts) return name, else return false
    getVarName(ast: AST): string | false {
        if (ast.type === "replvar") return ast.name;
        const params = this.getNfParams(ast);
        if (params) {
            return this.getVarName(params[0]);
        }
        return false;
    }
    // if ast is fn #v*nf, return [subAst, quantsvars, nofreevars] else return false
    getNfParams(ast: AST): [AST, AST[], Set<string>] | false {
        if (ast.type !== "fn") return false;
        if (ast.name.match(/^#v*nf$/)) {
            const quants: AST[] = [];
            const vars = new Set<string>;
            let i = 1;
            for (; ast.name[i] === "v"; i++) {
                let repeated = false;
                for (const q of quants) {
                    if (astmgr.equal(q, ast.nodes[i])) {
                        repeated = true; break;
                    }
                }
                if (repeated) continue;
                quants.push(ast.nodes[i]);
            }
            for (; i < ast.nodes.length; i++) {
                vars.add(this.getVarName(ast.nodes[i]) as string);
            }
            return [ast.nodes[0], quants, vars];
        }
        return false;
    }
    getQuantParams(ast: AST): [AST, AST] | false {
        if (ast.type !== "sym") return false;
        if (quantSyms.includes(ast.name)) {
            return [ast.nodes[0], ast.nodes[1]];
        }
        return false;
    }
    getCrpParams(ast: AST): [AST, AST, AST, string | number, boolean] | false {
        if (ast.type !== "fn") return false;
        if (ast.name !== "#crp") return false; //todo: vcrp??
        let nth = ast.nodes[3]?.name;
        let newnth: number;
        if (isFinite(Number(nth))) newnth = Number(nth) - 1;
        let right = false;
        if (newnth < -1) {
            newnth = -(newnth + 2);
            right = true;
        }
        return [ast.nodes[0], ast.nodes[1], ast.nodes[2], nth ? (newnth ?? nth) : -1, right];
    }
    getRpParams(ast: AST): [AST, AST, AST, string | number, boolean] | false {
        if (ast.type !== "fn") return false;
        if (ast.name !== "#rp") return false;
        let nth = ast.nodes[3]?.name;
        let newnth: number;
        if (isFinite(Number(nth))) newnth = Number(nth) - 1;
        let right = false;
        if (newnth < -1) {
            newnth = -(newnth + 2);
            right = true;
        }
        return [ast.nodes[0], ast.nodes[1], ast.nodes[2], nth ? (newnth ?? nth) : -1, right];
    }
    // check if assertions can't be propagated into ast's children nodes
    ignorePropagateAst(ast: AST): boolean {
        if (!ast.nodes?.length) return true;
        if (quantSyms.includes(ast.name) && ast.type === "sym") return true;
        if (ast.type === "fn" && ast.name.startsWith("#")) return true;
        return false;
    }
    // return q1 < q2, regarding arrays q1 q2 as sets
    subsetQuants(q1: AST[], q2: AST[]): boolean {
        for (const x of q1) {
            let found = false;
            for (const y of q2) {
                if (astmgr.equal(x, y)) { found = true; break; }
            }
            if (!found) return false;
        }
        return true;
    }
    // remove all #fns, return the first child node
    removeFn(ast: AST) {
        if (ast.type !== "fn" && !ast.name.startsWith("#")) throw "can't remove function from non #fn ast";
        astmgr.assign(ast, ast.nodes[0]);
    }
    // wrap ast with #v*nf fn, without simplify
    addNf(ast: AST, qs: AST[], vs: Set<string>) {
        if (!vs.size) return;
        const nodes = [ast];
        for (let i = 0; i < qs.length; i++) {
            let repeated = false;
            const x = qs[i];
            for (let j = i + 1; j < qs.length; j++) {
                const y = qs[j];
                if (astmgr.equal(x, y)) { repeated = true; break; }
            }
            if (!repeated) nodes.push(x);
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
    // fussy check whether name is nofree in V* ast, exclusions can be provided for replvar name
    nf(name: string, ast: AST, quants: AST[] = [], nameIsNot?: Set<string>): bool3 {
        const astName = this.getVarName(ast);
        // ast is var
        if (ast.type === "replvar") {
            if (nameIsNot && nameIsNot.has(name)) return T;
            const isEq = eq(name, astName as string);
            if (isEq === F) return T;
            // if no quant
            if (!quants?.length) return not(isEq);
            // if quants
            let res = F;
            for (const q of quants) {
                res = or(res, not(this.nf(name, q)));
            }
            if (res === T) return T;
            if (res === F) return not(isEq);
            return U;
        }
        // ast is not var
        const quantParam = this.getQuantParams(ast);
        //ast is quant
        if (quantParam) {
            const [q, sub] = quantParam;
            return this.nf(name, sub, [q, ...quants])
        }
        const nfParams = this.getNfParams(ast);
        // ast is nf
        if (nfParams) {
            const [sub, sq, sv] = nfParams;
            if (this.subsetQuants(sq, quants)) {
                // n(V1V2 a;;c) > n(V1V2V3V4 a;;c) => n(a;1,2;c) > n(a;1,2,3,4;c)
                if (sv.has(name)) return T;
                return this.nf(name, sub, quants);
            }
            // todo: whether others can be determined?
            return U;
        }
        const ignore = this.ignorePropagateAst(ast);
        // ast is complex fns which cant be mapped in nor decided
        if (ignore) return U;
        // ast is logic symbol, can be mapped in
        let res = T;
        if (ast.nodes?.length) for (const n of ast.nodes) {
            const subB = this.nf(name, n, quants);
            if (subB === F) return F; // short circuit for "and"
            res = and(res, subB);
        }
        return res;
    }
    // fussy check for #crp (can replace), varTypes is provided outside
    // if nth === -1, replace all
    crp(ast: AST, src: AST, dst: AST, nth: string | number, right: boolean, varTypes: ReplvarTypeTable): bool3 {
        if (typeof nth === "string" && !nth.match(/^\$/)) throw TR(`替换表达式中指定的匹配序号`) + nth + TR('必须为整数');
        if (typeof nth === "number" && Math.floor(nth) !== nth) throw TR("替换表达式中指定的匹配序号") + nth + TR('必须为整数');
        // item always can be replaced, so no need to check ast == src situation 
        if (this.getAstType(ast, varTypes)) return T;
        // if src=dst, id T
        if (this.astEq(src, dst) === T) return T;
        // todo: verify: if contains assertions, just match them exactly is ok?
        const scopes = this.getSubAstMatchTimes(ast, src, Number(nth), dst, undefined, undefined, right);
        if (!scopes) return U; // can't decide
        for (const [idx, scope] of scopes.entries()) {
            // if not match all, just verify nth
            if (typeof nth === "number") {
                if (nth !== -1 && idx !== nth) continue;
                if (nth > idx) break; // short circuit
            }
            let AllF = true;
            let res = T;
            for (const bv of scope) {
                const bvName = this.getVarName(bv) as string;
                const bvIsNot = this.getVarIsNotList(bv)
                const nf = this.nf(bvName, dst, [], bvIsNot);
                res = and(res, nf);
                if (res !== F) AllF = false;
            }
            if (typeof nth === "number") {
                return res;
            } else {
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
    getReplVarsType(ast: AST, res: ReplvarTypeTable = {}, isItem: boolean): ReplvarTypeTable {
        if (ast.type === "replvar") {
            res[ast.name] ??= isItem;
            if (res[ast.name] !== isItem) throw TR(`变量`)+ast.name+TR('不能同时为项和公式');
            return res;
        }
        for (const [idx, n] of ast.nodes.entries()) {
            this.getReplVarsType(n, res, this.getSubAstType(ast, idx, isItem));
        }
        return res;
    }

    // return ast's type (item for true, boolean for false)
    getAstType(ast: AST, varLists: ReplvarTypeTable): boolean {
        if (ast.type === "replvar") {
            const v = varLists[ast.name];
            if (v === true) return true;
            if (v === false) return false;
            throw "cannot reached";
        }
        if (ast.type === "sym") {
            if (logicSyms.includes(ast.name)) return false;
            if (quantSyms.includes(ast.name)) return false;
            return true;
        }
        if (ast.type === "fn") {
            if (ast.name.match(/^#v*nf/) || ast.name.match(/^#c?rp/)) {
                return this.getAstType(ast.nodes[0], varLists);
            }
        }
    }
    // if replvar is ast with nf assertions, get excluded values for this replvar
    getVarIsNotList(varAst: AST, isNot: Set<string> = new Set) {
        if (varAst.type === "replvar") return isNot;
        const nfp = this.getNfParams(varAst);
        if (!nfp) return isNot;
        this.getVarIsNotList(nfp[0], isNot);
        if (!nfp[1]?.length) {
            for (const n of nfp[2]) isNot.add(n);
        }
        return isNot;
    }
    // fussy eq
    astEq(ast1: AST, ast2: AST): bool3 {
        if (astmgr.equal(ast1, ast2)) return T;
        if (ast1.type === "replvar" && ast2.type === "replvar") {
            return eq(ast1.name, ast2.name);
        }
        if (ast1.type !== "replvar" && ast2.type !== "replvar") {
            if (ast1.name !== ast2.name) return F;
            if (ast1.nodes?.length !== ast2.nodes?.length) return F;
            if (!ast1.nodes) return T;
            let res = T;
            for (let i = 0; i < ast1.nodes.length; i++) {
                const subres = this.astEq(ast1.nodes[i], ast2.nodes[i]);
                if (subres === F) return F;
                res = and(res, subres);
            }
            return res;
        }
        if (ast1.type === "replvar") {
            if (ast1.name.match(/^\$/)) {
                // $1 = $2+$3 : U
                const subReplvars = (this.getVarNamesAndIsNots(ast2, {}, /^\$/));
                // $1 = $2+$1 : F
                if (subReplvars[ast1.name]) return F;
                // $1 = $2($1) : F
                if (this.nf(ast1.name, ast2) === U) return U;
                return F;
            }
            // x = $1+$2
            return F;
        }
        if (ast2.type === "replvar") {
            if (ast2.name.match(/^\$/)) {
                const subReplvars = (this.getVarNamesAndIsNots(ast1, {}, /^\$/));
                if (subReplvars[ast2.name]) return F;
                if (this.nf(ast2.name, ast1) === U) return U;
                return F;
            }
            return F;
        }
    }
    getVarNamesAndIsNots(ast: AST, res: { [name: string]: Set<string> }, reg: RegExp, scope: Set<string> = new Set): { [name: string]: Set<string> } {
        const varname = this.getVarName(ast);
        if (varname) {
            if (!varname.match(reg)) return res;
            res[varname] = this.getVarIsNotList(ast, res[varname]);
            for (const s of scope) res[varname].add(s);
            return res;
        }
        const nfp = this.getNfParams(ast);
        if (nfp) {
            if (!nfp[1].length) { // if nf with no quant
                for (const s of nfp[2]) scope.add(s);
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
        if (ast.nodes) for (const n of ast.nodes) {
            this.getVarNamesAndIsNots(n, res, reg, new Set(scope));
        }
        return res;
    }
    // fussy search if subast exist in ast
    // return  matched positions's scopes, false if unknown
    getSubAstMatchTimes(
        ast: AST, subAst: AST, nth: number, dst: AST, scope: AST[] = [], res: AST[][] = [], right?: boolean
    ): AST[][] | false {
        if (scope.length) {
            const vars = this.getVarNamesAndIsNots(subAst, {}, null);
            for (const [v, vIsNot] of Object.entries(vars)) {
                for (const bv of scope) {
                    const nf = this.nf(v, bv, [], vIsNot);
                    if (nf === F) return res; // can't match any bounded vars
                    if (nf === U) return false; // can't decided
                }
            }
        }
        const eq = this.astEq(ast, subAst);
        if (eq === T) { res.push(scope); return res; } // matched whole ast one time
        if (eq === U) {
            if (nth === -1 && (this.astEq(ast, dst))) return res;
            return false; // unknown
        }
        // else not equal
        if (!ast.nodes?.length) return res; // end of node, find 0
        const qp = this.getQuantParams(ast);
        if (qp) {
            // can't find free y in Vy:xxx
            if (qp[0].name === subAst.name && subAst.type === "replvar") return res;
            scope.push(qp[0]);
            return this.getSubAstMatchTimes(qp[1], subAst, nth, dst, scope, res, right);
        }
        if (right) {
            for (let n = ast.nodes.length - 1; n >= 0; n--) {
                const result = this.getSubAstMatchTimes(ast.nodes[n], subAst, nth, dst, scope.slice(0), res, right);
                // if found exact nth
                if (nth !== -1 && res.length === nth + 1) return res;
                // unknown spread
                if (result === false) return false;
            }
        }
        for (const n of ast.nodes) {
            // unknown spread
            if (this.getSubAstMatchTimes(n, subAst, nth, dst, scope.slice(0), res, right) === false) return false;
        }
        return res;
    }
    getSubAstMatchTimesAndReplace(
        ast: AST, subAst: AST, newAst: AST, nth: number, scope: AST[] = [], res: AST[][] = [], right: boolean
    ): AST[][] | false {
        if (nth !== -1 && nth < res.length) return res; // completed, this short circuit is neccesary for later unknown $s 
        if (scope.length) {
            const vars = this.getVarNamesAndIsNots(subAst, {}, null);
            for (const [v, vIsNot] of Object.entries(vars)) {
                for (const bv of scope) {
                    const nf = this.nf(v, bv, [], vIsNot);
                    if (nf === F) return res; // can't match any bounded vars
                    if (nf === U) return false; // can't decided
                }
            }
        }
        // x=x, x->y, 1

        const eq = this.astEq(ast, subAst);
        if (eq === T) {
            // here replace happens
            if (nth === res.length || nth === -1) { astmgr.assign(ast, newAst); }
            res.push(scope);
            return res;
        } // matched whole ast one time
        if (eq === U) {
            if (nth === -1 && this.astEq(ast, newAst)) return res;
            return false; // unknown
        }
        // else not equal
        if (!ast.nodes?.length) return res; // end of node, find 0
        const qp = this.getQuantParams(ast);
        if (qp) {
            if (nth === -1) {
                const bounded = this.astEq(qp[0], subAst);
                if (bounded === T) return res; // can't match bounded var
                if (bounded === U) return false;
            }
            scope.push(qp[0]);
            return this.getSubAstMatchTimesAndReplace(qp[1], subAst, newAst, nth, scope, res, right);
        }
        if (right) {
            for (let n = ast.nodes.length - 1; n >= 0; n--) {
                const subres = this.getSubAstMatchTimesAndReplace(ast.nodes[n], subAst, newAst, nth, scope.slice(0), res, right);
                // if unknown, don't spread, just ignore it and replace??
                if (subres === false) return false;
            }
        }
        for (const n of ast.nodes) {
            const subres = this.getSubAstMatchTimesAndReplace(n, subAst, newAst, nth, scope.slice(0), res, right);
            // if unknown, don't spread, just ignore it and replace??
            if (subres === false) return false;
        }
        return res;
    }
    // only according to ast's structure, give its nth child's type
    // this is a helper fn for recursively check sub nodes
    getSubAstType(ast: AST, idx: number, parentType: boolean) {
        if (ast.type === "sym") {
            if (quantSyms.includes(ast.name)) return idx === 0;
            return !logicSyms.includes(ast.name);
        }
        if (ast.type === "fn") {
            if (verbFns.includes(ast.name)) {
                return true;
            }
            if (ast.name.match(/^#v*nf/) || ast.name.match(/^#c?rp/)) {
                // #v*nf( isItem, true, true ....);
                // #c?rp( isItem, true, true ....);
                return idx === 0 ? parentType : true;
            }
            return parentType;
        }
    }
    // remove all assert fns without checkments
    unwrapAssertions(ast: AST) {
        if (ast.type === "replvar") return;
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
    expand(ast: AST, isItem: boolean, varLists?: ReplvarTypeTable) {
        // astmgr.assign(ast,astmgr.clone(ast)); // avoid inner inter refering
        varLists ??= this.getReplVarsType(ast, {}, isItem);
        // first, check all subnodes are consist and expand them
        if (ast.nodes?.length) {
            for (const [idx, n] of ast.nodes.entries()) {
                this.expand(n, this.getSubAstType(ast, idx, isItem), varLists);
            }
        }
        // ast is atomvar
        if (ast.type === "replvar") return;
        const nfParams = this.getNfParams(ast);
        // ast is nf
        if (nfParams) {
            let [sub, quants, vars] = nfParams;
            // self check
            for (const v of vars) {
                let res = this.nf(v, sub, quants);
                if (res === T) vars.delete(v);
                if (res === F) throw TR("断言失败：变量") + v + TR("自由出现");
            }
            // then check if quants can be eliminated
            const toRemove = [];
            for (const q of quants) {
                let allNotEq = true;
                for (const v of vars) {
                    if (this.nf(v, q) !== T) { allNotEq = false; break; }
                }
                if (allNotEq) toRemove.push(q);
            }
            quants = quants.filter(q => !toRemove.includes(q));
            this.removeFn(ast); sub = ast;
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
                } else if (this.subsetQuants(quants, sq)) {
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
            const ignore = this.ignorePropagateAst(sub);
            // sub is complex fns which cant be mapped in nor decided
            if (ignore) {
                this.addNf(ast, quants, vars);
                return;
            }
            // nf(a>b) => nf(a) > nf(b)
            const subAstType = this.getSubAstType(ast, 0, isItem); // all same, just give 0
            if (sub.nodes?.length) for (const n of sub.nodes) {
                this.addNf(n, quants, vars);
                this.expand(n, subAstType, varLists);
            }
        }
        const crpParams = this.getCrpParams(ast);
        // ast is crp
        if (crpParams) {
            const tf = this.crp(...crpParams, varLists);
            if (tf === T) this.removeFn(ast);
            if (tf === F) throw TR("断言失败：#crp执行替换后自由变量将被量词约束");
            // todo
        }
        const rpParams = this.getRpParams(ast);
        // ast is rp
        if (rpParams) {
            const [sub, src, dst, nth, right] = rpParams;
            const tf = this.crp(sub, src, dst, nth, right, varLists);
            if (tf === F) throw TR("函数#rp执行失败：自由变量将被量词约束");
            if (this.astEq(src, dst) === T) { this.removeFn(ast); return; } // id
            if (tf === U) {
                return; // can't expand, keep it
            }
            const eq = this.astEq(sub, src);
            if (eq === T) { astmgr.assign(ast, dst); return; } // exact match, todo: nth
            if (eq === U) return;
            if (typeof nth === "string") return;
            if (this.getSubAstMatchTimesAndReplace(sub, src, dst, nth, undefined, undefined, right)) {
                astmgr.assign(ast, sub); // unwrap
            };
            // else keep #rp
        }
    }
    // replNameReg: rule for replace var
    match(ast: AST, pattern: AST, replNameReg: RegExp, isItem: boolean, result: ReplvarMatchTable, varTable: ReplvarTypeTable, assertions: AST[]) {
        if (pattern.type === "replvar" && pattern.name.match(replNameReg)) {
            result[pattern.name] ??= ast;
            this.getReplVarsType(ast, varTable, isItem);
            if (!astmgr.equal(result[pattern.name], ast)) throw TR(`模式匹配失败：匹配多个替代变量`)+pattern.name+TR(`时值不相同`);
            return;
        }
        if (pattern.type === "fn" && pattern.name.match(/^#(v*nf|crp)/)) {
            this.match(ast, pattern.nodes[0], replNameReg, isItem, result, varTable, assertions);
            // ignore assertions, but collect them for later check
            assertions.push(astmgr.clone(pattern));
            return;
        }
        if (ast.type !== pattern.type || ast.name !== pattern.name) throw TR("模式匹配失败");
        if (ast.nodes?.length !== pattern.nodes?.length) throw TR("模式匹配失败");
        if (ast.nodes?.length) {
            for (let i = 0; i < ast.nodes.length; i++) {
                this.match(ast.nodes[i], pattern.nodes[i], replNameReg, this.getSubAstType(ast, i, isItem), result, varTable, assertions);
            }
        }
    }
    // match sub exactly and replace without fussy booleans, return total matched counts
    matchSubAndReplace(ast: AST, pattern: AST, replace: AST, nth: number, replNameReg: RegExp, isItem: boolean, result: number, varTable: ReplvarTypeTable): number {
        if (nth >= 0 && !(result <= nth)) return result;
        try {
            // match root ast
            const matched = {}
            const assertions = [];
            this.match(ast, pattern, replNameReg, isItem, matched, varTable, assertions);
            for (const ass of assertions) {
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
        } catch (e) { /** if can't match, just ignore it **/ }
        if (!ast.nodes?.length) return result;
        for (let i = 0; i < ast.nodes.length; i++) {
            if ("E!V".includes(ast.name) && i === 0) continue; // ignore replacing var name by mistake
            result = this.matchSubAndReplace(ast.nodes[i], pattern, replace, nth, replNameReg, this.getSubAstType(ast, i, isItem), result, varTable);
        }
        return result;
    }

    // m: metarule
    // d: deduction
    // p: proposition or bool
    // v: variable
    // i: item
    checkGrammer(ast: AST, type: "m" | "d" | "p" | "v" | "i", consts: Set<string>) {
        if (type === "v") {
            if (!this.getVarName(ast)) throw TR(`表达式出现在了变量的位置中`);
        }
        if (ast.type === "meta") {
            if (ast.name === "⊢M") if (type !== "m") throw TR("元推理符号⊢M只能出现在元推理规则中");
            if (ast.name === "⊢") if (type !== "d") throw TR("推理符号⊢只能出现在推理规则中");
            if (ast.name !== "⊢" && ast.name !== "⊢M") throw TR("未知的推理符号 ") + ast.name;
            if (ast.nodes?.length !== 2) throw TR("元推理/推理符号子节点数目必须为2");
            const [cond, conc] = ast.nodes;
            if (cond.type !== "fn" || cond.name !== "#array") throw TR("元推理/推理符号的条件格式必须为数组");
            if (conc.type !== "fn" || conc.name !== "#array") throw TR("元推理/推理符号的结论格式必须为数组");
            if (ast.name === "⊢" && conc.nodes?.length !== 1) throw TR("推理符号的结论数必须为1");
            if (ast.name === "⊢M" && !conc.nodes?.length) throw TR("元推理符号的结论不能为空");
            if (type === "m") return; // skip metarule check: check it by hand
            if (cond.nodes?.length) {
                for (const cd of cond.nodes) {
                    try {
                        this.checkGrammer(cd, "p", consts);
                    } catch (e) { throw TR(`条件中`) + e; }
                }
            }
            for (const cc of conc.nodes) {
                try {
                    this.checkGrammer(cc, "p", consts);
                } catch (e) { throw TR(`结论中`) + e; }
            }
            return;
        }
        if (type === "m") throw TR("未找到元推理符号"); if (type === "d") throw TR("未找到推理符号");
        if (ast.type === "sym") {
            if (quantSyms.includes(ast.name)) {
                if (type !== "p") return TR("意外出现了量词") + ast.name;
                const varName = this.getVarName(ast.nodes[0]);
                if (!varName) throw TR(`非变量表达式出现在了量词`) + ast.name + TR(`的约束变量中`);
                if (consts.has(varName)) {
                    throw TR(`常数符号`)+varName+TR('禁止出现在量词')+ast.name+TR('的约束变量中');
                }
                this.checkGrammer(ast.nodes[1], "p", consts);
                return;
            }
            if (fnSyms.includes(ast.name)) {
                if (type !== "i") throw TR("意外出现集合表达式");
                this.checkGrammer(ast.nodes[0], "i", consts);
                this.checkGrammer(ast.nodes[1], "i", consts);
                return;
            }
            if (verbSyms.includes(ast.name)) {
                if (type !== "p") throw TR("意外出现谓词符号") + ast.name;
                this.checkGrammer(ast.nodes[0], "i", consts);
                this.checkGrammer(ast.nodes[1], "i", consts);
                return;
            }
            if (logicSyms.includes(ast.name)) {
                if (type !== "p") throw TR("意外出现逻辑连词") + ast.name;
                this.checkGrammer(ast.nodes[0], "p", consts);
                if (ast.nodes[1]) this.checkGrammer(ast.nodes[1], "p", consts);
                return;
            }
        }
        if (ast.type === "fn") {
            if (ast.name === "#rp" || ast.name === "#crp") {
                if (ast.nodes?.length !== 3 && ast.nodes?.length !== 4) throw TR('系统函数')+ast.name+TR(`的参数个数必须为三个或四个`);
                this.checkGrammer(ast.nodes[0], type, consts);
                this.checkGrammer(ast.nodes[1], "i", consts);
                this.checkGrammer(ast.nodes[2], "i", consts);
                if (ast.nodes[3]) this.checkGrammer(ast.nodes[3], "v", consts);
                return;
            }
            if (ast.name.match(/^#v*nf$/)) {
                if (!(ast.nodes?.length > ast.name.length - 2)) throw TR('系统函数')+ast.name+TR(`的参数个数必须至少有`)+(ast.name.length - 1)+TR(`个`);
                this.checkGrammer(ast.nodes[0], type, consts);
                for (let i = 1; i < ast.nodes.length; i++) {
                    try {
                        this.checkGrammer(ast.nodes[i], "v", consts);
                    } catch (e) {
                        throw TR('系统函数')+ast.name+TR(`第${i + 1}个参数中：`)+e;
                    }
                }
                return;
            }
            if (ast.name === "Prime") {
                if (type !== "p") throw TR("意外出现算数谓词表达式");
                if (ast.nodes?.length !== 1) throw TR(`算数谓词 Prime 仅接受一个类型为项的参数`);
                for (const n of ast.nodes) this.checkGrammer(n, "i", consts);
                return;
            }
            if (ast.name === "Equiv") {
                if (type !== "p") throw TR("意外出现双射谓词表达式");
                if (ast.nodes?.length !== 2) throw TR(`双射谓词 Equiv 仅接受两个类型为项的参数`);
                for (const n of ast.nodes) this.checkGrammer(n, "i", consts);
                return;
            }
            if (ast.name === "Order" || ast.name === "WellOrder") {
                if (type !== "p") throw TR("意外出现序关系谓词表达式");
                if (ast.nodes?.length !== 2) throw TR(`序关系谓词${ast.name}仅接受两个类型为项的参数`);
                for (const n of ast.nodes) this.checkGrammer(n, "i", consts);
                return;
            }
            if (ast.name === "Rel") {
                if (type !== "p") throw TR("意外出现二元关系谓词表达式");
                if (ast.nodes?.length !== 3) throw TR(`二元关系谓词 Rel 仅接受3个类型为项的参数`);
                for (const n of ast.nodes) this.checkGrammer(n, "i", consts);
                return;
            }
            if (fnSyms.includes(ast.name)) {
                if (type !== "i") throw TR("意外出现集合表达式");
                for (const n of ast.nodes) this.checkGrammer(n, "i", consts);
                return;
            }
        }
        if (ast.type === "replvar" && consts.has(ast.name)) {
            if (type === "p") throw TR("无法将集合常量符号“") + ast.name + TR("”作为原子公式符号");
            return;
        }
        // remained are unknown fns, keep type in subnodes
        if (ast.nodes?.length) {
            for (const n of ast.nodes) this.checkGrammer(n, type, consts);
        }
    }
    isNameQuantVarIn(name: string, ast: AST) {
        if (this.getQuantParams(ast)) {
            if (name === this.getVarName(ast.nodes[0])) return true;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                if (this.isNameQuantVarIn(name, n)) return true;
            }
        }
        return false;
    }
    // if outter fn can't wrap, throw error
    assertUnwrap(ast: AST, varTypes: ReplvarTypeTable) {
        const nfp = this.getNfParams(ast);
        if (nfp) {
            for (const v of nfp[2]) {
                if (this.nf(v, nfp[0], nfp[1]) !== T) throw TR(`变量`)+v+TR(`自由出现断言失败`);
            }
            return;
        }
        const crp = this.getCrpParams(ast);
        if (crp) {
            if (this.crp(...crp, varTypes) !== T) throw TR(`表达式可被替换断言失败`);
            return;
        }
        throw TR("未找到断言函数");
    }
}