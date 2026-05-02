import { TR } from "../lang.js";
import { ASTParser, AST } from "./astparser.js";
const parser = new ASTParser;

// sugars begin

export function wrapVar(v: string): AST {
    return { type: "var", name: v };
}
function wrapU(v: string): AST {
    return { type: "apply", name: "", nodes: [wrapVar("U"), wrapVar(v)] };
}
export function wrapLambda(type: string, param: string, paramType: AST, body: AST): AST {
    return { type, name: param, nodes: [paramType, body] };
}
export function wrapApply(...terms: AST[]): AST {
    let ast = terms.shift();
    let ast1: AST;
    while (ast1 = terms.shift()) {
        ast = { type: "apply", name: "", nodes: [ast, ast1] };
    }
    return ast;
}
export type Varlist = {
    [varname: string]: AST,
}
export type Context = [string, AST, number][];

export class InferTable {
    list: Map<string, Context> = new Map;
    rel: Varlist = {};
    solved = new Set<string>;
    // find new name, and add it to list. param is just a ref value for finding
    addNewName(n = 0, ctxt: Context) {
        if (!n) n = 0;
        while (this.list.has(String(n++)));
        const name = String(n - 1);
        this.list.set(name, ctxt);
        if (name === "10") {
            console.log("hqho");
        }
        return name;
    }
    clone(): InferTable {
        const n = new InferTable;
        n.list = new Map(this.list);
        n.rel = Object.fromEntries(Object.entries(this.rel).map(([k, v]) => {
            const nv = Core.clone(v, true);
            nv.origin = v.origin;
            nv["desugared"] = v["desugared"];
            if (typeof nv.origin === "object") nv.origin = Core.clone(nv.origin, true);
            return [k, nv];
        }));
        n.solved = new Set(this.solved);
        return n;
    }
    constructor(ast?: AST) {
        if (ast) this.findInferVal(ast);
    }
    private findInferVal(ast: AST, context = []) {
        if (ast.name?.[0] === "?") {
            this.list.set(ast.name.replace(/^\?([^\:]+)\:*$/, "$1"), context);
        }
        if (ast.type === "P" || ast.type === "S" || ast.type === "L") {
            return this.findInferVal(ast.nodes[1], assignContext([ast.name, ast.nodes[0], ast.bondVarId], context));
        }
        if (ast.nodes) {
            for (const n of ast.nodes) {
                this.findInferVal(n, context);
            }
        }
    }
}

// for finding bondvars
class DisjointSet {
    private parent: Map<number, number>;
    private size: Map<number, number>;
    constructor() {
        this.parent = new Map<number, number>();
        this.size = new Map<number, number>();
    }
    clone() {
        const n = new DisjointSet;
        n.parent = new Map(this.parent);
        n.size = new Map(this.size);
        return n;
    }
    add(x: number): void {
        if (!this.parent.has(x)) {
            this.parent.set(x, x);
            this.size.set(x, 1);
        }
    }
    find(x: number): number {
        if (!this.parent.has(x)) {
            this.add(x);
            return x;
        }
        const p = this.parent.get(x);
        if (p !== x) {
            const root = this.find(p);
            this.parent.set(x, root);
            return root;
        }
        return x;
    }
    union(x: number, y: number): void {
        const rootX = this.find(x);
        const rootY = this.find(y);
        if (rootX === rootY) {
            return;
        }
        const sizeX = this.size.get(rootX);
        const sizeY = this.size.get(rootY);
        if (sizeX < sizeY) {
            this.parent.set(rootX, rootY);
            this.size.set(rootY, sizeX + sizeY);
            this.size.delete(rootX);
        } else {
            this.parent.set(rootY, rootX);
            this.size.set(rootX, sizeX + sizeY);
            this.size.delete(rootY);
        }
    }
    eq(x: number, y: number): boolean {
        return this.find(x) === this.find(y);
    }
}

type State = {
    /** system prime constants and their types */
    sysTypes: Varlist;
    /** system defined constants and their values */
    sysDefs: Varlist;
    /** user defined constants and their values */
    userDefs: Varlist;
    /** all compute rules here, e.g. { "indnat": {pattern:["_","#C","#0","#succ","succ #n"],result:"#succ #n (indnat #C #0 #succ #n)"} } */
    computeRules: { [ctor: string]: { pattern: AST[], result: AST }[] };
    /**  */
    inferTable: InferTable;
    bondVarId: number;
    bondVarRel: DisjointSet;
    /** errormsg in ast tree */
    errormsg: { ast: AST, msg: string }[];
    disableSimpleFn?: boolean;
}
/** return a cloned Context */
export function assignContext(added: [string, AST, number], oldContext: Context) {
    const n = oldContext.slice(0);
    n.unshift(added);
    return n;
}

export class Core {
    static assign(ast: AST, value: AST, moveSemantic?: boolean) {
        const v = moveSemantic ? value : this.clone(value);
        ast.type = v.type;
        ast.name = v.name;
        ast.nodes = v.nodes;
        ast.checked = v.checked;
        ast.bondVarId = v.bondVarId;
    }
    static match(ast: AST, pattern: AST, regexp: RegExp, res: { [variable: string]: AST } = {}) {
        if (pattern.type === "var" && pattern.name.match(regexp)) {
            res[pattern.name] ??= ast;
            if (!this.exactEqual(ast, res[pattern.name])) return null;
            return res;
        }
        if (NatLiteral.is(ast) && pattern.nodes?.[0].name === "succ") {
            if (ast.name !== "0") return this.match(
                wrapVar(String(BigInt(ast.name) - 1n)), pattern.nodes[1], regexp, res
            );
        }
        if (ast.type !== pattern.type) return null;
        if (ast.nodes?.length !== pattern.nodes?.length) return null;
        if (ast.nodes?.length) {
            for (let i = 0; i < ast.nodes.length; i++) {
                if (!this.match(ast.nodes[i], pattern.nodes[i], regexp, res)) return null;
            }
        }
        if (ast.name !== pattern.name) return null;
        return res;
    }
    static clone(ast: AST, cloneChecked?: boolean): AST {
        const checked = (cloneChecked && ast.checked) ? this.clone(ast.checked) : null;
        const newast: AST = {
            type: ast.type, name: ast.name, checked, err: ast.err, bondVarId: ast.bondVarId
        };
        if (ast.nodes) {
            newast.nodes = ast.nodes.map(p => this.clone(p, cloneChecked));
        }
        return newast;
    }
    static replaceByMatch(ast: AST, res: Varlist, regexp: RegExp): boolean {
        if (!res) throw TR("未匹配");
        if (!ast) return; // here not panic because aftercheck need it
        if (ast.type === "var" && ast.name.match(regexp)) {
            if (!res[ast.name]) return false;
            this.assign(ast, this.clone(res[ast.name]));
            return true;
        } else if (ast.nodes?.length) {
            let modified = false;
            for (const n of ast.nodes) {
                if (this.replaceByMatch(n, res, regexp)) modified = true;
            }
            return modified;
        }
    }
    static cloneContext(c: Context): Context {
        return c.map(e => [e[0], this.clone(e[1]), e[2]]);
    }
    hasBondVar(ast: AST, id: number) {
        if (ast.type === "var") {
            if (ast.name === "_" && ast.checked?.type === ":") {
                return this.hasBondVar(ast.checked.nodes[0], id);
            }
            return this.isBondVarIdEqual(ast.bondVarId, id);
        } else if (ast.nodes?.length === 2) {
            return this.hasBondVar(ast.nodes[0], id) || this.hasBondVar(ast.nodes[1], id);
        }
    }
    hasInferVar(ast: AST, name: string) {
        if (ast.type === "var") {
            return ast.name === name;
        } else if (ast.nodes?.length === 2) {
            return this.hasInferVar(ast.nodes[0], name) || this.hasInferVar(ast.nodes[1], name);
        }
    }
    // give L/P/S new ids in an ast which is already marked (this is to solve bug for reducing ind_nat for succ)
    remarkLambdaBondIds(ast: AST, context: Context) {
        if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            const old = ast.bondVarId; ast.bondVarId = 0;
            const n = this.getBondVarId(ast);
            const v = wrapVar(ast.name); v.bondVarId = n; v.checked = ast.checked;
            this.replaceVar(ast.nodes[1], ast.name, old, v, context);
            this.remarkLambdaBondIds(ast.nodes[0], context);
            this.remarkLambdaBondIds(ast.nodes[1], assignContext([ast.name, ast.nodes[0], ast.bondVarId], context));
        } else if (ast.nodes?.length === 2) {
            this.remarkLambdaBondIds(ast.nodes[0], context);
            this.remarkLambdaBondIds(ast.nodes[1], context);
        }
        return ast;
    }
    // mark bonvar ids for an ast
    markBondVars(ast: AST, context: Context) {
        if (ast.type === "var") {
            if (ast.bondVarId) return ast;
            ast.bondVarId = context.find(e => e[0] === ast.name)?.[2];
        } else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            if (ast.bondVarId) return ast;
            this.getBondVarId(ast);
            if (ast.name === "_") ast.name = "*" + ast.bondVarId;
            this.markBondVars(ast.nodes[0], context);
            this.markBondVars(ast.nodes[1], assignContext([ast.name, ast.nodes[0], ast.bondVarId], context));
        } else if (ast.nodes?.length === 2) {
            this.markBondVars(ast.nodes[0], context);
            this.markBondVars(ast.nodes[1], context);
        }
        return ast;
    }
    // we didnt mark bondvar's with id, need do it
    getBondVarId(ast: AST) {
        if (ast.bondVarId) return ast.bondVarId;
        ast.bondVarId = this.state.bondVarId++;
        return ast.bondVarId;
    }
    mergeBondVarId(m: number, n: number) {
        this.state.bondVarRel.union(m, n);
    }
    isBondVarIdEqual(m: number, n: number) {
        return m && this.state.bondVarRel.eq(m, n);
    }
    // return whether ast has changed 
    // if bondvarId == -1, it will exact match name, e.g. inferval
    replaceVar(ast: AST, name: string, bondvarId: number, dst: AST, context?: Context): boolean {
        if (name === "_") return false;
        if (ast.checked) this.replaceVar(ast.checked, name, bondvarId, dst, context);
        if (ast.type === "var") {
            // x[y->_] -> x
            // naive approach: if (ast.name !== name) return false; this cannot deal with alpha conversion
            if (bondvarId === -1 ? ast.name !== name : !this.isBondVarIdEqual(ast.bondVarId, bondvarId)) return false;
            // x[x->_] -> _
            Core.assign(ast, dst); if (dst.checked) ast.checked = Core.clone(dst.checked); return true;
        } else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            // replace node[0] type first : #rp(Lx:A,...) -> Lx:#rp(A), ...
            const head = this.replaceVar(ast.nodes[0], name, bondvarId, dst, context);
            // (Lx.x)[x->_] = (Lx.x) not changed
            // if (ast.name === name) return head;// bounded
            return this.replaceVar(ast.nodes[1], name, bondvarId, dst, context) || head;
        } else if (ast.nodes?.length === 2) {
            const a = this.replaceVar(ast.nodes[0], name, bondvarId, dst, context);
            const b = this.replaceVar(ast.nodes[1], name, bondvarId, dst, context);
            return a || b;
        }
        return false;
    }
    state: State = {
        sysTypes: {
            "U@": wrapVar("U@:"),
            "U@:": wrapVar("U@:"),
            "@max": parser.parse("U@->U@->U@"),
            "@succ": parser.parse("U@->U@"),
        },
        bondVarId: 1,
        bondVarRel: null,
        sysDefs: {},
        userDefs: {},
        computeRules: {},
        inferTable: null,
        errormsg: []
    };
    cloneState(): State {
        return {
            sysTypes: this.state.sysTypes,
            bondVarId: this.state.bondVarId,
            bondVarRel: this.state.bondVarRel?.clone(),
            sysDefs: this.state.sysDefs,
            userDefs: this.state.userDefs,
            computeRules: this.state.computeRules,
            inferTable: this.state.inferTable?.clone(),
            errormsg: this.state.errormsg
        }
    }
    clearState() {
        this.state.errormsg = [];
        this.state.inferTable = new InferTable;
        this.state.bondVarId = 1;
        this.state.bondVarRel = new DisjointSet();
    }
    error(ast: AST, msg: any, stop: boolean) {
        this.state.errormsg.push({ ast, msg });
        console.log(parser.stringify(ast), msg);
        ast.err = msg;
        if (stop) throw msg;
    }
    checkType(ast: AST, context: Context, allowModify: boolean) {
        let errmsg: any;
        this.state.errormsg = [];
        this.state.inferTable = new InferTable(ast);
        this.state.bondVarId = 1;
        this.state.bondVarRel = new DisjointSet();
        // mark if context is not marked
        if (context.length) context = Core.cloneContext(context);
        for (let i = context.length - 1; i >= 0; i--) {
            const [e, t, id] = context[i];
            if (!id) context[i][2] = this.state.bondVarId++;
            context[i][1] = this.markBondVars(this.desugar(t, false), context.slice(i));
        }
        ast = this.markBondVars(this.desugar(ast, allowModify), context);
        const checkTypeIs = (ast: AST) => {
            const type = this.check(ast.nodes[0], context, true);
            ast.nodes[1].checked = this.check(ast.nodes[1], context, true);
            const assertion = this.equal(type, ast.nodes[1], context);
            if (!assertion) { this.error(ast, TR("类型断言失败"), true); }
            this.check(type, context, false);
            const assertionType = this.equal(type.checked, ast.nodes[1].checked, context);
            if (!assertionType) { this.error(ast, TR("类型断言失败"), true); }
            ast.checked = ast.nodes[1];
        }
        try {
            // Type assertion
            if (ast.type === ":") {
                checkTypeIs(ast);
            } else if (ast.type === ":=") {
                if (ast.nodes[1].type === ":") {
                    checkTypeIs(ast.nodes[1]);
                } else {
                    this.check(ast.nodes[1], context, true);
                }
                ast.nodes[0].checked = ast.nodes[1].checked;
                ast.checked = ast.nodes[1].checked;
            } else if (ast.type === "===") {
                this.check(ast.nodes[0], context, true);
                this.check(ast.nodes[1], context, true);
                const assertion = this.equal(ast.nodes[0], ast.nodes[1], context);
                if (!assertion) { this.error(ast, TR("定义相等断言失败"), true); return; }
                ast.checked = ast.nodes[0].checked;
                let assertionT: boolean;
                assertionT = this.equal(Core.clone(ast.nodes[0].checked), Core.clone(ast.nodes[1].checked), context);
                if (!assertionT) { this.error(ast, TR("定义相等断言失败"), true); return; }
                this.check(ast.checked, context, true);
            } else if (allowModify && ast.type === "whnf") {
                // used for proof assistance to simplify expr
                this.whnf(ast.nodes[0], context, true);
            } else {
                this.check(ast, context, true);
                this.check(ast.checked, context, true);
            }

            this.solveInferRel();
            for (const [k, v] of Object.entries(this.state.inferTable.rel)) {
                this.whnf(v, this.state.inferTable.list.get(k.replace(/\:+$/, "").slice(1)), true);
            }
            this.fillInfered(ast);

        } catch (e) {
            errmsg = e;
        }
        // reduce final result, fill infer
        try {
            this.markAndCheckInferedValue(ast, context);
        } catch (e) {
            errmsg = e;
        }
        const alphaConversionIds = new Set<number>;
        this.reduce(ast, context, alphaConversionIds);
        this.doAlphaConversionByIds(ast, alphaConversionIds);
        if (this.state.errormsg.length) throw this.state.errormsg[0].msg;
        if (errmsg) { if (String(errmsg).includes("Maximum call")) throw TR("类型推断错误：疑似发现循环引用"); throw errmsg; }
        return ast.checked;
    }
    markAndCheckInferedValue(ast: AST, context: Context) {
        if (typeof ast.origin === "object") {
            const ori = ast.origin;
            delete ast.origin;
            const infered = (ori.name === "_" || ori.name[0] === "?") && ori.type === "var" ? Core.clone(ast, true) : null;
            if (infered) {
                Core.assign(ast, ori, true);
                if (infered.type === "var") {
                    infered.checked = this.checkConst(infered.name, context);
                }
                const err = this.state.errormsg.length;
                infered.checked ??= this.check(infered, context, false);
                if (this.state.errormsg.length > err) {
                    delete infered.checked;
                    this.state.errormsg.pop();
                }
                ast.checked = { type: ":", nodes: [infered, infered.checked ?? wrapVar("_")], name: "" };
            } else {
                Core.assign(ast, ori, true);
                this.fillInfered(ast);
            }
        } else {
            if (ast.nodes?.[0]) this.markAndCheckInferedValue(ast.nodes[0], context);
            if (ast.nodes?.[1]) {
                this.markAndCheckInferedValue(ast.nodes[1],
                    (ast.type === "L" || ast.type === "P" || ast.type === "S") ? assignContext(
                        [ast.name, ast.nodes[0], ast.bondVarId], context
                    ) : context
                );
            }
        }
    }
    reduce(ast: AST, context: Context, alphaConversionIds = new Set<number>) {
        if (ast.origin !== true) {
            // if is origin, don't modify
            const t = ast.checked;
            this.whnf(ast, context, true);
            ast.checked = t;
        }
        if (ast.nodes?.[0]) this.reduce(ast.nodes[0], context, alphaConversionIds);
        if (ast.nodes?.[1]) {
            this.reduce(ast.nodes[1],
                (ast.type === "L" || ast.type === "P" || ast.type === "S") ? assignContext(
                    [ast.name, ast.nodes[0], ast.bondVarId], context
                ) : context, alphaConversionIds
            );
        }
        if (ast.type === "var" && ast.bondVarId && ast.bondVarId !== Infinity) {
            // alpha conversion
            // find var in context by id
            const idx = context.findIndex(e => this.isBondVarIdEqual(e[2], ast.bondVarId));
            if (idx === -1) {
                console.warn("Bound Var Leakage of id " + ast.bondVarId, context); return;
            }
            // then check whether there is the same name
            // if the same name occur in inner context, it must be renamed, we added it to a array then solve it latter
            const boundedIdx = context.filter((e, subidx) => subidx < idx && e[0] === context[idx][0]);
            for (const [a, b, c] of boundedIdx) {
                alphaConversionIds.add(c);
            }
            ast.name = context[idx][0];
        }
        if (ast.checked) this.reduce(ast.checked, context, alphaConversionIds);

        if (!ast.origin || ast["desugared"]) this.ensugar(ast);
    }
    static getFreeVars(ast: AST, res = new Set<string>, scope: string[] = []) {
        if (ast.type === "var" && !scope.includes(ast.name)) {
            res.add(ast.name);
        } else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            this.getFreeVars(ast.nodes[0], res, scope);
            this.getFreeVars(ast.nodes[1], res, [ast.name, ...scope])
        } else if (ast.nodes?.length === 2) {
            this.getFreeVars(ast.nodes[0], res, scope);
            this.getFreeVars(ast.nodes[1], res, scope);
        }
        return res;
    }
    static getNewName(refName: string, excludeSet: Set<string>) {
        let n = refName;
        while (excludeSet.has(n)) {
            n += "'";
        }
        return n;
    }
    doAlphaConversionByIds(ast: AST, ids: Set<number>) {
        if ((ast.type === "L" || ast.type === "P" || ast.type === "S") && ids.has(ast.bondVarId) && ast.origin !== true) {
            // Lx1.Lx2. x1 Lx'.x'
            const k = wrapVar(Core.getNewName(ast.name + "'", Core.getFreeVars(ast)));
            k.checked = ast.nodes[0];
            k.bondVarId = ast.bondVarId;
            this.replaceVar(ast.nodes[1], "?", ast.bondVarId, k);
            ast.name = k.name;
            ast.origin = true;
            // ids.delete(ast.bondVarId);
        }
        if (ast.nodes?.[0]) this.doAlphaConversionByIds(ast.nodes[0], ids);
        if (ast.nodes?.[1]) this.doAlphaConversionByIds(ast.nodes[1], ids);
        delete ast.bondVarId;
        if (ast.checked) this.doAlphaConversionByIds(ast.checked, ids);
    }
    showInfered() {
        let ast = this.state;
        let str = "";
        if (ast?.inferTable?.list)
            str += JSON.stringify(Array.from(ast.inferTable.list.keys()).filter(e => !ast.inferTable.solved.has("?" + e))) + "\n";
        if (ast?.inferTable?.rel)
            str += JSON.stringify(Object.entries(ast.inferTable.rel).map(([k, v]) => [k, parser.stringify(v)]));
        return str;
    }
    private check(ast: AST, context: Context, ignoreErr: boolean): AST {
        // pick cache
        // if (ast.checked) return ast.checked;
        if (ast.type === "var") {
            if (ast.name === "_") {
                const n = this.state.inferTable.addNewName(0, context);
                ast.name = "?" + n;
                if (context[0]?.[0] === "U@") {
                    ast.checked = wrapVar("U@");
                    return ast.checked;
                }
                if (ast.origin) {
                    ast.origin = wrapVar("_");
                }
                ast.checked = wrapVar("?" + n + ":");
                return ast.checked;
            }
            // variable in condition
            const ctxtInfo = context?.find(e => this.isBondVarIdEqual(e[2], ast.bondVarId));
            if (ctxtInfo) {
                ast.checked = ctxtInfo[1];
                ast.bondVarId = ctxtInfo[2];
            }
            if (ast.checked) return ast.checked;
            if (ast.bondVarId) { this.error(ast, TR("本应约束的变量在类型推断时自由出现：") + ast.name, ignoreErr); return; }
            // const in environment
            const cc = this.checkConst(ast.name, context);
            if (cc) { ast.checked = cc; } else this.error(ast, TR("未知的变量：") + ast.name, ignoreErr);
            return ast.checked;
        }
        if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            const bondVarId = this.getBondVarId(ast);
            const domain = ast.nodes[0];
            const Udomain = UniverseLevel.get(this.check(domain, context, ignoreErr));
            if (Udomain === false) this.error(domain, TR(`函数参数类型不合法`), ignoreErr);
            const subCtxt = assignContext([ast.name, domain, bondVarId], context);
            const codomain = this.check(ast.nodes[1], subCtxt, ignoreErr);
            if (ast.type === "L") {
                ast.checked = wrapLambda("P", ast.name, domain, codomain);
                ast.checked.bondVarId = ast.bondVarId;
            } else if (ast.type === "P" || ast.type === "S") {
                const Ucodomain = UniverseLevel.get(codomain);
                if (Ucodomain === false) this.error(ast.nodes[1], TR(`函数返回类型不合法`), ignoreErr);
                this.check(ast.nodes[0], context, ignoreErr);
                ast.checked = UniverseLevel.max(domain.checked, codomain);
            }
            return ast.checked;
        }
        if (ast.type === "apply") {
            // U(n) : U(@succ n)
            if (ast.nodes[0].name === "U") {
                this.check(ast.nodes[1], assignContext(["U@", null, Infinity], context), true);
                ast.checked = UniverseLevel.succ(ast);
                return ast.checked;
            }
            const tfn = this.check(ast.nodes[0], context, ignoreErr);
            const tap = this.check(ast.nodes[1], context, ignoreErr);
            // tfn.origin = Core.clone(tfn, true);
            // tap.origin = Core.clone(tap, true);
            if (!tfn || !tap) {
                this.error(ast, TR("非函数尝试作用"), ignoreErr);
            }
            if (tfn.type === "->") {
                if (this.equal(tfn.nodes[0], tap, context)) {
                    ast.checked = tfn.nodes[1];
                    return ast.checked;
                }
            }
            const ap = wrapVar("_");
            const fnType = wrapLambda("P", "_", tap, ap);
            const bondVarId = this.getBondVarId(fnType);
            // a: Px:A.B(x)   b:A  -> a(b):B(b)
            if (this.equal(fnType, tfn, context)) {
                // before beta-reduction, fill infered
                this.solveInferRel();
                ast.checked = Core.clone(ap);
                this.fillInfered(ast.checked);
                this.replaceVarInInfer(fnType.name, bondVarId, ast.nodes[1]);
                this.replaceVar(ast.checked, fnType.name, bondVarId, ast.nodes[1], context);
                return ast.checked;
            } else {
                this.error(ast, TR("函数作用类型不匹配"), ignoreErr);
            }
            return ast.checked;
        }
    }
    desugar(ast: AST, allowModify: boolean) {
        ast.origin = !allowModify;
        if (ast.type === "X") {
            const nast = parser.parse("@Prod _ _ ?A (L_:?A.?B)");
            nast.nodes[0].nodes[1] = ast.nodes[0];
            nast.nodes[1].nodes[0] = ast.nodes[0];
            nast.nodes[1].nodes[1] = ast.nodes[1];
            ast["desugared"] = true;
            Core.assign(ast, nast);
        } else if (ast.type === "+") {
            const nast = parser.parse("@Sum _ _ ?A ?B");
            nast.nodes[0].nodes[1] = ast.nodes[0];
            nast.nodes[1] = ast.nodes[1];
            ast["desugared"] = true;
            Core.assign(ast, nast);
        } else if (ast.type === ",") {
            const nast = parser.parse("@pair _ _ _ (L_:_._) ?a ?b");
            nast.nodes[0].nodes[1] = ast.nodes[0];
            nast.nodes[1] = ast.nodes[1];
            ast["desugared"] = true;
            Core.assign(ast, nast);
        } else if (ast.type === "S") {
            const nast = parser.parse("@Prod _ _ ?a ?fn");
            nast.nodes[1] = Core.clone(ast);
            nast.nodes[1].type = "L";
            Core.assign(ast, nast);
            ast["desugared"] = true;
            ast.nodes[0].nodes[1] = ast.nodes[1].nodes[0];
        }
        if (ast.type === "->") {
            ast.type = "P"; ast.name = "_";
            ast["desugared"] = true;
        }
        if (ast.nodes) {
            for (const n of ast.nodes) this.desugar(n, allowModify);
        }
        return ast;
    }
    opaque = [
        ["pair", 4], ["eq", 3], ["inl", 5], ["inr", 5], ["refl", 3], ["ind_Prod", 5], ["ind_eq", 4], ["ind_Sum", 6],
        ["ind_Bool", 2], ["ind_nat", 2], ["ap", 5], ["trans", 4], ["apd", 4], ["inveq", 4], ["compeq", 5],
        ["pr0", 3], ["prd1", 2], ["pr1", 3], ["id2eqv", 4], ["eqv", 2]
    ] as [string, number][];
    ensugar(ast: AST) {
        // no recursive, outter fn will do that
        if (ast.type === "P") {
            if (ast.name === "_" || !this.hasBondVar(ast.nodes[1], ast.bondVarId)) {
                if (ast.bondVarId === 4 && ast.name[0] === "y" && ast.nodes[0].name === "nat") {
                    console.log("uu");
                }
                ast.type = "->";
                ast.name = "";
            }
        }
        if (ast.type === "apply") {
            const ali = this.flattenApplyList(ast);
            if (ali[0].bondVarId) return ast;
            const args = ali.length;
            const fn = ali[0].name;
            if (fn === "@Prod" && args === 5) {
                const l = ali[4];
                const t = ast.checked;
                if (this.hasBondVar(l.nodes[1], l.bondVarId)) {
                    Core.assign(ast, wrapLambda("S", l.name, l.nodes[0], l.nodes[1]), true);
                    ast.bondVarId = l.bondVarId;
                } else {
                    Core.assign(ast, { type: "X", nodes: l.nodes, name: "" }, true);
                }
                ast.checked = t;
                return;
            }
            if (fn === "@Sum" && args === 5) {
                const t = ast.checked;
                Core.assign(ast, { type: "+", nodes: [ali[3], ali[4]], name: "" }, true);
                ast.checked = t;
                return;
            }
            for (const [k, v] of this.opaque) {
                if (ali[0].name === "@" + k && args === v) {
                    const t = ast.checked;
                    Core.assign(ast, wrapVar(k));
                    ast.checked = t;
                    continue;
                }
            }
            if (fn === "@pair" && args === 7 && ali[4].type === "L" && !this.hasBondVar(ali[4].nodes[1], ali[4].bondVarId)) {
                const t = ast.checked;
                Core.assign(ast, { type: ",", nodes: [ali[5], ali[6]], name: "" }, true);
                ast.checked = t;
                return;
            }
            if (fn === "pair" && args === 4 && ali[1].type === "L" && !this.hasBondVar(ali[1].nodes[1], ali[1].bondVarId)) {
                const t = ast.checked;
                Core.assign(ast, { type: ",", nodes: [ali[2], ali[3]], name: "" }, true);
                ast.checked = t;
                return;
            }
        }
        return ast;
    }
    checkConst(n: string, context: Context): AST {
        if (n.startsWith("?")) {
            return this.state.inferTable.rel[n + ":"] || wrapVar(n + ":");
        }
        // sys types
        let res = this.state.sysTypes[n];
        if (res) return this.markBondVars(Core.clone(res), context);
        // sys/user Defs
        res = this.state.sysDefs[n] || this.state.userDefs[n];
        if (res) {
            return this.check(this.markBondVars(Core.clone(res), context), context, false);
        }

        // literal:

        // @i : U@
        if (n[0] === "@" && NatLiteral.is(n.slice(1))) return wrapVar("U@");
        // 12345: nat
        if (NatLiteral.is(n)) return wrapVar("nat");
        // unknown
        return null;
    }
    replaceVarInInfer(name: string, bondVarId: number, dst: AST) {
        const it = this.state.inferTable;
        for (const [k, v] of it.list.entries()) {
            if (it.rel["?" + k] && v.find(e => this.state.bondVarRel.eq(e[2], bondVarId))) {
                this.replaceVar(it.rel["?" + k], name, bondVarId, dst, v);
            }
        }
    }
    tryDirectCompute(ast: AST, context: Context, skipExpand: boolean) {
        const list = this.flattenApplyList(ast);
        if (list[0].bondVarId) return false; // this implies that "add" is local var, cannot reduce
        const fn = list[0].name;
        if ((fn === "add" || fn === "mul" || fn === "pow") && list.length === 3) {
            this.whnf(list[1], context, skipExpand);
            this.whnf(list[2], context, skipExpand);
            if (list[2].nodes?.[0]?.name === "succ") {
                // add a succ(b) -> succ(add a b)
                if (fn === "add") { Core.assign(ast, wrapApply(wrapVar("succ"), wrapApply(list[0], list[1], list[2].nodes[1]))); return true; }
                // mul a succ(b) -> mul(a b)
                if (fn === "mul") { Core.assign(ast, wrapApply(wrapVar("succ"), wrapApply(list[0], list[1], list[2].nodes[1]))); return true; }
            }
            if (!NatLiteral.is(list[1]) || !NatLiteral.is(list[2])) return false;
            try {
                // || NaN is for preventing "" -> 0n
                const a = BigInt(list[1].name || NaN);
                const b = BigInt(list[2].name || NaN);
                if (a < 0n || b < 0n) return;
                Core.assign(ast, wrapVar(String(
                    fn === "add" ? a + b : fn === "mul" ? a * b : fn === "pow" ? a ** b : ""
                )));
                return true;
            } catch (e) {
                return false;
            }
        }
        if ((fn === "pred" || fn === "succ") && list.length === 2) {
            this.whnf(list[1], context, skipExpand);
            if (!NatLiteral.is(list[1])) return false;
            try {
                // || NaN is for preventing "" -> 0n
                const a = BigInt(list[1].name || NaN);
                if (a < 0n) return;
                Core.assign(ast, wrapVar(String(
                    fn === "pred" ? a > 0n ? a - 1n : 0n : fn === "succ" ? a + 1n : ""
                )));
                return true;
            } catch (e) {
                return false;
            }
        }
        return false;
    }
    whnf(ast: AST, context: Context, skipExpand: boolean) {
        while (true) {
            if (ast.type === "apply") {
                if (this.tryDirectCompute(ast, context, skipExpand)) continue;
                this.whnf(ast.nodes[0], context, skipExpand);
                const [fn, ap] = ast.nodes;
                if (fn.type === "L") {
                    const id = this.getBondVarId(fn);
                    // try to fill infered values before beta-reduction, to avoid some bad things
                    // this.solveInferRel();
                    this.fillInfered(ast);
                    // this.replaceVarInInfer(fn.name, id, ap);
                    const nt1 = Core.clone(fn.nodes[1], true);
                    this.replaceVar(nt1, fn.name, id, ap, context);
                    Core.assign(ast, nt1, true);
                } else if (fn.type === "var" && !fn.bondVarId && !skipExpand) {
                    let expand: AST;
                    // f a => (....) a
                    if (expand = this.state.sysDefs[fn.name] || this.state.userDefs[fn.name]) {
                        Core.assign(fn, this.markBondVars(Core.clone(expand), context));
                    }
                    // if compute rule modified, then go on loop
                    if (!this.iotaHead(ast, context)) return true;
                } else {
                    if (!this.iotaHead(ast, context)) return true;
                }
            } else if (ast.type === "var" && !ast.bondVarId && !skipExpand) {
                let expand: AST;
                // f a => (....) a
                if (expand = this.state.sysDefs[ast.name] || this.state.userDefs[ast.name]) {
                    Core.assign(ast, this.markBondVars(Core.clone(expand), context));
                } else return;
            } else return;
        }
    }

    flattenApplyList(ast: AST): AST[] {
        const applyList = [];
        let sub = ast;
        while (sub.type === "apply") {
            applyList.unshift(sub.nodes[1]);
            sub = sub.nodes[0];
        }
        applyList.unshift(sub);
        return applyList;
    }
    // exprs containning @max and @succ can reduced by @max(xx:m+,xx:n,xxx+++,xx); where "+" stands for @succ, :m for bondvar id
    getUmaxItems(ast: AST): Set<string> | string {
        if (ast.type === "var") return ast.name + (ast.bondVarId ? ":" + ast.bondVarId : "");
        let ali = this.flattenApplyList(ast);
        if (ali[0].name === "@succ" && ali.length === 2) {
            const k = this.getUmaxItems(ali[1]);
            if (typeof k === "string") {
                return k + "+";
            } else {
                return new Set(Array.from(k).map(k => k + "+"));
            }
        }
        if (ali[0].name !== "@max") {
            this.error(ast, TR("未知的全类层级运算") + " : " + ali[0].name, true);
            return;
        }
        let s = new Set<string>;
        for (let i = 1; i < ali.length; i++) {
            const k = this.getUmaxItems(ali[i]);
            if (typeof k === "string") s.add(k); else k.forEach(e => s.add(e));
        }
        return s;
    }
    iotaHead(ast: AST, context: Context): boolean {
        const applyList = this.flattenApplyList(ast);
        if (applyList[0].bondVarId) return false;
        const fn = applyList[0].name;
        // @succ @n => @n+1
        if (fn === "@succ" && applyList.length === 2) {
            this.whnf(ast.nodes[1], context, false);
            const n = ast.nodes[1].name;
            if (n?.startsWith("@")) {
                try {
                    const succN = BigInt(ast.nodes[1].name.slice(1)) + 1n;
                    ast.nodes[1].name = "@" + succN;
                    Core.assign(ast, ast.nodes[1]);
                } catch (e) { this.error(ast, TR("未知的全类层级运算") + " : " + n, true); }
            }
        }
        if (fn === "@max" && applyList.length > 2) {
            const sk = this.getUmaxItems(ast) as Set<string>;
            const k = Array.from(sk) as (string | BigInt)[];
            const idxK = k.slice(0) as string[];
            let maxBigInt = 0n;
            for (let i = 0; i < k.length; i++) {
                if ((k[i] as string).startsWith("@")) {
                    try {
                        const succN = BigInt((k[i] as string).slice(1).replaceAll("+", "")) + BigInt((k[i] as string).length - (k[i] as string).replaceAll("+", "").length);
                        if (succN > maxBigInt) maxBigInt = succN; else sk.delete(k[i] as string);
                        k[i] = succN;
                        continue;
                    } catch (e) { }
                }
                let a = k[i] as string;
                let n = BigInt(a.length - a.replaceAll("+", "").length);
                if (n > maxBigInt) maxBigInt = n;
            }
            for (let i = 0; i < k.length; i++) {
                let a = k[i];
                if (typeof a === "bigint") {
                    if (a < maxBigInt) {
                        sk.delete(idxK[i]);
                    }
                }
                for (let j = i + 1; j < k.length; j++) {
                    let b = k[j];
                    if (typeof a === "string" && typeof b === "string") {
                        // k[i] = A++++, k[j] = A+ => k[i] > k[j], so delete k[j]
                        if (a.startsWith(b) && a.endsWith("+".repeat(a.length - b.length))) {
                            sk.delete(b);
                        }
                        // k[j] = A++++, k[i] = A+ => k[j] > k[i], so delete k[i]
                        if (b.startsWith(a) && b.endsWith("+".repeat(b.length - a.length))) {
                            sk.delete(a); continue;
                        }
                    }

                }
            }
            const res = sk;
            if (!res.size) res.add("@0");
            let astPrev: AST;
            let nast: AST;
            for (let r of res) {
                if (typeof r === "bigint") {
                    nast = wrapVar("@" + r);
                } else {
                    let astVar = wrapVar("");
                    nast = astVar;
                    while ((r as string).endsWith("+")) {
                        r = (r as string).slice(0, -1);
                        nast = wrapApply(wrapVar("@succ"), nast);
                    }
                    const name_id = (r as string).split(":");
                    astVar.name = name_id[0];
                    if (name_id[1]) astVar.bondVarId = Number(name_id[1]);
                }
                if (astPrev) {
                    nast = wrapApply(wrapVar("@max"), astPrev, nast);
                }
                astPrev = nast;
            }
            Core.assign(ast, nast);
        }
        let rule = this.state.computeRules[fn];
        if (!rule?.length) return false;
        for (const rle of rule) {
            const { pattern, result } = rle;
            let tail = applyList.length - pattern.length;
            if (tail < 0) continue;

            const res = Core.clone(result);
            const matchTable: Varlist = {};
            let matchFail = false;
            for (let i = 0; i < pattern.length; i++) {
                const p = pattern[i];
                if (p.name === "_") continue;
                const it = applyList[i];
                // when do match, the term must be whnf to get head ctor
                if (i && p.name[0] !== "?") this.whnf(it, context, false);
                if (!Core.match(it, p, /^\?/, matchTable)) { matchFail = true; break; }
            }
            if (matchFail) continue;
            Core.replaceByMatch(res, matchTable, /^\?/);
            let replaceAst = ast;
            while (tail--) replaceAst = replaceAst.nodes[0];
            Core.assign(replaceAst, this.remarkLambdaBondIds(res, context));
            return true;
        }
    }

    addInferRel(name: string, ast: AST, context: Context) {
        const ctxt = this.state.inferTable.list.get(name.slice(1).replaceAll(":", "")) ?? [];
        let a = ctxt.length - 1, b = context.length - 1;
        const rel = this.state.bondVarRel;
        let whnfed = false;
        while (a >= 0 && b >= 0) {
            const ida = ctxt[a][2], idb = context[b][2];
            // L1.L2.?0   ->  L1.L3 ({1} {3})  ->   2=3
            if (this.hasBondVar(ast, idb) && !rel.eq(ida, idb)) {
                if (!whnfed) { if (ast.origin === true) ast = Core.clone(ast, true); this.whnf(ast, context, false); whnfed = true; }
                if (this.hasBondVar(ast, idb)) {
                    rel.union(ida, idb);
                }
            }
            a--; b--;
        }
        if (ast.name === name) return true;
        if (this.hasInferVar(ast, name)) { // exclude contain self
            // maybe there is fake loop, e.g. ?1 == ((Lx:_.Bool) ?1) -> ?1 == Bool, no loop
            if (!whnfed) { if (ast.origin === true) ast = Core.clone(ast, true); this.whnf(ast, context, false); whnfed = true; }
            if (ast.name === name) return true;
            if (this.hasInferVar(ast, name)) {
                console.log("loop " + name + " !== " + parser.stringify(ast));
                this.error(ast, TR("类型推断错误：发现循环引用"), false); return false;
            }
        }
        const oldVal = this.state.inferTable.rel[name];
        // if here is already a value, conflict must be solved now!!
        if (oldVal) {
            return this.equal(oldVal, ast, context);
        }
        // cancel loop
        let dst = ast;
        while (dst?.name?.[0] === "?") {
            dst = this.state.inferTable.rel[dst.name];
            if (dst) ast = dst;
        }
        if (ast.name === name) return true;

        this.state.inferTable.rel[name] = ast;
        return true;
    }
    solveInferRel() {
        const it = this.state.inferTable;
        const solved = it.solved;
        while (true) {
            let replaceKey = null;
            for (const [k, v] of Object.entries(it.rel)) {
                // if this is not a inferval's type, && its value is solved, we replace all other occurences
                if (!solved.has(k) && !k.endsWith(":") && !Array.from(new InferTable(v).list.keys()).filter(e => !solved.has("?" + e)).length) {
                    solved.add(k);
                    replaceKey = k;
                    if (it.rel[k + ":"]) {
                        const kt = k + ":";
                        for (const [k, v] of Object.entries(it.rel)) {
                            if (!solved.has(k)) {
                                this.replaceVar(v, kt, -1, it.rel[kt]);
                            }
                        }
                        const ctxt = it.list.get(k.slice(1).replaceAll(":", "")) ?? [];
                        this.whnf(v, ctxt, false);
                        if (!this.equal(this.check(v, ctxt, false), it.rel[kt], ctxt)) return false;
                        it.rel[kt] = this.check(v, ctxt, false);
                        solved.add(kt);
                    }
                    break;
                }
            }
            if (replaceKey) {
                let changed = false;
                for (const [k, v] of Object.entries(it.rel)) {
                    // replace all other occurences
                    if (solved.has(k)) continue;
                    const ch = this.replaceVar(v, replaceKey, -1, it.rel[replaceKey]);
                    changed ||= ch;

                }
                if (!changed) {
                    solved.add(replaceKey);
                }
            } else {
                break;
            }
        }
    }
    fillInfered(ast: AST) {
        const it = this.state.inferTable;
        if (ast.checked) {
            this.fillInfered(ast.checked);
        }
        if (ast.nodes) {
            for (const n of ast.nodes) {
                this.fillInfered(n);
            }
        } else {
            Core.replaceByMatch(ast, it.rel, /^\?/);
        }
    }
    equal(a: AST, b: AST, context: Context): boolean {
        if (a === b || Core.exactEqual(a, b)) return true;
        if (a.type === b.type && a.type === "var" && this.isBondVarIdEqual(a.bondVarId, b.bondVarId)) return true;

        // type "U@" and "U@:" are equal
        if (a.name?.startsWith("U@") && b.name?.startsWith("U@")) return true;
        if (a.origin === true) a = Core.clone(a);
        if (b.origin === true) b = Core.clone(b);
        // infered value matched. add this rel
        if (a.name?.startsWith("?")) {
            return this.addInferRel(a.name, b, context);
        } else if (b.name?.startsWith("?")) {
            return this.addInferRel(b.name, a, context);
        }
        // whnf: fn apply beta reduction, iota computation and delta expansion
        this.whnf(a, context, false);
        this.whnf(b, context, false);

        if (a.name?.startsWith("?")) {
            return this.addInferRel(a.name, b, context);
        } else if (b.name?.startsWith("?")) {
            return this.addInferRel(b.name, a, context);
        }

        // fn alpha conversion
        if (a.type === b.type && (a.type === "L" || a.type === "P" || a.type === "S")) {
            if (!this.equal(a.nodes[0], b.nodes[0], context)) {
                console.log(`${a.type} ${parser.stringify(a.nodes[0])} != ${parser.stringify(b.nodes[0])}`);
                return false;
            }
            if (a.name === "_") a.name = b.name; else if (b.name === "_") b.name = a.name;
            // this union is equiv for alpha-conversion
            this.state.bondVarRel.union(this.getBondVarId(a), this.getBondVarId(b));
            return this.equal(a.nodes[1], b.nodes[1], assignContext([a.name, a.nodes[0], this.getBondVarId(a)], context));
        }

        // recurse
        if (a.type === b.type && a.name == b.name && a.nodes?.length && a.nodes?.length === b.nodes?.length) {
            let breaked = false;
            // if recursive eq failed, we need to undo inferring during recursive eq.
            for (let i = 0; i < a.nodes?.length; i++) {
                if (!this.equal(a.nodes[i], b.nodes[i], context)) { breaked = true; break; }
            }
            if (!breaked) return true;
            // recursive eq failed
            return false;
        }
        if (a.type === b.type && a.type === "var" && ((!a.bondVarId && !b.bondVarId && a.name === b.name) || this.isBondVarIdEqual(a.bondVarId, b.bondVarId))) return true;

        // def delta expand
        if (a.type === "var") {
            if (a.name === "_") {
                Core.assign(a, b);
                return true;
            }
            let expand: AST;
            if (!a.bondVarId && (expand = this.state.sysDefs[a.name] || this.state.userDefs[a.name])) {
                Core.assign(a, this.markBondVars(Core.clone(expand), context));
                return this.equal(a, b, context);
            }
            // fn eta conversion: Lx:a.b = f  ->  Lx:a.b = Lx:a.f x
            if (b.type === "L") {
                Core.assign(a, wrapLambda("L", b.name, b.nodes[0], wrapApply(wrapVar(a.name), wrapVar(b.name))));
                return this.equal(a.nodes[1], b.nodes[1], context);
            }
            // number === succ (n:nat)
            if (a.name !== "0" && NatLiteral.is(a) && b.type === "apply" && b.nodes[0].name === "succ") {
                return this.equal(wrapVar(String(BigInt(a.name) - 1n)), b.nodes[1], context);
            }
        }
        if (b.type === "var") {
            if (b.name === "_") {
                Core.assign(b, a);
                return true;
            }
            let expand: AST;
            if (!b.bondVarId && (expand = this.state.sysDefs[b.name] || this.state.userDefs[b.name])) {
                Core.assign(b, this.markBondVars(Core.clone(expand), context));
                return this.equal(a, b, context);
            }
            // fn eta conversion: Lx:a.b = f  ->  Lx:a.b = Lx:a.f x
            if (a.type === "L") {
                Core.assign(b, wrapLambda("L", a.name, a.nodes[0], wrapApply(wrapVar(b.name), wrapVar(a.name))));
                return this.equal(a.nodes[1], b.nodes[1], context);
            }
            // number eta-like conversion: n = succ x -> succ (n-1) = succ x
            if (b.name !== "0" && NatLiteral.is(b) && a.type === "apply" && a.nodes[0].name === "succ") {
                return this.equal(wrapVar(String(BigInt(b.name) - 1n)), a.nodes[1], context);
            }
        }
        if (a.type === b.type && a.type === "var" && a.bondVarId && b.bondVarId) {
            // they are both bond vars, test whether they are equal by alpha/beta conversion
            return this.state.bondVarRel.eq(a.bondVarId, b.bondVarId);
        }
        // a = ?xx b  ->  ?xx := L_.a
        if (b.type === "apply" && b.nodes[0].name[0] === "?") {
            const l = wrapLambda("L", "_", b.checked ?? wrapVar("_"), Core.clone(a, true));
            this.getBondVarId(l);
            return this.addInferRel(b.nodes[0].name, l, context);
        }
        // b = ?xx a  ->  ?xx := L_.b
        if (a.type === "apply" && a.nodes[0].name[0] === "?") {
            const l = wrapLambda("L", "_", a.checked ?? wrapVar("_"), Core.clone(b, true));
            this.getBondVarId(l);
            return this.addInferRel(a.nodes[0].name, l, context);
        }
        console.log(`? ${parser.stringify(a)} != ${parser.stringify(b)}`);
        return false;
    }

    static exactEqual(ast1: AST, ast2: AST) {
        if (ast1 === ast2) return true;
        if (ast1.type !== ast2.type) return false;
        if (ast1.type === "var" && ast1.bondVarId && ast1.bondVarId !== ast2.bondVarId) {
            return false;
        }
        if (ast1.name != ast2.name) return false; // undefined == null but !== null
        if (ast1.nodes?.length !== ast2.nodes?.length) return false;
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.exactEqual(ast1.nodes[i], ast2.nodes[i])) return false;
            }
        }
        return true;
    }

    expandDef(ast: AST, context: Context, n: string | Set<string>): boolean {
        let found = false;
        if (ast.type === "var" && !ast.bondVarId && (
            ast.name === n || (typeof n === "object" && n.has(ast.name))) && !context.find(e => e[0] === ast.name)
        ) {
            const expr = this.state.sysDefs[ast.name] || this.state.userDefs[ast.name];
            Core.assign(ast, Core.clone(expr));
            return true;
        }
        if (ast.nodes?.length) {
            found = this.expandDef(ast.nodes[0], context, n) || found;
            if (ast.type === "P" || ast.type === "L" || ast.type === "S") {
                context = assignContext([ast.name, ast.nodes[0], 0], context);
            }
            found = this.expandDef(ast.nodes[1], context, n) || found;
        }
        return found;
    }
}
class NatLiteral {
    static is(ast: AST | string) {
        if (!ast) return false;
        return typeof ast === "string" ? ast === "0" || ast.match(/^[1-9][0-9]*$/) : ast.type === "var" && (ast.name === "0" || ast.name.match(/^[1-9][0-9]*$/));
    }
}
class UniverseLevel {
    static succ(ast: AST) {
        const u = UniverseLevel.get(ast);
        if (typeof u === "bigint") {
            return wrapU("@" + String(u + 1n));
        }
        if (u === false) throw TR("尝试对非全类操作层级");
        return {
            type: "apply", name: "", nodes: [
                wrapVar("U"),
                {
                    type: "apply", name: "", nodes: [
                        wrapVar("@succ"), Core.clone(ast.nodes[1])
                    ]
                }
            ]
        };
    }
    static max(a: AST, b: AST) {
        const u = UniverseLevel.get(a);
        const v = UniverseLevel.get(b);
        if (typeof u === "bigint" && typeof v === "bigint") {
            return wrapApply(wrapVar("U"), wrapVar("@" + String(u > v ? u : v)));
        }
        if (u === false || v === false) throw TR("尝试对非全类操作层级");
        if (a.type === "var" || b.type === "var") return wrapApply(wrapVar("U"), wrapVar("?"));
        return {
            type: "apply", name: "", nodes: [
                wrapVar("U"),
                wrapApply(
                    wrapVar("@max"), Core.clone(a.nodes[1]), Core.clone(b.nodes[1])
                )
            ]
        };
    }
    /** check whether ast is universe, return its level number, if level is not given return true, if it is not universe, return false */
    static get(ast: AST): bigint | boolean {
        if (ast.type === "var" && ast.name === "U") {
            return 0n;
        }
        if (ast.type === "var" && (ast.name === "_" || ast.name.endsWith(":"))) {
            // an unknown inffered type
            return true;
        }
        if (ast.type === "apply" && ast.nodes[0].name === "U") {
            if (ast.nodes[1].name[0] === "@") {
                const s = ast.nodes[1].name.slice(1);
                if (NatLiteral.is(s)) return BigInt(s);
            }
            return true;
        }
        return false;
    }
}