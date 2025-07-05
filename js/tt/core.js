import { TR } from "../lang.js";
import { ASTParser } from "./astparser.js";
const parser = new ASTParser;
// sugars begin
export function wrapVar(v) {
    return { type: "var", name: v };
}
function wrapU(v) {
    return { type: "apply", name: "", nodes: [wrapVar("U"), wrapVar(v)] };
}
function wrapLambda(type, param, paramType, body) {
    return { type, name: param, nodes: [paramType, body] };
}
export function wrapApply(...terms) {
    let ast = terms.shift();
    let ast1;
    while (ast1 = terms.shift()) {
        ast = { type: "apply", name: "", nodes: [ast, ast1] };
    }
    return ast;
}
/** return a cloned Context */
function assignContext(added, oldContext) {
    return Object.assign(Object.assign({}, oldContext), added);
}
export class Core {
    static assign(ast, value, moveSemantic) {
        const v = moveSemantic ? value : this.clone(value);
        ast.type = v.type;
        ast.name = v.name;
        ast.nodes = v.nodes;
        ast.checked = v.checked;
    }
    static match(ast, pattern, regexp, res = {}) {
        if (pattern.type === "var" && pattern.name.match(regexp)) {
            res[pattern.name] ??= ast;
            if (!this.exactEqual(ast, res[pattern.name]))
                return null;
            return res;
        }
        if (ast.type !== pattern.type)
            return null;
        if (ast.nodes?.length !== pattern.nodes?.length)
            return null;
        if (ast.nodes?.length) {
            for (let i = 0; i < ast.nodes.length; i++) {
                if (!this.match(ast.nodes[i], pattern.nodes[i], regexp, res))
                    return null;
            }
        }
        if (ast.name !== pattern.name)
            return null;
        return res;
    }
    static clone(ast, cloneChecked) {
        const checked = (cloneChecked && ast.checked) ? this.clone(ast.checked) : null;
        const newast = {
            type: ast.type, name: ast.name, checked, err: ast.err
        };
        if (ast.nodes) {
            newast.nodes = ast.nodes.map(p => this.clone(p, cloneChecked));
        }
        return newast;
    }
    static replaceByMatch(ast, res, regexp) {
        if (!res)
            throw TR("未匹配");
        if (!ast)
            return; // here not panic because aftercheck need it
        if (ast.type === "var" && ast.name.match(regexp)) {
            if (!res[ast.name])
                return false;
            this.assign(ast, this.clone(res[ast.name]));
            return true;
        }
        else if (ast.nodes?.length) {
            let modified = false;
            for (const n of ast.nodes) {
                if (this.replaceByMatch(n, res, regexp))
                    modified = true;
            }
            return modified;
        }
    }
    static getNewName(refName, excludeSet) {
        let n = refName + "'";
        if (excludeSet instanceof Set) {
            while (excludeSet.has(n)) {
                n += "'";
            }
        }
        else {
            while (excludeSet[n]) {
                n += "'";
            }
        }
        return n;
    }
    static getFreeVars(ast, res = new Set, scope = []) {
        if (ast.type === "var" && !scope.includes(ast.name)) {
            res.add(ast.name);
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            this.getFreeVars(ast.nodes[0], res, scope);
            this.getFreeVars(ast.nodes[1], res, [ast.name, ...scope]);
        }
        else if (ast.nodes?.length === 2) {
            this.getFreeVars(ast.nodes[0], res, scope);
            this.getFreeVars(ast.nodes[1], res, scope);
        }
        return res;
    }
    replaceVarInChecked(ast, name, dst, context) {
        if (ast.checked)
            this.replaceVar(ast.checked, name, dst, context);
        if (ast.nodes?.length === 2) {
            this.replaceVarInChecked(ast.nodes[0], name, dst, context);
            this.replaceVarInChecked(ast.nodes[1], name, dst, context);
        }
    }
    replaceVar(ast, name, dst, context, fvDst = Core.getFreeVars(dst)) {
        if (ast.type === "var") {
            if (ast.name !== name)
                return;
            Core.assign(ast, dst);
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            this.replaceVar(ast.nodes[0], name, dst, context, fvDst);
            if (ast.name === name)
                return; // bounded
            const fvSrcBody = Core.getFreeVars(ast.nodes[1]);
            if (!fvSrcBody.has(name))
                return; // not bounded, but not found
            let bounded = false;
            if (context) {
                for (const e of fvDst) {
                    if (context[e] && Core.exactEqual(context[e], ast.nodes[0])) {
                        bounded = true;
                        break;
                    }
                }
            }
            if (!fvDst.has(ast.name) || bounded) {
                this.replaceVar(ast.nodes[1], name, dst, context, fvDst);
            }
            else {
                const newName = Core.getNewName(ast.name, new Set([...fvSrcBody, ...fvDst]));
                this.replaceVar(ast.nodes[1], ast.name, { type: "var", name: newName }, context);
                this.replaceVar(ast.nodes[1], name, dst, context, fvDst);
                ast.name = newName;
            }
            return;
        }
        else if (ast.nodes?.length === 2) {
            this.replaceVar(ast.nodes[0], name, dst, context, fvDst);
            this.replaceVar(ast.nodes[1], name, dst, context, fvDst);
        }
    }
    state = {
        sysTypes: {
            "U@": wrapVar("U@:"),
            "U@:": wrapVar("U@:"),
            "@max": parser.parse("U@->U@->U@"),
            "@succ": parser.parse("U@->U@"),
        },
        sysDefs: {},
        userDefs: {},
        errormsg: []
    };
    error(ast, msg, stop) {
        this.state.errormsg.push({ ast, msg });
        ast.err = msg;
        if (stop)
            throw msg;
    }
    checkType(ast, context = {}, outast, infered) {
        let errmsg;
        this.state.inferId = infered ? Object.keys(infered).length : 0;
        this.state.inferValues = infered ?? {};
        this.state.errormsg = [];
        const nast = this.preprocessInfered(ast);
        this.state.activeAst = nast;
        try {
            this.check(nast, context, false);
        }
        catch (e) {
            errmsg = e;
        }
        try {
            this.afterCheckType(nast, ast);
        }
        catch (e) { }
        if (this.state.errormsg.length)
            throw this.state.errormsg[0].msg;
        if (errmsg)
            throw errmsg;
        if (outast) {
            Core.assign(outast, nast);
            while (Core.replaceByMatch(outast, this.state.inferValues, /^\?/))
                ;
        }
        return ast.checked;
    }
    /** a preproccess for replace every "_"s with "?id", where id is distinct for each one.
     * @param [cloned=false] internal usage, leave it blank.
     * @returns a cloned ast after replacement
     */
    preprocessInfered(ast, cloned = false) {
        if (!cloned)
            ast = Core.clone(ast);
        delete ast.err;
        if (ast.nodes) {
            for (const n of ast.nodes) {
                this.preprocessInfered(n, true);
            }
        }
        else if (ast.type === "var") {
            if (ast.name === "_")
                ast.name = "?" + (this.state.inferId++);
            // if (ast.name[0] === "?") ast.name = "?" + (this.state.inferId++);
        }
        return ast;
    }
    /** assign information in new ast to original ast and finish type checking */
    afterCheckType(nast, ast) {
        if (nast.checked) {
            let maxReplacement = Object.keys(this.state.inferValues).length + 1;
            while (maxReplacement-- && Core.replaceByMatch(nast.checked, this.state.inferValues, /^\?/))
                ;
        }
        ast.checked = nast.checked;
        ast.err = nast.err;
        if (ast.nodes)
            for (let i = 0; i < ast.nodes.length; i++) {
                this.afterCheckType(nast.nodes[i], ast.nodes[i]);
            }
        if (ast.checked) {
            this.reduce(ast.checked);
            Compute.hideinfferd(ast.checked);
        }
    }
    /** dgb */
    showInfered() {
        return Object.entries(this.state.inferValues).map(([k, v]) => [k, parser.stringify(v)]);
    }
    check(ast, context, ignoreErr) {
        // pick cache
        if (ast.checked)
            return ast.checked;
        // in Universe level, context is always {"*":"U@"}
        if (context["*"])
            return context["*"];
        if (ast.type === "var") {
            // variable in condition
            ast.checked ??= context[ast.name];
            if (ast.checked)
                return ast.checked;
            // const in environment
            ast.checked ??= this.checkConst(ast.name);
            if (ast.checked) {
                let maxReplacement = Object.keys(this.state.inferValues).length + 1;
                while (maxReplacement-- && Core.replaceByMatch(ast.checked, this.state.inferValues, /^\?/))
                    ;
                return ast.checked;
            }
            // a variable to be infered
            if (ast.name.startsWith("?")) {
                ast.checked = wrapVar(ast.name + ":");
                return ast.checked;
            }
            this.error(ast, TR("未知的变量：") + ast.name, ignoreErr);
            return;
        }
        if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            // if (this.checkConst(ast.name)) {
            //     this.error(ast.nodes[0], `参数变量${ast.name}不能是常量符号`, ignoreErr);
            // }
            // #check domain -> U
            const domain = ast.nodes[0];
            const Udomain = UniverseLevel.get(this.check(domain, context, ignoreErr));
            if (Udomain === false)
                this.error(domain, TR(`函数参数类型不合法`), ignoreErr);
            // #check codomain
            const subCtxt = assignContext({ [ast.name]: domain }, context);
            const codomain = this.check(ast.nodes[1], subCtxt, ignoreErr);
            if (ast.type === "L") {
                // if (Core.getFreeVars(codomain).has(ast.name)) {
                // reffering
                ast.checked = wrapLambda("P", ast.name, domain, codomain);
                // } else {
                //     // reffering
                //     ast.checked = { type: "->", name: "", nodes: [domain, codomain] };
                // }
            }
            else if (ast.type === "P" || ast.type === "S") {
                const Ucodomain = UniverseLevel.get(codomain);
                if (Ucodomain === false)
                    this.error(ast.nodes[1], TR(`函数返回类型不合法`), ignoreErr);
                // todo: deal with inferred type
                ast.checked = UniverseLevel.max(domain.checked, codomain);
            }
            return ast.checked;
        }
        if (ast.type === "->") {
            const domain = this.check(ast.nodes[0], context, ignoreErr);
            const Udomain = UniverseLevel.get(domain);
            if (Udomain === false)
                this.error(ast.nodes[0], TR(`函数参数类型不合法`), ignoreErr);
            const codomain = this.check(ast.nodes[1], context, ignoreErr);
            const Ucodomain = UniverseLevel.get(codomain);
            if (Ucodomain === false)
                this.error(ast.nodes[1], TR(`函数返回类型不合法`), ignoreErr);
            ast.checked = UniverseLevel.max(domain, codomain);
            return ast.checked;
        }
        if (ast.type === "apply") {
            if (ast.nodes[0].name === "U") {
                ast.checked = UniverseLevel.succ(ast);
                return ast.checked;
            }
            let tfn = this.check(ast.nodes[0], context, ignoreErr);
            while (tfn?.name?.startsWith("?")) {
                const rfn = this.state.inferValues[tfn.name];
                if (!rfn)
                    this.error(ast, TR("函数作用导致类型推断信息丢失"), ignoreErr);
                tfn = rfn;
            }
            const tap = this.check(ast.nodes[1], context, ignoreErr);
            if (!tfn || !tap)
                return;
            if (!tfn.nodes)
                this.error(ast, TR("非函数尝试作用"), ignoreErr);
            if (!this.equal(tfn.nodes[0], tap, context)) {
                this.error(ast, TR("函数作用类型不匹配"), ignoreErr);
                // ast.checked = wrapVar("函数作用类型不匹配");
            }
            else if (tfn.type === "->") {
                // reffering
                ast.checked = tfn.nodes[1];
            }
            else if (tfn.type === "P") {
                const repl = Core.clone(tfn.nodes[1]);
                // reffering
                this.replaceVar(repl, tfn.name, ast.nodes[1]);
                this.reduce(repl);
                ast.checked = repl;
            }
            return ast.checked;
        }
        if (ast.type === "X" || ast.type === "," || ast.type === "+") {
            this.check(ast.nodes[0], context, ignoreErr);
            this.check(ast.nodes[1], context, ignoreErr);
            ast.checked = this.check(this.desugar(ast), context, ignoreErr);
            return ast.checked;
        }
        // Type assertion
        if (ast.type === ":") {
            const type = this.check(ast.nodes[0], context, ignoreErr);
            this.check(ast.nodes[1], context, ignoreErr);
            const assertion = this.equal(type, ast.nodes[1], context);
            if (!assertion) {
                this.error(ast, TR("类型断言失败"), ignoreErr);
            }
            let maxReplacement = Object.keys(this.state.inferValues).length + 1;
            while (maxReplacement-- && Core.replaceByMatch(ast.nodes[1].checked, this.state.inferValues, /^\?/))
                ;
            this.check(type, context, false);
            maxReplacement = Object.keys(this.state.inferValues).length + 1;
            while (maxReplacement-- && Core.replaceByMatch(type.checked, this.state.inferValues, /^\?/))
                ;
            const assertionType = this.equal(type.checked, ast.nodes[1].checked, context);
            if (!assertionType) {
                this.error(ast, TR("类型断言失败"), ignoreErr);
            }
            return ast.nodes[1];
        }
        if (ast.type === "===") {
            if (Core.exactEqual(ast.nodes[0], ast.nodes[1])) {
                ast.checked = this.check(ast.nodes[0], context, ignoreErr);
                return ast.checked;
            }
            const assertion = this.equal(ast.nodes[0], ast.nodes[1], context);
            this.check(ast.nodes[0], context, ignoreErr);
            this.check(ast.nodes[1], context, ignoreErr);
            if (!assertion) {
                this.error(ast, TR("定义相等断言失败"), ignoreErr);
                return;
            }
            // let ta0 = ast.nodes[0].checked; while (ta0.nodes) ta0 = ta0.nodes[0];
            // let ta1 = ast.nodes[1].checked; while (ta1.nodes) ta1 = ta1.nodes[0];
            let assertionT;
            try {
                let maxReplacement = Object.keys(this.state.inferValues).length + 1;
                while (maxReplacement-- && Core.replaceByMatch(ast.nodes[0].checked, this.state.inferValues, /^\?/))
                    ;
                maxReplacement = Object.keys(this.state.inferValues).length + 1;
                while (maxReplacement-- && Core.replaceByMatch(ast.nodes[1].checked, this.state.inferValues, /^\?/))
                    ;
                assertionT = this.equal(ast.nodes[0].checked, ast.nodes[1].checked, context);
            }
            catch (e) {
                // trick for bugs: compare U (max @1 (@1 ....?1 ?2)) with U (max @1 (@1 ....?3 ?4)) will throw error
                // if (ta0.name === "U" && ta1.name === "U") {
                //     ast.checked = ast.nodes[0].checked;
                //     return ast.nodes[0].checked;
                // }
                throw e;
            }
            if (!assertionT) {
                this.error(ast, TR("定义相等断言失败"), ignoreErr);
                return;
            }
            ast.checked = ast.nodes[0].checked;
            return ast.checked;
        }
        if (ast.type === ":=") {
            return ast.nodes[0].checked;
        }
    }
    desugar(ast) {
        if (ast.type === "X") {
            const nast = this.preprocessInfered(parser.parse("@Prod _ _ ?A (Lx:?A.?B)"), true);
            nast.nodes[0].nodes[1] = ast.nodes[0];
            nast.nodes[1].nodes[0] = ast.nodes[0];
            nast.nodes[1].nodes[1] = ast.nodes[1];
            return nast;
        }
        else if (ast.type === "+") {
            const nast = this.preprocessInfered(parser.parse("@Sum _ _ ?A ?B"), true);
            nast.nodes[0].nodes[1] = ast.nodes[0];
            nast.nodes[1] = ast.nodes[1];
            return nast;
        }
        else if (ast.type === ",") {
            const nast = this.preprocessInfered(parser.parse("@pair _ _ _ (Lx:?a：.?b：) ?a ?b"), true);
            const dfn = nast.nodes[0].nodes[0].nodes[1];
            dfn.nodes[0] = ast.nodes[0].checked;
            dfn.nodes[1] = ast.nodes[1].checked;
            nast.nodes[0].nodes[1] = ast.nodes[0];
            nast.nodes[1] = ast.nodes[1];
            return nast;
        }
        throw "cannnot reached";
    }
    checkConst(n) {
        // sys types
        let res = this.state.sysTypes[n];
        if (res)
            return res;
        // sys/user Defs
        res = this.state.sysDefs[n] || this.state.userDefs[n];
        if (["add", "natO", "leqO"].includes(n) && res?.checked)
            return res.checked;
        if (res)
            return this.check(this.preprocessInfered(res), {}, false);
        // @i : U@
        if (n[0] === "@" && NatLiteral.is(n.slice(1)))
            return wrapVar("U@");
        // 12345: nat
        if (NatLiteral.is(n))
            return wrapVar("nat");
        // unknown
        return null;
    }
    equal(a, b, context, moveSemantic, depth = Infinity) {
        if (depth < 1)
            return false;
        if (a === b || Core.exactEqual(a, b))
            return true;
        // type "U@" and "U@:" are equal
        if (a.name?.startsWith("U@") && b.name?.startsWith("U@"))
            return true;
        // infered value matched
        if (a.name?.startsWith("?")) {
            const name = a.name;
            return this.mergeInfered({ [name]: b, [name + ":"]: this.check(b, context, false) }, context, depth);
        }
        else if (b.name?.startsWith("?")) {
            const name = b.name;
            return this.mergeInfered({ [name]: a, [name + ":"]: this.check(a, context, false) }, context, depth);
        }
        // -> may not be real nondependent fn type, since it may infer bounded var
        if ((a.type === "->" && b.type === "P") || (b.type === "->" && a.type === "P")) {
            if (this.equal(a.nodes[0], b.nodes[0], context, moveSemantic, depth) &&
                this.equal(a.nodes[1], b.nodes[1], assignContext({ [a.name || b.name]: a.nodes[0] }, context), moveSemantic, depth)) {
                a.name = a.name || b.name;
                b.name = b.name || a.name;
                a.type = "P";
                b.type = "P";
                return true;
            }
        }
        // -> may not be real nondependent prod type, since it may infer bounded var
        if ((a.type === "X" && b.type === "S") || (b.type === "X" && a.type === "S")) {
            if (this.equal(a.nodes[0], b.nodes[0], context, moveSemantic, depth) &&
                this.equal(a.nodes[1], b.nodes[1], assignContext({ [a.name || b.name]: a.nodes[0] }, context), moveSemantic, depth)) {
                a.name = a.name || b.name;
                b.name = b.name || a.name;
                a.type = "S";
                b.type = "S";
                return true;
            }
        }
        if ((a.type === "," && b.type === "apply") || (b.type === "," && a.type === "apply")) {
            const xa = a.type === "," ? a : b;
            let xb = b.type === "," ? a : b;
            if (this.equal(xa.nodes[1], xb.nodes[1], context, moveSemantic, depth) &&
                xb.nodes[0].type === "apply" &&
                this.equal(xa.nodes[0], xb.nodes[0].nodes[1], context, moveSemantic, depth)) {
                let level = 0;
                while (xb.nodes && xb.nodes[0]) {
                    xb = xb.nodes[0];
                    level++;
                }
                if (xb.name === "pair" && level === 3)
                    return true;
                if (xb.name === "@pair" && level === 6)
                    return true;
            }
        }
        // fn alpha conversion
        if (a.type === b.type && (a.type === "L" || a.type === "P" || a.type === "S")) {
            if (!this.equal(a.nodes[0], b.nodes[0], context, moveSemantic, depth))
                return false;
            if (a.name === b.name)
                return this.equal(a.nodes[1], b.nodes[1], assignContext({ [a.name]: a.nodes[0] }, context));
            const tempA1 = Core.clone(a.nodes[1]);
            this.replaceVar(tempA1, a.name, wrapVar(b.name));
            return this.equal(b.nodes[1], tempA1, assignContext({ [b.name]: b.nodes[0] }, context), moveSemantic, depth);
            // const tempB1 = Core.clone(b.nodes[1]);
            // this.replaceVar(tempB1, b.name, wrapVar(a.name));
            // return this.equal(a.nodes[1], tempB1, assignContext({ [a.name]: a.nodes[0] }, context));
        }
        if (Object.keys(this.state.inferValues).length > 2048) {
            return false; // two many infereds, something bad happens
        }
        if (a.name.startsWith("@") && b.type === "apply" && b.nodes[0].name === "@succ" && isFinite(Number(a.name.slice(1)))) {
            try {
                const i = BigInt(a.name.slice(1)) - 1n;
                return this.equal(wrapVar("@" + i), b.nodes[1], context, moveSemantic);
            }
            catch (e) { }
        }
        else if (b.name.startsWith("@") && a.type === "apply" && a.nodes[0].name === "@succ" && isFinite(Number(b.name.slice(1)))) {
            try {
                const i = BigInt(b.name.slice(1)) - 1n;
                return this.equal(wrapVar("@" + i), a.nodes[1], context, moveSemantic);
            }
            catch (e) { }
        }
        if (context["*"]) {
            UniverseLevel.reduceLvl(a);
            UniverseLevel.reduceLvl(b);
            if (a.type === "apply" && a.nodes[0].type === "apply" && a.nodes[0].nodes[0].name === "@max" &&
                b.type === "apply" && b.nodes[0].type === "apply" && b.nodes[0].nodes[0].name === "@max") {
                return this.equal(a.nodes[0].nodes[1], b.nodes[0].nodes[1], context, moveSemantic, Math.min(1, depth - 1)) && this.equal(a.nodes[1], b.nodes[1], context, moveSemantic, Math.min(1, depth - 1));
            }
            return this.equal(a, b, context, moveSemantic, Math.min(1, depth - 1));
        }
        // expand defs
        const a1 = moveSemantic ? a : Core.clone(a);
        const b1 = moveSemantic ? b : Core.clone(b);
        let modified = false;
        modified ||= this.reduce(a1, true);
        modified ||= this.reduce(b1, true);
        modified ||= Compute.exec(a1);
        modified ||= Compute.exec(b1);
        // recurse
        if (a1.type === b1.type && a1.name == b1.name && a1.nodes?.length === b1.nodes?.length) {
            let oldContext = context;
            if (a1.type === "apply" && a1.nodes[0].name === "U" && b1.nodes[0].name === "U") {
                context = { "*": wrapVar("U@") };
            }
            let breaked = false;
            for (let i = 0; i < a1.nodes?.length; i++) {
                if (!this.equal(a1.nodes[i], b1.nodes[i], context, true, depth)) {
                    breaked = true;
                    break;
                }
            }
            if (!breaked)
                return true;
            context = oldContext;
        }
        modified ||= this.expandDef(a1);
        modified ||= this.expandDef(b1);
        if (modified)
            return this.equal(a1, b1, context, true, depth - 1);
        return false;
    }
    mergeInfered(added, context, depth = Infinity) {
        const vals = this.state.inferValues;
        for (const [k, v] of Object.entries(added)) {
            if (k.endsWith("::"))
                continue;
            vals[k] ??= v;
            if (!this.equal(vals[k], v, context, true, depth)) {
                if (!vals[v.name] || !this.equal(vals[k], vals[v.name], context, true, depth)) {
                    return false;
                }
            }
            // }
            for (const val of Object.values(vals)) {
                this.replaceVar(val, k, v, context);
            }
            this.replaceVar(this.state.activeAst, k, v, context);
            this.replaceVarInChecked(this.state.activeAst, k, v, context);
        }
        return true;
    }
    /** lambda reduce, def expands are not inclueded */
    reduce(ast, dependent) {
        if (ast.type === "P" && !dependent) {
            // nondependenet func to ->
            const m1 = this.reduce(ast.nodes[0]);
            const m2 = this.reduce(ast.nodes[1]);
            const codomain = ast.nodes[1];
            if (!this.state.disableSimpleFn && !Core.getFreeVars(codomain).has(ast.name)) {
                ast.name = "";
                ast.type = "->";
                return true;
            }
            return m1 || m2;
        }
        else if (ast.type === "S" && !dependent) {
            // nondependenet func to ->
            const m1 = this.reduce(ast.nodes[0]);
            const m2 = this.reduce(ast.nodes[1]);
            const codomain = ast.nodes[1];
            if (!this.state.disableSimpleFn && !Core.getFreeVars(codomain).has(ast.name)) {
                ast.name = "";
                ast.type = "X";
                return true;
            }
            return m1 || m2;
        }
        else if (ast.type === "apply") {
            const [fn, ap] = ast.nodes;
            if (fn.type === "L") {
                // beta-reduction
                const nt1 = Core.clone(fn.nodes[1]);
                this.replaceVar(nt1, fn.name, ap);
                Core.assign(ast, nt1, true);
                this.reduce(ast);
                return true;
            }
            else if (fn.name === "U") {
                // universe level reduce
                return UniverseLevel.reduce(ast);
            }
            else {
                const m1 = this.reduce(ast.nodes[0]);
                const m2 = this.reduce(ast.nodes[1]);
                return m1 || m2;
            }
        }
        else if (ast.type === "L") {
            const [domain, body] = ast.nodes;
            if (body.type === "apply" && body.nodes[1].name === ast.name && !Core.getFreeVars(body.nodes[0]).has(ast.name)) {
                // iota-reduction (func uniqueless)
                Core.assign(ast, body.nodes[0], true);
                this.reduce(ast);
                return true;
            }
            else {
                const m1 = this.reduce(ast.nodes[0]);
                const m2 = this.reduce(ast.nodes[1]);
                return m1 || m2;
            }
        }
        else if (ast.nodes?.length === 2) {
            const m1 = this.reduce(ast.nodes[0]);
            const m2 = this.reduce(ast.nodes[1]);
            return m1 || m2;
        }
        else if (ast.name[0] === "?") {
            let nast = ast;
            let length = Object.keys(this.state.inferValues).length + 1;
            while (nast.name[0] === "?" && length) {
                const temp = this.state.inferValues[nast.name];
                if (!temp)
                    break;
                // if(temp.name < nast.name) break; // stop infer, something bad will happen
                nast = temp;
                length--;
            }
            if (length && nast !== ast) { // modified, and ignore loop quot
                Core.assign(ast, nast);
                return true;
            }
        }
        return false;
    }
    static exactEqual(ast1, ast2) {
        if (ast1 === ast2)
            return true;
        if (ast1.type !== ast2.type)
            return false;
        if (ast1.name != ast2.name)
            return false; // undefined == null but !== null
        if (ast1.nodes?.length !== ast2.nodes?.length)
            return false;
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.exactEqual(ast1.nodes[i], ast2.nodes[i]))
                    return false;
            }
        }
        return true;
    }
    expandDef(ast, specified) {
        if (ast.type === "var") {
            if (specified && !specified.has(ast.name))
                return false;
            // defined constant expansion
            const res = this.state.sysDefs[ast.name] || this.state.userDefs[ast.name];
            if (!res)
                return false;
            const nast = this.preprocessInfered(res);
            Core.assign(ast, nast, true);
            return true;
        }
        let modified = false;
        if (ast.nodes.length) {
            for (const n of ast.nodes) {
                if (this.expandDef(n, specified))
                    modified = true;
            }
        }
        return modified;
    }
}
class NatLiteral {
    static is(ast) {
        if (!ast)
            return false;
        return typeof ast === "string" ? ast === "0" || ast.match(/^[1-9][0-9]*$/) : ast.type === "var" && (ast.name === "0" || ast.name.match(/^[1-9][0-9]*$/));
    }
}
class UniverseLevel {
    static reduce(ast) {
        if (ast.type === "apply" && ast.nodes[0].name === "U") {
            if (ast.nodes[1].type !== "apply")
                return false;
            return UniverseLevel.reduceLvl(ast.nodes[1]);
        }
        return false;
    }
    static reduceLvl(ast) {
        if (ast.type === "var")
            return false;
        if (ast.type !== "apply")
            throw TR("未知的全类层级运算");
        if (ast.nodes[0].name === "@succ") {
            const modified = this.reduceLvl(ast.nodes[1]);
            if (ast.nodes[1].name[0] !== "@")
                return modified;
            const s = ast.nodes[1].name.slice(1);
            if (NatLiteral.is(s)) {
                ast.nodes[1].name = "@" + String(Number(s) + 1);
                Core.assign(ast, ast.nodes[1], true);
                return true;
            }
            return modified;
        }
        if (ast.nodes[0].type !== "apply")
            throw TR("未知的全类层级运算");
        if (ast.nodes[0].nodes[0].name !== "@max")
            throw TR("未知的全类层级运算");
        const modified1 = this.reduceLvl(ast.nodes[0].nodes[1]);
        const modified2 = this.reduceLvl(ast.nodes[1]);
        // max(a,0)=a
        if (ast.nodes[0].nodes[1].name === "@0") {
            Core.assign(ast, ast.nodes[1], true);
            return true;
        }
        // max(0,a)=a
        if (ast.nodes[1].name === "@0") {
            Core.assign(ast, ast.nodes[0].nodes[1], true);
            return true;
        }
        // max(a,a)=a
        if (Core.exactEqual(ast.nodes[0].nodes[1], ast.nodes[1])) {
            Core.assign(ast, ast.nodes[1], true);
            return true;
        }
        if (ast.nodes[0].nodes[1].name[0] !== "@")
            return modified1 || modified2;
        if (ast.nodes[1].name[0] !== "@")
            return modified1 || modified2;
        const s1 = ast.nodes[0].nodes[1].name.slice(1);
        const s2 = ast.nodes[1].name.slice(1);
        if (NatLiteral.is(s1) && NatLiteral.is(s2)) {
            ast.nodes[1].name = "@" + String(Math.max(Number(s1), Number(s2)));
            Core.assign(ast, ast.nodes[1], true);
            return true;
        }
        return modified1 || modified2;
    }
    static succ(ast) {
        const u = UniverseLevel.get(ast);
        if (typeof u === "number") {
            return wrapU("@" + String(u + 1));
        }
        if (u === false)
            throw TR("尝试对非全类操作层级");
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
    static max(a, b) {
        const u = UniverseLevel.get(a);
        const v = UniverseLevel.get(b);
        if (typeof u === "number" && typeof v === "number") {
            return wrapApply(wrapVar("U"), wrapVar("@" + String(Math.max(u, v))));
        }
        if (u === false || v === false)
            throw TR("尝试对非全类操作层级");
        if (a.type === "var" || b.type === "var")
            return wrapApply(wrapVar("U"), wrapVar("?"));
        return {
            type: "apply", name: "", nodes: [
                wrapVar("U"),
                wrapApply(wrapVar("@max"), Core.clone(a.nodes[1]), Core.clone(b.nodes[1]))
            ]
        };
    }
    /** check whether ast is universe, return its level number, if level is not given return true, if it is not universe, return false */
    static get(ast) {
        if (ast.type === "var" && ast.name === "U") {
            return 0;
        }
        if (ast.type === "var" && ast.name.endsWith(":")) {
            // an unknown inffered type
            return true;
        }
        if (ast.type === "apply" && ast.nodes[0].name === "U") {
            if (ast.nodes[1].name[0] === "@") {
                const s = ast.nodes[1].name.slice(1);
                if (NatLiteral.is(s))
                    return Number(s);
            }
            return true;
        }
        return false;
    }
}
export class Compute {
    static isApplyBrach(ast) {
        if (ast.type !== "apply")
            return false;
        return ast.nodes[0].name !== "U";
    }
    static matchApply(ast, root = true, res = []) {
        if (!root) {
            if (this.isApplyBrach(ast)) {
                this.matchApply(ast.nodes[1], true, res);
                this.matchApply(ast.nodes[0], false, res);
                res[0][0] = ast;
                res[0].push(ast.nodes[1]);
            }
            else {
                if (ast.nodes?.length === 2) {
                    this.matchApply(ast.nodes[0], true, res);
                    this.matchApply(ast.nodes[1], true, res);
                }
                res.unshift([ast, ast]);
            }
        }
        else {
            if (this.isApplyBrach(ast)) {
                this.matchApply(ast.nodes[1], true, res);
                this.matchApply(ast.nodes[0], false, res);
                res[0][0] = ast;
                res[0].push(ast.nodes[1]);
            }
            else {
                if (ast.nodes?.length === 2) {
                    this.matchApply(ast.nodes[0], true, res);
                    this.matchApply(ast.nodes[1], true, res);
                }
            }
        }
        return res;
    }
    static exec(ast) {
        const applyRes = this.matchApply(ast, true).reverse();
        let modified = false;
        let tempReduce = []; // [&AST, oldAST]
        for (const matched of applyRes) {
            if (matched[1]?.type !== "var")
                continue;
            const fn = matched[1].name;
            let ast = matched[0];
            // temporal reduce, for later matching (e.g. ind_eq ... @refl)
            // @@ref u nat 1 := refl
            if (fn === "@refl" && matched.length > 4) {
                tempReduce.push([ast, Core.clone(ast)]);
                Core.assign(ast, wrapVar("rfl"), true);
                continue;
            }
            if (fn === "refl" && matched.length > 2) {
                tempReduce.push([ast, Core.clone(ast)]);
                Core.assign(ast, wrapVar("rfl"), true);
                continue;
            }
            // temporal reduce, for later matching (e.g. ind_Prod ... @pair)
            if (fn === "@pair" && matched.length > 4) {
                let tail = matched.length - 5;
                while (tail--)
                    ast = ast.nodes[0];
                tempReduce.push([ast, Core.clone(ast)]);
                Core.assign(ast, wrapVar("pair"), true);
                continue;
            }
            // indTrue _ c true := c
            if (fn === "ind_True" && matched.length > 4 && matched[4].name === "true") {
                let tail = matched.length - 5;
                while (tail--)
                    ast = ast.nodes[0];
                Core.assign(ast, matched[3], true);
                modified = true;
                continue;
            }
            if (fn === "@ind_True" && matched.length > 5 && matched[5].name === "true") {
                let tail = matched.length - 6;
                while (tail--)
                    ast = ast.nodes[0];
                Core.assign(ast, matched[4], true);
                modified = true;
                continue;
            }
            // ind_Prod _ C c (pair _ a b) := c
            if (fn === "ind_Prod" && matched.length > 5) {
                const val = matched[5];
                let tail = matched.length - 6;
                while (tail--)
                    ast = ast.nodes[0];
                if (val.type === ",") {
                    Core.assign(ast, wrapApply(matched[4], val.nodes[0], val.nodes[1]), true);
                    modified = true;
                    continue;
                }
                else if (val.type === "apply" && val.nodes[0].type === "apply" && val.nodes[0].nodes[0].type === "apply" && val.nodes[0].nodes[0].nodes[0].name === "pair") {
                    Core.assign(ast, wrapApply(matched[4], val.nodes[0].nodes[1], val.nodes[1]), true);
                    modified = true;
                    continue;
                }
            }
            // indBool _ c0 c1 0b||1b := c0||c1
            if (fn === "ind_Bool" && matched.length > 5) {
                if (matched[5].name === "0b") {
                    let tail = matched.length - 6;
                    while (tail--)
                        ast = ast.nodes[0];
                    Core.assign(ast, matched[3], true);
                    modified = true;
                    continue;
                }
                else if (matched[5].name === "1b") {
                    let tail = matched.length - 6;
                    while (tail--)
                        ast = ast.nodes[0];
                    Core.assign(ast, matched[4], true);
                    modified = true;
                    continue;
                }
            }
            if (fn === "@ind_Bool" && matched.length > 6) {
                if (matched[6].name === "0b") {
                    let tail = matched.length - 7;
                    while (tail--)
                        ast = ast.nodes[0];
                    Core.assign(ast, matched[4], true);
                    modified = true;
                    continue;
                }
                else if (matched[6].name === "1b") {
                    let tail = matched.length - 7;
                    while (tail--)
                        ast = ast.nodes[0];
                    Core.assign(ast, matched[5], true);
                    modified = true;
                    continue;
                }
            }
            // indEqa A _ c a refla := 
            if (fn === "ind_eq" && matched.length > 6) {
                if (matched[6].name === "rfl") {
                    // if (Core.exactEqual(matched[2], matched[5]) && matched[6].name === "rfl") {
                    let tail = matched.length - 7;
                    while (tail--)
                        ast = ast.nodes[0];
                    Core.assign(ast, matched[4], true);
                    modified = true;
                    continue;
                }
            }
            if (fn === "@ind_eq" && matched.length > 9) {
                if (matched[9].name === "rfl") {
                    // already checked type, noneed to check "indeq x _ _ x m: eq x x", if two xs are inffered, there may be error
                    // if (Core.exactEqual(matched[5], matched[8]) && matched[9].name === "rfl") {
                    let tail = matched.length - 10;
                    while (tail--)
                        ast = ast.nodes[0];
                    Core.assign(ast, matched[7], true);
                    modified = true;
                    continue;
                }
            }
            // indnat C 0 s num
            if (fn === "ind_nat" && matched.length > 5) {
                // indnat C c0 cs 0 = c0
                if (matched[5].name === "0") {
                    let tail = matched.length - 6;
                    while (tail--)
                        ast = ast.nodes[0];
                    Core.assign(ast, matched[3], true);
                    modified = true;
                    continue;
                }
                // indnat C c0 cs (succ ?) = cs ? indnat C c0 cs (?)
                if (matched[5].type === "apply" && matched[5].nodes[0].name === "succ") {
                    let tail = matched.length - 6;
                    while (tail--)
                        ast = ast.nodes[0];
                    const cn = matched[5].nodes[1];
                    Core.assign(ast, wrapApply(matched[4], cn, wrapApply(matched[1], matched[2], matched[3], matched[4], cn)), true);
                    modified = true;
                    continue;
                }
                // indnat C c0 cs num = cs ? indnat C c0 cs (?)
                if (isFinite(Number(matched[5].name))) {
                    let b = BigInt(matched[5].name);
                    let tail = matched.length - 6;
                    while (tail--)
                        ast = ast.nodes[0];
                    let c0 = matched[3];
                    let cs = matched[4];
                    if (cs.type === "L" && cs.nodes[1].type === "L" && !Core.getFreeVars(cs.nodes[1].nodes[1]).has(cs.nodes[1].name)) {
                        Core.assign(ast, wrapApply(matched[4], wrapVar(String(b - 1n)), wrapVar("??")), true);
                        modified = true;
                        continue;
                    }
                    let expandDepth = 2;
                    // indnat C c0 cs 5 = cs 4 (cs 3 (cs 2 (cs 1(c0))))
                    let nast = ast;
                    while (true) {
                        expandDepth--;
                        if (b === 0n) {
                            Core.assign(nast, c0);
                            break;
                        }
                        Core.assign(nast, wrapApply(cs, wrapVar(String(b)), wrapVar("??")));
                        nast = nast.nodes[1];
                        b--;
                        if (!expandDepth) {
                            Core.assign(nast, wrapApply(matched[1], matched[2], c0, cs, wrapVar(String(b))));
                        }
                    }
                    modified = true;
                    continue;
                }
            }
            if (fn === "add" && matched.length > 3) {
                // add 1 2 := 1+2
                if (matched[2].type === "var" && matched[3].type === "var" && isFinite(Number(matched[2].name)) && isFinite(Number(matched[3].name))) {
                    try {
                        const bint = BigInt(matched[2].name) + BigInt(matched[3].name);
                        Core.assign(ast, wrapVar(String(bint)), true);
                        modified = true;
                        continue;
                    }
                    catch (e) { }
                }
                // add x 0 := x
                if (matched[3].name === "0" && matched[3].type === "var") {
                    try {
                        Core.assign(ast, matched[2], true);
                        modified = true;
                        continue;
                    }
                    catch (e) { }
                }
                const dstrct = matched[3];
                // add x (succ y)
                if (dstrct.type === "apply" && dstrct.nodes[0].name === "succ") {
                    try {
                        // remove inner succ
                        Core.assign(dstrct, dstrct.nodes[1], true);
                        // add outter succ
                        Core.assign(ast, wrapApply(wrapVar("succ"), ast)); // when wrap, soor move
                        modified = true;
                        continue;
                    }
                    catch (e) { }
                }
            }
            if (fn === "succ" && matched.length > 2 && matched[2].type === "var") {
                try {
                    const bint = BigInt(matched[2].name);
                    Core.assign(ast, wrapVar(String(bint + 1n)), true);
                    modified = true;
                    continue;
                }
                catch (e) { }
            }
            if (fn === "double" && matched.length > 2) {
                const dstrct = matched[2];
                // double (succ y)
                if (dstrct.type === "apply" && dstrct.nodes[0].name === "succ") {
                    try {
                        // remove inner succ
                        Core.assign(dstrct, dstrct.nodes[1], true);
                        // add outter succ
                        Core.assign(ast, wrapApply(wrapVar("succ"), wrapApply(wrapVar("succ"), ast))); // when wrap, soor move
                        modified = true;
                        continue;
                    }
                    catch (e) { }
                }
                if (matched[2].type === "var") {
                    try {
                        const bint = BigInt(matched[2].name);
                        Core.assign(ast, wrapVar(String(bint * 2n)), true);
                        modified = true;
                        continue;
                    }
                    catch (e) { }
                }
            }
            if (fn === "pred" && matched.length > 2 && matched[2].type === "var") {
                if (matched[2].name === "0") {
                    Core.assign(ast, wrapVar("0"), true);
                    modified = true;
                    continue;
                }
                else
                    try {
                        const bint = BigInt(matched[2].name);
                        Core.assign(ast, wrapVar(String(bint - 1n)), true);
                        modified = true;
                        continue;
                    }
                    catch (e) { }
            }
            if (fn === "mul" && matched.length > 3 && matched[2].type === "var" && matched[3].type === "var") {
                // mul 1 2 := 1*2
                try {
                    const bint = BigInt(matched[2].name) * BigInt(matched[3].name);
                    Core.assign(ast, wrapVar(String(bint)), true);
                    modified = true;
                    continue;
                }
                catch (e) { }
            }
            // indord C 0 s l ord
            if (fn === "ind_Ord" && matched.length > 6) {
                // indnat C c0 cs 0 = c0
                if (matched[6].name === "0O") {
                    let tail = matched.length - 7;
                    while (tail--)
                        ast = ast.nodes[0];
                    Core.assign(ast, matched[3], true);
                    modified = true;
                    continue;
                }
                // ind C c0 cs cl (succ ?) = cs ? ind C c0 cs cl (?)
                if (matched[6].type === "apply" && matched[6].nodes[0].name === "succO") {
                    let tail = matched.length - 7;
                    while (tail--)
                        ast = ast.nodes[0];
                    const cn = matched[6].nodes[1];
                    Core.assign(ast, wrapApply(matched[4], cn, wrapApply(matched[1], matched[2], matched[3], matched[4], matched[5], cn)), true);
                    modified = true;
                    continue;
                }
                // ind C c0 cs cl (lim ?) = cs ? ind C c0 cs cl (?)
                if (matched[6].type === "apply" && matched[6].nodes[0].name === "limO") {
                    let tail = matched.length - 7;
                    while (tail--)
                        ast = ast.nodes[0];
                    const cf = matched[6].nodes[1];
                    Core.assign(ast, wrapApply(matched[5], cf, { type: "L", name: "n", nodes: [wrapVar("nat"), wrapApply(matched[1], matched[2], matched[3], matched[4], matched[5], wrapApply(cf, wrapVar("n")))] }), true);
                    modified = true;
                    continue;
                }
            }
            // natO (succ x) : succO (natO x)
            if (fn === "natO" && matched.length > 2) {
                if (matched[2].type === "var" && isFinite(Number(matched[2].name))) {
                    let num = Number(matched[2].name);
                    while ((num) + 1) {
                        if (num-- === 0) {
                            Core.assign(ast, wrapVar("0O"), true);
                            break;
                        }
                        Core.assign(ast, wrapApply(wrapVar("succO"), wrapVar("")), true);
                        ast = ast.nodes[1];
                    }
                    modified = true;
                    continue;
                }
                if (matched[2].name === "0") {
                    Core.assign(ast, wrapVar("0O"), true);
                    modified = true;
                    continue;
                }
                if (matched[2].type === "apply" && matched[2].nodes[0].name === "succ") {
                    Core.assign(ast, wrapApply(wrapVar("succO"), wrapApply(matched[1], matched[2].nodes[1])), true);
                    modified = true;
                    continue;
                }
            }
            if (fn === "addO" && matched.length > 3) {
                // add 0 x : x
                if (matched[2].name === "0O") {
                    Core.assign(ast, matched[3], true);
                    modified = true;
                    continue;
                }
                // add succ x y : succ(add x y)
                if (matched[2].type === "apply" && matched[2].nodes[0].name === "succO") {
                    Core.assign(ast, wrapApply(wrapVar("succO"), wrapApply(wrapVar("addO"), matched[2].nodes[1], matched[3])), true);
                    modified = true;
                    continue;
                }
                // add lim f y : lim(Ln.add fn y)
                if (matched[2].type === "apply" && matched[2].nodes[0].name === "limO") {
                    Core.assign(ast, wrapApply(wrapVar("limO"), {
                        type: "L", name: "n", nodes: [
                            wrapVar("nat"),
                            wrapApply(wrapVar("addO"), wrapApply(matched[2].nodes[1], wrapVar("n")), matched[3])
                        ]
                    }), true);
                    modified = true;
                    continue;
                }
            }
            if (fn === "leqO" && matched.length > 3) {
                // 0 <= a : True
                if (matched[2].name === "0O") {
                    Core.assign(ast, wrapVar("True"), true);
                    modified = true;
                    continue;
                }
                if (matched[2].type === "apply" && matched[2].nodes[0].name === "succO") {
                    // succ a <= 0 : False
                    if (matched[3].name === "0O") {
                        Core.assign(ast, wrapVar("False"), true);
                        modified = true;
                        continue;
                    }
                    // succ a <= succ b : a <= b
                    if (matched[3].type === "apply" && matched[3].nodes[0].name === "succO") {
                        Core.assign(matched[2], matched[2].nodes[1], true);
                        Core.assign(matched[3], matched[3].nodes[1], true);
                        modified = true;
                        continue;
                    }
                    // succ a <= lim f : Sn, succ a <= fn
                    if (matched[3].type === "apply" && matched[3].nodes[0].name === "limO") {
                        Core.assign(ast, {
                            type: "S", name: "n", nodes: [wrapVar("nat"),
                                wrapApply(wrapVar("leqO"), matched[2], wrapApply(matched[3].nodes[1], wrapVar("n")))
                            ]
                        }, true);
                        modified = true;
                        continue;
                    }
                }
                // lim f <= a : Pn, fn <= a
                if (matched[2].type === "apply" && matched[2].nodes[0].name === "limO") {
                    Core.assign(ast, {
                        type: "P", name: "n", nodes: [wrapVar("nat"), wrapApply(wrapVar("leqO"), wrapApply(matched[2].nodes[1], wrapVar("n")), matched[3])]
                    }, true);
                    modified = true;
                    continue;
                }
            }
        }
        for (const [ptr_AST, oldAST] of tempReduce) {
            Core.assign(ptr_AST, oldAST, true);
        }
        return modified;
    }
    static hideinfferd(ast) {
        const applyRes = this.matchApply(ast, true).reverse();
        for (const matched of applyRes) {
            if (matched[1]?.type !== "var")
                continue;
            const fn = matched[1].name;
            let ast = matched[0];
            // temporal reduce, for later matching (e.g. ind_eq ... @@refl)
            // @@ref u nat 1:= @refl 1
            if (fn === "@refl" && matched.length > 3) {
                let tail = matched.length - 4;
                while (tail--)
                    ast = ast.nodes[0];
                const type = ast.checked;
                Core.assign(ast, wrapVar("refl"), true);
                ast.checked = type;
                continue;
            }
            // @indTrue _ := indTrue
            if ((fn === "@ind_True" || fn === "@ind_Bool" || fn === "@ind_False") && matched.length > 2) {
                let tail = matched.length - 3;
                while (tail--)
                    ast = ast.nodes[0];
                const type = ast.checked;
                Core.assign(ast, wrapVar(fn.slice(1)), true);
                ast.checked = type;
                continue;
            }
            // @indEq _ _ _ := indEq
            if (fn === "@ind_eq" && matched.length > 4) {
                let tail = matched.length - 5;
                while (tail--)
                    ast = ast.nodes[0];
                const type = ast.checked;
                Core.assign(ast, wrapVar(fn.slice(1)), true);
                ast.checked = type;
                continue;
            }
            // @eq _ A x y := eq x y
            if (fn === "@eq" && matched.length > 3) {
                let tail = matched.length - 4;
                while (tail--)
                    ast = ast.nodes[0];
                const type = ast.checked;
                Core.assign(ast, wrapVar("eq"), true);
                ast.checked = type;
                continue;
            }
        }
    }
}
//# sourceMappingURL=core.js.map