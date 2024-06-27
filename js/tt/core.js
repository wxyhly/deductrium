import { ASTParser } from "./astparser.js";
function wrapVar(v) {
    return { type: "var", name: v };
}
function wrapU(v) {
    return { type: "apply", name: "U", nodes: [wrapVar("U"), wrapVar(v)] };
}
function wrapLambda(type, param, paramType, body) {
    return { type, name: param, nodes: [paramType, body] };
}
function wrapApply(...terms) {
    let ast = terms.pop();
    let ast1;
    while (ast1 = terms.pop()) {
        ast = { type: "apply", nodes: [ast1, ast] };
    }
    return ast;
}
function assignContext(added, oldContext) {
    return Object.assign(Object.assign({}, oldContext), added);
}
export class Core {
    /** this parameter affect performance for definitional equal checking */
    expandStepsBetweenEqCheck = 1;
    static assign(ast, value, moveSemantic) {
        const v = moveSemantic ? value : this.clone(value);
        ast.type = v.type;
        ast.name = v.name;
        ast.nodes = v.nodes;
        ast.checked = v.checked;
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
    static replaceByMatch(ast, res) {
        if (!res)
            throw "未匹配";
        if (ast.type === "var" && ast.name.match(/^\?/)) {
            if (!res[ast.name])
                return;
            this.assign(ast, this.clone(res[ast.name]));
        }
        else if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this.replaceByMatch(n, res);
            }
        }
    }
    constsTypes = {
        "nat": wrapVar("U"),
        "bool": wrapVar("U"),
        "True": wrapVar("U"),
        "true": wrapVar("True"),
        "succ": { type: "->", nodes: [wrapVar("nat"), wrapVar("nat")] },
        "False": wrapVar("U"),
        "ind_nat": new ASTParser().parse("Pu:lvl,PC:Px:nat,Uu,Pc0:C 0,Pcs:(Px:nat,Py:C x,C (succ x)),Px:nat,C x"),
        "eq": new ASTParser().parse("Pu:lvl,Pa:Uu,a->a->Uu"),
        "refl": new ASTParser().parse("Pu:lvl,Pa:U u,Px:a,eq u a x x"),
        "Prod": new ASTParser().parse("Pu:lvl,Pv:Un,Pa:Uu,Pb:Uv,a->a->(Uu Uv)"),
    };
    constsDefs = {};
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
    static replaceVar(ast, name, dst, fvDst = this.getFreeVars(dst)) {
        if (ast.type === "var") {
            if (ast.name !== name)
                return;
            this.assign(ast, dst);
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            this.replaceVar(ast.nodes[0], name, dst, fvDst);
            if (ast.name === name)
                return; // bounded
            const fvSrcBody = this.getFreeVars(ast.nodes[1]);
            if (!fvSrcBody.has(name))
                return; // not bounded, but not found
            if (!fvDst.has(ast.name)) {
                this.replaceVar(ast.nodes[1], name, dst, fvDst);
            }
            else {
                const newName = this.getNewName(ast.name, new Set([...fvSrcBody, ...fvDst]));
                this.replaceVar(ast.nodes[1], ast.name, { type: "var", name: newName }, fvDst);
                this.replaceVar(ast.nodes[1], name, dst, fvDst);
                ast.name = newName;
            }
            return;
        }
        else if (ast.nodes?.length === 2) {
            this.replaceVar(ast.nodes[0], name, dst, fvDst);
            this.replaceVar(ast.nodes[1], name, dst, fvDst);
        }
    }
    checkConst(n) {
        const res = this.constsTypes[n];
        if (res)
            return res;
        let ulevel = 0;
        if (ulevel = UniverseLevel.is(n))
            return UniverseLevel.gen(ulevel + 1);
        if (NatLiteral.is(n))
            return wrapVar("nat");
        return null;
    }
    error(ast, msg) {
        ast.err = msg;
        throw msg;
    }
    checkType(ast, context) {
        ast = Core.clone(ast);
        const inferIds = [0];
        this.precheck(ast, inferIds);
        const inffered = {};
        this.check(ast, context, inffered);
        Core.replaceByMatch(ast.checked, inffered);
        return ast.checked;
    }
    precheck(ast, inferIds) {
        delete ast.err;
        if (ast.nodes) {
            for (const n of ast.nodes) {
                this.precheck(n, inferIds);
            }
        }
        else if (ast.type === "var" && ast.name === "_") {
            ast.name = "?" + (inferIds[0]++);
        }
    }
    mergeContext(added, old, envCtxt) {
        for (const [k, v] of Object.entries(added)) {
            old[k] ??= v;
            if (!this.equal(old[k], v, envCtxt, old, true)) {
                return null;
            }
        }
        return old;
    }
    check(ast, context, infered) {
        if (ast.checked)
            return ast.checked;
        if (ast.type === "var") {
            ast.checked ??= context[ast.name];
            if (ast.checked)
                return ast.checked;
            ast.checked ??= this.checkConst(ast.name);
            if (ast.checked)
                return ast.checked;
            if (ast.name.startsWith("?")) {
                ast.checked = wrapVar(ast.name + ":");
                return ast.checked;
            }
        }
        if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            if (this.checkConst(ast.name))
                this.error(ast.nodes[0], `参数变量${ast.name}不能是常量符号`);
            // #check domain -> U
            const domain = ast.nodes[0];
            const Udomain = UniverseLevel.get(this.check(domain, context, infered));
            if (!Udomain)
                this.error(domain, `函数参数类型不合法`);
            // #check codomain
            const subCtxt = assignContext({ [ast.name]: domain }, context);
            const codomain = this.check(ast.nodes[1], subCtxt, infered);
            if (ast.type === "L") {
                if (Core.getFreeVars(codomain).has(ast.name)) {
                    // reffering
                    ast.checked = wrapLambda("P", ast.name, domain, codomain);
                }
                else {
                    // reffering
                    ast.checked = { type: "->", nodes: [domain, codomain] };
                }
            }
            else if (ast.type === "P" || ast.type === "S") {
                const Ucodomain = UniverseLevel.get(codomain);
                if (!Ucodomain)
                    this.error(ast.nodes[1], `函数返回类型不合法`);
                ast.checked = UniverseLevel.merge(Ucodomain, Udomain);
            }
            return ast.checked;
        }
        if (ast.type === "->") {
            const domain = this.check(ast.nodes[0], context, infered);
            const Udomain = UniverseLevel.get(domain);
            if (!Udomain)
                this.error(ast.nodes[0], `函数参数类型不合法`);
            const codomain = this.check(ast.nodes[1], context, infered);
            const Ucodomain = UniverseLevel.get(codomain);
            if (!Ucodomain)
                this.error(ast.nodes[1], `函数返回类型不合法`);
            ast.checked = UniverseLevel.merge(Ucodomain, Udomain);
            return ast.checked;
        }
        if (ast.type === "apply") {
            if (ast.name === "U") {
                ast.checked = UniverseLevel.succ(ast);
            }
            const tfn = this.check(ast.nodes[0], context, infered);
            const tap = this.check(ast.nodes[1], context, infered);
            if (!this.equal(tfn.nodes[0], tap, context, infered))
                this.error(ast, "函数作用类型不匹配");
            if (tfn.type === "->") {
                // reffering
                ast.checked = tfn.nodes[1];
            }
            else if (tfn.type === "P") {
                const repl = Core.clone(tfn.nodes[1]);
                // reffering
                Core.replaceVar(repl, tfn.name, ast.nodes[1]);
                Core.reduce(repl);
                ast.checked = repl;
            }
            return ast.checked;
        }
    }
    /** lambda reduce, def expands are not inclueded */
    static reduce(ast) {
        if (ast.type === "P") {
            // nondependenet func to ->
            const m1 = this.reduce(ast.nodes[0]);
            const m2 = this.reduce(ast.nodes[1]);
            const codomain = ast.nodes[1];
            if (!this.getFreeVars(codomain).has(ast.name)) {
                ast.name = null;
                ast.type = "->";
                return true;
            }
            return m1 || m2;
        }
        else if (ast.type === "apply") {
            // beta-reduction
            const [fn, ap] = ast.nodes;
            if (fn.type === "L") {
                const nt1 = this.clone(fn.nodes[1]);
                this.replaceVar(nt1, fn.name, ap);
                this.assign(ast, nt1, true);
                this.reduce(ast);
                return true;
            }
            else {
                const m1 = this.reduce(ast.nodes[0]);
                const m2 = this.reduce(ast.nodes[1]);
                return m1 || m2;
            }
        }
        else if (ast.type === "L") {
            const [domain, body] = ast.nodes;
            if (body.type === "apply" && body.nodes[1].name === ast.name && !this.getFreeVars(body.nodes[0]).has(ast.name)) {
                // iota-reduction (func uniqueless)
                this.assign(ast, body.nodes[0], true);
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
        return false;
    }
    equal(a, b, context, infered, moveSemantic) {
        if (a === b || Core.exactEqual(a, b))
            return true;
        if (a.name.startsWith("?")) {
            const name = a.name;
            Core.assign(a, b);
            return this.mergeContext({ [name]: b }, infered, context);
        }
        else if (b.name.startsWith("?")) {
            const name = b.name;
            Core.assign(b, a);
            return this.mergeContext({ [name]: a }, infered, context);
        }
        // fn alpha conversion
        if (a.type === b.type && (a.type === "L" || a.type === "P" || a.type === "S")) {
            if (!this.equal(a.nodes[0], b.nodes[0], context, infered))
                return false;
            if (a.name === b.name)
                return this.equal(a.nodes[1], b.nodes[1], assignContext({ [a.name]: a.nodes[0] }, context), infered);
            const tempB1 = Core.clone(b.nodes[1]);
            Core.replaceVar(tempB1, b.name, wrapVar(a.name));
            return this.equal(a.nodes[1], tempB1, assignContext({ [a.name]: a.nodes[0] }, context), infered);
        }
        // expand defs
        const a1 = moveSemantic ? a : Core.clone(a);
        const b1 = moveSemantic ? b : Core.clone(b);
        let modified = false;
        modified ||= Core.reduce(a1);
        modified ||= Core.reduce(b1);
        modified ||= this.expandDef(a1, context, this.expandStepsBetweenEqCheck);
        modified ||= this.expandDef(b1, context, this.expandStepsBetweenEqCheck);
        if (modified)
            return this.equal(a1, b1, context, infered, true);
        // recurse
        if (a.type === b.type && a.name == b.name && a.nodes?.length === b.nodes?.length) {
            for (let i = 0; i < a.nodes.length; i++) {
                if (!this.equal(a.nodes[i], b.nodes[i], context, infered))
                    return false;
            }
            return true;
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
    expandDef(ast, context, count = 0) {
        return false;
    }
}
class NatLiteral {
    static is(ast) {
        return typeof ast === "string" ? ast.match(/^[1-9][0-9]*$/) : "var" && ast.name.match(/^[1-9][0-9]*$/);
    }
}
class UniverseLevel {
    static reduce(ast) {
    }
    static succ(ast) {
        if (ast.type === "var" && ast.name === "U") {
            return wrapU("1");
        }
        if (ast.type === "apply" && ast.name === "U") {
            if (NatLiteral.is(ast.nodes[1].name)) {
                return wrapU(String(Number(ast.nodes[1].name) + 1));
            }
            else {
                return { type: "apply", name: "U", [wrapVar("succ"), ast]:  };
            }
        }
        return null;
    }
    /** if ast is U/Un return 1/n+1, else return 0 */
    static get(ast) {
        if (ast.type !== "var")
            return 0;
        return this.is(ast.name);
    }
    static is(name) {
        if (!name || name[0] !== "U")
            return 0;
        if (name === "U")
            return 1;
        const m = name.match(/^U([0-9]*)$/);
        if (m && m[1]) {
            return Number(m[1]) + 1;
        }
        return 0;
    }
    static gen(n) {
        if (n === 1)
            return wrapVar("U");
        if (n > 1)
            return wrapVar("U" + (n - 1));
    }
    static merge(lv1, lv2) {
        return this.gen(Math.max(lv1, lv2));
    }
}
class Compute {
}
//# sourceMappingURL=core.js.map