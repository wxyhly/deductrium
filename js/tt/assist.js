import { TR } from "../lang.js";
import { ASTParser } from "./astparser.js";
import { Core, wrapApply, wrapLambda, wrapVar } from "./core.js";
let core = new Core;
let parser = new ASTParser;
export class Assist {
    // the target theorem ast
    theorem;
    // a goal has a context, a type (this is goal) and an ast pointer refered in elem
    goal;
    // inhabited elem : theorem
    elem;
    static disableMultipleApply = true;
    static disableDestructConds = true;
    static disableDestructEq = true;
    constructor(h, target) {
        core = h;
        core.clearState();
        if (typeof target === "string") {
            target = parser.parse(target);
        }
        this.theorem = Core.clone(target);
        // this.theorem = Core.clone(core.markBondVars(target, []),false);
        // this.theorem = core.markBondVars(core.desugar(Core.clone(target),false),[]);
        this.elem = { type: "var", name: "(?#0)", checked: target };
        this.goal = [{ context: [], type: target, ast: this.elem, depend: null }];
    }
    markTargets() {
        let count = 0;
        for (const g of this.goal) {
            g.ast.name = "(?#" + (count++) + ")";
            g.ast.checked = g.type;
        }
    }
    dependVarId = 0;
    autofillTactics() {
        const tactics = [];
        const g = this.goal[0];
        if (!g) {
            return ["qed"];
        }
        const type = g.type;
        const introVar = (n) => !type.name ? Core.getNewName(n, new Set(g.context.map(e => e[0]))) : type.name;
        if (type.type === "X") {
            tactics.push("case");
        }
        else if (type.type === "+") {
            tactics.push("left");
            tactics.push("right");
        }
        else if (type.type === "S") {
            // let found = false;
            for (const [k, v] of g.context) {
                if (Core.exactEqual(v, type.nodes[0])) {
                    tactics.push("ex " + k);
                    // found = true;
                }
            }
            tactics.push("ex");
        }
        else if (type.type === "P") {
            tactics.push("intro " + introVar(type.name));
        }
        else if (type.name === "True") {
            tactics.push("apply true");
            return tactics;
        }
        else if (type.name === "Bool") {
            tactics.push("apply 0b");
            tactics.push("apply 1b");
            // return tactics;
        }
        else if (type.type === "->") {
            tactics.push("intro " + introVar("h"));
        }
        else {
            let matchEq = Core.match(type, parser.parse("$1 = $2"), /^\$/);
            if (!matchEq)
                matchEq = Core.match(type, parser.parse("eq $1 $2"), /^\$/);
            if (!matchEq)
                matchEq = Core.match(type, parser.parse("@eq $3 $4 $1 $2"), /^\$/);
            if (matchEq) {
                try {
                    if (core.checkType({ type: "===", name: "", nodes: [matchEq["$1"], matchEq["$2"]] }, g.context, false)) {
                        tactics.push("rfl");
                    }
                }
                catch (e) { }
                try {
                    if (core.checkType({ type: ":", name: "", nodes: [matchEq["$1"], wrapLambda("->", "", wrapVar("_"), wrapVar("_"))] }, g.context, false)) {
                        tactics.push("fnext");
                    }
                }
                catch (e) { }
            }
        }
        const s = new Set;
        for (const [val, typ] of g.context) {
            const matchEq = Core.match(typ, parser.parse("$2 = $3"), /^\$/) || Core.match(typ, parser.parse("eq $2 $3"), /^\$/) || Core.match(typ, parser.parse("@eq $0 $1 $2 $3"), /^\$/);
            if (matchEq) {
                const fnparam = "*";
                const fnbody2 = this.genReplaceFn(g.type, matchEq["$2"], fnparam, s);
                if (Core.getFreeVars(fnbody2).has(fnparam))
                    tactics.push("rw " + val);
                const fnbody3 = this.genReplaceFn(g.type, matchEq["$3"], fnparam, s);
                if (Core.getFreeVars(fnbody3).has(fnparam))
                    tactics.push("rwb " + val);
            }
            if (this.isIndType(typ)) {
                tactics.push("destruct " + val);
            }
            try {
                const k = Core.clone(typ);
                if (core.checkType({
                    type: "===", name: "", nodes: [
                        k, Core.clone(g.type)
                    ]
                }, g.context, true)) {
                    tactics.push("apply " + val);
                }
            }
            catch (e) { }
            try {
                const k2 = {
                    type: "===", name: "", nodes: [
                        Core.clone(typ), wrapLambda("P", "_", wrapVar("_"), Core.clone(g.type))
                    ]
                };
                if (core.checkType(k2, g.context, false))
                    tactics.push("apply " + val);
            }
            catch (e) { }
        }
        const ntype = Core.clone(type);
        this.whnf(ntype, g.context);
        if (!Core.exactEqual(type, ntype)) {
            tactics.push("simpl");
        }
        const vars = Core.getFreeVars(type);
        const defs1 = Object.keys(core.state.userDefs);
        const defs2 = Object.keys(core.state.sysDefs);
        const defs = new Set([...defs1, ...defs2]);
        const ignore = new Set(["add", "mul", "addO", "mulO", "leqO", "pair", "natO", "eq", "ua", "liftU", "LiftU", "lowerU", "rfl", "refl", "inl", "inr"]);
        for (const v of defs) {
            if (vars.has(v) && !g.context.find(e => e[0] === v)) {
                if (ignore.has(v) || v.startsWith("ind_"))
                    continue;
                tactics.push("expand " + v);
            }
        }
        const findEqv = (ast) => {
            if (ast.type === "~=")
                return true;
            if (ast.nodes?.length)
                return findEqv(ast.nodes[0]) || findEqv(ast.nodes[1]);
        };
        if (findEqv(type))
            tactics.push("expand eqv");
        return tactics;
    }
    resolveDependGoal(d) {
        if (!d)
            return;
        const { src, dst, varname, goals } = d;
        core.replaceVar(dst, varname, -1, src);
        for (const goal of goals) {
            core.replaceVar(goal.type, varname, -1, src);
            for (const [k, v, id] of goal.context) {
                core.replaceVar(v, varname, -1, src);
            }
        }
    }
    isIndType(typ) {
        return (typ.name === "nat" || typ.name === "Bool" || typ.name === "I" || typ.name === "S1" || typ.name === "Ord" || typ.name === "True" || typ.name === "False" || (typ.type === "apply" && typ.nodes?.[0]?.name === "Sus")
            || typ.type === "+" || typ.type === "X" || typ.type === "S" || (!Assist.disableDestructEq && ((typ.type === "=") || typ.nodes?.[0]?.nodes?.[0]?.name === "eq")));
    }
    intro(s) {
        s = s.trim();
        if (s.includes(" ")) {
            return this.intros(s);
        }
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        const tartgetType = goal.type;
        if (tartgetType.type !== "P" && tartgetType.type !== "->") {
            this.goal.unshift(goal);
            throw TR("intro 只能作用于函数类型");
        }
        s = Core.getNewName(s || tartgetType.name || "h", new Set(goal.context.map(e => e[0])));
        goal.context.unshift([s, tartgetType.nodes[0], 0]);
        // goal.ast is refferd at outter level hole,  we fill the hole first
        Core.assign(goal.ast, { "type": "L", name: s, nodes: [tartgetType.nodes[0], { type: "var", name: "(?#0)" }] }, true);
        goal.ast.checked = tartgetType;
        core.checkType(goal.ast.nodes[0], goal.context, false);
        // console.log(s + " : " + core.print(tartgetType.nodes[0]));
        const newtype = Core.clone(tartgetType.nodes[1]);
        this.replaceFreeVar(newtype, goal.type.name, { type: "var", name: s });
        // Core.assign(goal.type, newtype); // pq copy here? may contain dangerou refers
        goal.type = newtype;
        // then set goal.ast to refer the new smaller hole
        goal.ast = goal.ast.nodes[1];
        goal.ast.checked = goal.type;
        this.goal.unshift(goal);
        return this;
    }
    intros(s) {
        if (!s?.trim())
            throw TR("意外的空表达式");
        s.split(" ").map(ss => ss ? this.intro(ss) : "");
        return this;
    }
    apply(ast) {
        if (typeof ast === "string") {
            ast = parser.parse(ast);
        }
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        let context = goal.context;
        try {
            const k = Core.clone(ast);
            core.checkType({
                type: ":", name: "", nodes: [
                    k, Core.clone(goal.type)
                ]
            }, context, true);
            Core.assign(goal.ast, k, true);
            this.resolveDependGoal(goal.depend);
            return this;
        }
        catch (e) { }
        let applyType = null;
        try {
            const k = {
                type: ":", name: "", nodes: [
                    Core.clone(ast), wrapLambda("P", "_", wrapVar("_"), Core.clone(goal.type))
                ]
            };
            core.checkType(k, context, false);
            applyType = k.nodes[1].nodes[0];
            if (applyType.checked?.type === ":") {
                applyType = applyType.checked.nodes[0];
            }
        }
        catch (e) {
            this.goal.unshift(goal);
            try {
                if (Assist.disableMultipleApply)
                    throw e;
                this.apply2(ast);
                return;
            }
            catch (e) {
                core.checkType(ast, context, false);
                throw TR("无法对类型") + parser.stringify(ast.checked) + TR("使用apply策略作用于类型") + parser.stringify(goal.type);
            }
        }
        core.checkType(ast, context, false);
        // goal.ast is refferd at outter level hole,  we fill the hole first
        Core.assign(goal.ast, {
            type: "apply", name: "", nodes: [ast, {
                    type: "var", name: "(?#0)", checked: applyType
                }], checked: goal.type
        }, true);
        // then set goal.ast to refer the new smaller hole
        goal.ast = goal.ast.nodes[1];
        goal.type = applyType;
        this.goal.unshift(goal);
        return this;
    }
    apply2(ast) {
        const goal = this.goal.shift();
        let fn;
        try {
            fn = core.checkType(ast, goal.context, false);
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        const fnParams = this.flattenParams(fn, true);
        const fnParamNames = this.flattenParamNames(fn);
        let tail = fn;
        let holeNumbers = 1;
        while (true) {
            if (tail.type === "->" || tail.type === "P") {
                tail = tail.nodes[1];
            }
            else {
                this.goal.unshift(goal);
                throw TR("无法对类型") + parser.stringify(ast.checked) + TR("使用apply策略作用于类型") + parser.stringify(goal.type);
            }
            try {
                core.checkType(wrapLambda("===", "", Core.clone(tail), Core.clone(goal.type)), goal.context, true);
                break;
            }
            catch (e) { }
            holeNumbers++;
        }
        const fnBody = [];
        const newGoals = [];
        const dependence = [];
        for (let i = 0; i < holeNumbers; i++) {
            const fnParamType = fnParams[i];
            const fnParamName = fnParamNames[i];
            const gast = wrapVar("(?#0)");
            const ctx = Core.cloneContext(goal.context);
            gast.checked = fnParamType;
            // mark depend
            const depend = [];
            if (fnParamName) {
                for (let j = i; j < holeNumbers; j++) {
                    if (j === i)
                        continue;
                    if (Core.getFreeVars(fnParams[j]).has(fnParamName)) {
                        depend.push(j);
                    }
                }
            }
            dependence.push(depend);
            newGoals.push({ context: ctx, ast: gast, type: fnParamType, depend: null });
            fnBody.push(gast);
        }
        // record dependences in goals
        for (let i = 0; i < holeNumbers; i++) {
            const d = dependence[i];
            if (!d.length)
                continue;
            const goals = d.map(j => newGoals[j]);
            const varname = this.getNewDependGoalVarName();
            newGoals[i].depend = {
                src: newGoals[i].ast, dst: goal.ast, goals, varname
            };
            const srcname = fnParamNames[i];
            for (const g of goals) {
                this.replaceFreeVar(g.type, srcname, wrapVar(varname));
            }
        }
        Core.assign(goal.ast, wrapApply(ast, ...fnBody), true);
        if (!newGoals.length) {
            this.resolveDependGoal(goal.depend);
            return;
        }
        newGoals[newGoals.length - 1].depend = goal.depend;
        this.goal.unshift(...newGoals);
    }
    rw(eq, back = false) {
        if (typeof eq === "string")
            eq = parser.parse(eq);
        if (!eq)
            throw TR("请输入用于改写的相等假设");
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        let matched;
        try {
            const t = core.checkType(eq, goal.context, false);
            matched = Core.match(t, parser.parse("$2 = $3"), /^\$/) || Core.match(t, parser.parse("eq $2 $3"), /^\$/) || Core.match(t, parser.parse("@eq $0 $1 $2 $3"), /^\$/);
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        let isRfl = false;
        try {
            core.checkType(wrapLambda("===", "", eq, wrapVar("rfl")), goal.context, false);
            isRfl = true;
        }
        catch (e) {
        }
        if (!matched) {
            this.goal.unshift(goal);
            throw TR("使用rewrite策略必须提供一个相等类型");
        }
        matched["$eq"] = eq;
        const ctxtSet = new Set(goal.context.map(e => e[0]));
        const fnbody = this.genReplaceFn(goal.type, matched[back ? "$3" : "$2"], "(?#)", ctxtSet);
        const fnparam = Core.getNewName("x", ctxtSet);
        this.replaceFreeVar(fnbody, "(?#)", wrapVar(fnparam));
        // eq: eleq: eq t a b
        // type: F(a/b) 
        // F(a/b)->F(a/b), eleq  |- F(b/a)->F(a/b) 
        // newgoal: F(b/a)
        const fn = { type: "L", name: fnparam, nodes: [core.checkType(matched[back ? "$3" : "$2"], goal.context, false), fnbody] };
        matched["$fn"] = fn;
        if (!isRfl) {
            matched["$type"] = matched[back ? "$3" : "$2"].checked;
            const y = Core.getNewName("y", ctxtSet);
            const m = Core.getNewName("m", ctxtSet);
            matched["$fn_2"] = Core.clone(fnbody);
            this.replaceFreeVar(matched["$fn_2"], fnparam, matched["$2"]);
            matched["$fn_y"] = Core.clone(fnbody);
            this.replaceFreeVar(matched["$fn_y"], fnparam, wrapVar(y));
            let newAst = parser.parse(core.checkConst("trans", []) && (back || core.checkConst("inveq", [])) ?
                `trans $fn ` + (back ? `$eq` : `(inveq $eq)`) : `ind_eq $2 (L${y}:$type.L${m}:$2=${y}. P${m}:` + (back ? `$fn_2, $fn_y` : `$fn_y, $fn_2`) + `) (Lx:_.x) $3 $eq`);
            Core.replaceByMatch(newAst, matched, /^\$/);
            // try {
            core.checkType(newAst, goal.context, false);
            // } catch (e) {
            //     console.log("[rw] " + e);
            // }
            newAst = { type: "apply", name: "", nodes: [newAst, { type: "var", name: "(?#0)" }] };
            Core.assign(goal.ast, newAst, true);
            goal.ast.checked = goal.type;
            goal.ast = goal.ast.nodes[1];
        }
        goal.type = Core.clone(fn.nodes[1]);
        this.replaceFreeVar(goal.type, fnparam, matched[back ? "$2" : "$3"]);
        goal.ast.checked = goal.type;
        this.goal.unshift(goal);
        return this;
    }
    rwb(eq) {
        this.rw(eq, true);
        return this;
    }
    // replace "search" in ast by "varname"
    genReplaceFn(ast, search, varname, excludedNames) {
        if (this.exactEqualByAlphaConversion(ast, search)) {
            return { type: "var", name: varname };
        }
        if (ast.type === "var") {
            excludedNames.add(ast.name);
            return ast;
        }
        if (ast.nodes?.length === 2) {
            const nast = Core.clone(ast);
            nast.nodes[1] = this.genReplaceFn(nast.nodes[1], search, varname, excludedNames);
            nast.nodes[0] = this.genReplaceFn(nast.nodes[0], search, varname, excludedNames);
            return nast;
        }
    }
    boundId = 0;
    exactEqualByAlphaConversion(ast1, ast2) {
        if (ast1 === ast2)
            return true;
        if (ast1.type !== ast2.type)
            return false;
        if (ast1.type === "var")
            return ast1.name === ast2.name;
        if (ast1.nodes?.length !== ast2.nodes?.length)
            return false;
        if (ast1.type === "L" || ast1.type === "P" || ast1.type === "S") {
            const n1 = ast1.name;
            const n2 = ast2.name;
            if (n1 !== n2) {
                ast1 = Core.clone(ast1);
                ast2 = Core.clone(ast2);
                ast1.name = ast2.name = (this.boundId++).toString();
                this.replaceFreeVar(ast1.nodes[1], n1, wrapVar(ast1.name));
                this.replaceFreeVar(ast2.nodes[1], n2, wrapVar(ast1.name));
            }
        }
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.exactEqualByAlphaConversion(ast1.nodes[i], ast2.nodes[i]))
                    return false;
            }
        }
        return true;
    }
    search(ast, search) {
        if (this.exactEqualByAlphaConversion(ast, search)) {
            return true;
        }
        if (ast.nodes?.length === 2) {
            const nast = Core.clone(ast);
            return this.search(nast.nodes[1], search) || this.search(nast.nodes[0], search);
        }
        return false;
    }
    rfl() {
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        let matched = Core.match(goal.type, parser.parse("$1 = $2"), /^\$/);
        if (!matched)
            matched = Core.match(goal.type, parser.parse("eq $1 $2"), /^\$/);
        if (!matched)
            matched = Core.match(goal.type, parser.parse("@eq $3 $4 $1 $2"), /^\$/);
        if (!matched) {
            this.goal.unshift(goal);
            throw TR("无法对非相等类型使用该策略");
        }
        try {
            if (!core.checkType({ type: "===", name: "", nodes: [matched["$1"], matched["$2"]] }, goal.context, false)) {
                throw TR("使用rfl策略失败：等式两边无法化简至相等");
            }
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        const newAst = wrapVar("rfl");
        Core.assign(goal.ast, newAst, true);
        goal.ast.checked = goal.type;
        this.resolveDependGoal(goal.depend);
        return this;
    }
    qed() {
        if (this.goal.length)
            throw TR("证明尚未完成");
        // core.checkType({ type: ":", name: "", nodes: [Core.clone(this.elem), Core.clone(this.theorem)] }, [], false);
    }
    simpl(str) {
        if (str) {
            str = str.trim();
        }
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        const type = goal.context.find(e => e[0] === str)?.[1];
        if (!type && str) {
            this.goal.unshift(goal);
            throw TR("未知的变量：") + str;
        }
        this.whnf(type ?? goal.type, type ? goal.context.slice(0, goal.context.findIndex(e => e[0] === str)) : goal.context);
        this.goal.unshift(goal);
        return this;
    }
    fnext() {
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        let matched;
        try {
            const t = goal.type;
            matched = Core.match(t, parser.parse("$2 = $3"), /^\$/) || Core.match(t, parser.parse("eq $2 $3"), /^\$/) || Core.match(t, parser.parse("@eq $0 $1 $2 $3"), /^\$/);
            if (!matched)
                throw TR("无法对非相等类型使用该策略");
            if (!core.checkType({ type: ":", name: "", nodes: [matched["$2"], wrapLambda("->", "", wrapVar("_"), wrapVar("_"))] }, goal.context, false)) {
                throw TR("无法对非函数相等类型使用fnext策略");
            }
            this.goal.unshift(goal);
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        this.apply(wrapApply(wrapVar("fnext")));
    }
    hyp(astr) {
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        try {
            let ast = parser.parse(astr);
            const ctxtNames = new Set(goal.context.map(e => e[0]));
            let name = Core.getNewName("hyp", ctxtNames);
            if (ast.type === ":" && ast.nodes[0].type === "var") {
                if (ctxtNames.has(ast.nodes[0].name))
                    throw TR("无法引入重复名称的假设变量");
                name = ast.nodes[0].name;
                ast = ast.nodes[1];
            }
            const newast = wrapApply({ type: "L", name, nodes: [ast, wrapVar("(?#0)")] }, wrapVar("(?#0)"));
            Core.assign(goal.ast, newast, true);
            goal.ast.checked = goal.type;
            goal.ast.nodes[0].checked = { type: "->", name: "", nodes: [ast, goal.type] };
            core.checkType(ast, goal.context, false);
            const anotherGoal = {
                ast: goal.ast.nodes[1],
                context: goal.context,
                type: Core.clone(ast),
                depend: goal.depend
            };
            anotherGoal.ast.checked = anotherGoal.type;
            goal.ast = goal.ast.nodes[0].nodes[1];
            goal.ast.checked = goal.type;
            goal.context = goal.context.slice(0);
            goal.context.unshift([name, ast, 0]);
            this.goal.unshift(goal);
            goal.depend = null;
            this.goal.unshift(anotherGoal);
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
    }
    flattenParams(typ, withEnd) {
        let params = [];
        while (typ.type === "P" || typ.type === "->") {
            params.push(typ.nodes[0]);
            typ = typ.nodes[1];
        }
        if (withEnd)
            params.push(typ);
        return params;
    }
    flattenParamNames(typ) {
        let names = [];
        while (typ.type === "P" || typ.type === "->") {
            names.push(typ.name);
            typ = typ.nodes[1];
        }
        return names;
    }
    destruct(n) {
        n = n.trim();
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        const nast = { type: "var", name: n };
        let nType;
        try {
            nType = core.checkType(nast, goal.context, false);
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        if (!this.isIndType(nType)) {
            this.goal.unshift(goal);
            throw TR("只能解构解锁的归纳类型的变量");
        }
        const excludedSet = new Set(goal.context.map(e => e[0]));
        Core.getFreeVars(goal.type, excludedSet);
        const indFnName = "ind_" + (nType.nodes?.[0]?.name === "Sus" ? "Sus" : (nType.nodes?.[0]?.nodes?.[0]?.name === "eq" || nType.type === "=") ? "eq" : nType.type === "+" ? "Sum" : nType.type === "X" ? "Prod" : nType.type === "S" ? "Prod" : nType.name);
        // x in x=y, just parameter for types 
        // nType.nodes?.[0]?.name === "Sus" ? [nType.nodes[1]] :
        const typeParams = nType.nodes?.[0]?.nodes?.[0]?.name === "eq" ? [nType.nodes[0].nodes[1]] : nType.type === "=" ? [nType.nodes[0]] : nType.type === "X" ? [wrapLambda("L", Core.getNewName("x", excludedSet), nType.nodes[0], nType.nodes[1])] : nType.type === "S" ? [wrapLambda("L", nType.name, nType.nodes[0], nType.nodes[1])] : [];
        // y in x=y: induction on this group of types
        const groupParam = nType.nodes?.[0]?.nodes?.[0]?.name === "eq" || nType.type === "=" ? nType.nodes[1] : null;
        // destruct with other variables in context as condition added in target C
        const conds = [];
        if (!Assist.disableDestructConds) {
            for (const [k, v, id] of goal.context) {
                if (k === n)
                    continue;
                if (Core.getFreeVars(v).has(n) || (groupParam && this.search(v, groupParam))) {
                    conds.push([k, v, id]);
                }
            }
        }
        const condsNames = conds.map(e => e[0]);
        let goalWithConds = Core.clone(goal.type);
        for (const [k, v, id] of conds) {
            goalWithConds = wrapLambda("P", k, v, goalWithConds);
        }
        let C = wrapLambda("L", n, nType, goalWithConds);
        if (groupParam) {
            const eqType = core.checkType(groupParam, goal.context, false);
            const newY = Core.getNewName(groupParam.type === "var" ? groupParam.name : "y", excludedSet);
            C = wrapLambda("L", newY, eqType, Core.clone(C, true));
            C.nodes[1] = this.genReplaceFn(C.nodes[1], groupParam, newY, excludedSet);
        }
        const indFn = wrapVar(indFnName);
        const indFnHead = wrapApply(indFn, ...typeParams.map(e => Core.clone(e)), Core.clone(C));
        let headType;
        try {
            headType = core.checkType(indFnHead, goal.context, false);
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        const indFnType = indFn.checked;
        const indFnParams = this.flattenParams(indFnType);
        const indFnParamNames = this.flattenParamNames(indFnType);
        // holes includes ctor holes and also grpara / tail: x->C x
        const holes = this.flattenParams(headType);
        // grpara is group param
        // ind_xxx :param->C->(C grpara? ctor1)->(C grpara? ctor2)->...->grpara->x:xxx->(C grpara xxx)
        let ctorNumbers = indFnParams.length - typeParams.length - 1 - (groupParam ? 1 : 0) - 1;
        const indFnBody = [];
        const newGoals = [];
        const introNums = [];
        const ctorOffset = typeParams.length + 1;
        const dependence = [];
        for (let i = 0; i < ctorNumbers; i++) {
            const gtype = holes[i];
            const gast = wrapVar("(?#0)");
            const ctx = Core.cloneContext(goal.context).filter(e => e[0] !== n && !condsNames.includes(e[0]));
            gast.checked = gtype;
            const indFnParamType = indFnParams[i + ctorOffset];
            const indFnParamName = indFnParamNames[i + ctorOffset];
            const holeParams = this.flattenParamNames(indFnParamType);
            holeParams.push(...condsNames);
            introNums.push(holeParams);
            // mark depend
            const depend = [];
            if (indFnParamName) {
                for (let j = i; j < ctorNumbers; j++) {
                    if (j === i)
                        continue;
                    if (Core.getFreeVars(indFnParams[j + ctorOffset]).has(indFnParamName)) {
                        depend.push(j);
                    }
                }
            }
            dependence.push(depend);
            newGoals.push({ context: ctx, ast: gast, type: gtype, depend: null });
            indFnBody.push(gast);
        }
        // record dependences in goals
        for (let i = 0; i < ctorNumbers; i++) {
            const d = dependence[i];
            if (!d.length)
                continue;
            const goals = d.map(j => newGoals[j]);
            const varname = this.getNewDependGoalVarName();
            newGoals[i].depend = {
                src: newGoals[i].ast, dst: goal.ast, goals, varname
            };
            const srcname = indFnParamNames[i + ctorOffset];
            for (const g of goals) {
                this.replaceFreeVar(g.type, srcname, wrapVar(varname));
            }
        }
        if (groupParam)
            indFnBody.push(groupParam);
        Core.assign(goal.ast, wrapApply(indFnHead, ...indFnBody, nast, ...conds.map(e => {
            const k = wrapVar(e[0]);
            k.checked = e[1];
            return k;
        })), true);
        let k = 0;
        for (const g of newGoals) {
            this.goal.unshift(g);
            const intros = introNums[k++];
            intros.forEach(e => this.intro((n + "_" + e).replaceAll("_x", "")));
            this.goal.shift();
        }
        if (!newGoals.length) {
            this.resolveDependGoal(goal.depend);
            return;
        }
        newGoals[newGoals.length - 1].depend = goal.depend;
        this.goal.unshift(...newGoals);
        return this;
    }
    getNewDependGoalVarName() {
        return "(%" + (this.dependVarId++) + ")";
    }
    ex(n) {
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type !== "S")
            throw TR("ex策略只能作用于依赖积类型");
        const dfn = Core.clone(goal.type);
        dfn.type = "L";
        n = n?.trim();
        if (n?.startsWith("?") || n === "_")
            n = null;
        try {
            let val = n ? parser.parse(n) : wrapVar("(?#0)");
            Core.assign(goal.ast, wrapApply(wrapVar("pair"), dfn, val, wrapVar("(?#0)")), true);
            goal.ast.checked = goal.type;
            if (n) {
                core.checkType(goal.ast.nodes[0], goal.context, false);
            }
            else {
                const newGoal = {
                    ast: goal.ast.nodes[0].nodes[1],
                    type: dfn.nodes[0],
                    context: Core.cloneContext(goal.context),
                    depend: {
                        src: goal.ast.nodes[0].nodes[1],
                        dst: goal.ast.nodes[1],
                        goals: [goal],
                        varname: this.getNewDependGoalVarName()
                    }
                };
                val = wrapVar(newGoal.depend.varname);
                this.goal.unshift(newGoal, goal);
            }
            goal.ast = goal.ast.nodes[1];
            goal.type = Core.clone(dfn.nodes[1]);
            this.replaceFreeVar(goal.type, dfn.name, val);
            if (n) {
                core.checkType(goal.type, goal.context, false);
                this.goal.unshift(goal);
            }
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
    }
    left() {
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type !== "+")
            throw TR("left策略只能作用于和类型");
        Core.assign(goal.ast, wrapApply(wrapVar("inl"), wrapVar("(?#0)")), true);
        goal.ast.checked = goal.type;
        goal.ast.nodes[0].checked = wrapLambda("->", "", goal.type.nodes[0], goal.type);
        goal.ast = goal.ast.nodes[1];
        goal.type = goal.type.nodes[0];
        goal.ast.checked = goal.type;
        this.goal.unshift(goal);
    }
    right() {
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type !== "+")
            throw TR("left策略只能作用于和类型");
        Core.assign(goal.ast, wrapApply(wrapVar("inr"), wrapVar("(?#0)")), true);
        goal.ast.checked = goal.type;
        goal.ast.nodes[0].checked = wrapLambda("->", "", goal.type.nodes[1], goal.type);
        goal.ast = goal.ast.nodes[1];
        goal.type = goal.type.nodes[1];
        goal.ast.checked = goal.type;
        this.goal.unshift(goal);
    }
    case() {
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type !== "X")
            throw TR("case策略只能作用于积类型");
        Core.assign(goal.ast, { type: ",", name: "", nodes: [wrapVar("(?#0)"), wrapVar("(?#0)")] }, true);
        const anotherGoal = {
            ast: goal.ast.nodes[1],
            context: goal.context.slice(0),
            type: goal.type.nodes[1],
            depend: goal.depend
        };
        anotherGoal.ast.checked = anotherGoal.type;
        goal.ast.checked = goal.type;
        goal.ast = goal.ast.nodes[0];
        goal.type = goal.type.nodes[0];
        goal.ast.checked = goal.type;
        goal.depend = null;
        this.goal.unshift(anotherGoal);
        this.goal.unshift(goal);
    }
    expand(n) {
        n = n?.trim();
        if (!n)
            throw TR("意外的空表达式");
        const k = n.split(" ");
        if (k.length === 1)
            k.unshift("0");
        const pos = Number(k.shift());
        n = k.join(" ");
        if (Math.round(pos) !== pos)
            throw TR("未找到任何指定展开的项");
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        try {
            if (!core.expandDef(goal.type, goal.context, n, [pos, 1])) {
                this.goal.unshift(goal);
                throw TR("未找到任何指定展开的项");
            }
            ;
            if (core.opaque.find(e => e[0] === n) && core.state.sysDefs["@" + n]) {
                core.expandDef(goal.type, goal.context, "@" + n, [0, 1]);
            }
            this.whnf(goal.type, goal.context);
            core.checkType(goal.type, goal.context, false);
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        this.goal.unshift(goal);
        return this;
    }
    replaceFreeVar(ast, src, dst, freevarInDst = Core.getFreeVars(dst)) {
        if (ast.type === "var") {
            if (ast.name === src) {
                Core.assign(ast, dst);
            }
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            if (freevarInDst.has(ast.name)) {
                // alpha conversion
                const exset = Core.getFreeVars(ast.nodes[1]);
                const nn = Core.getNewName(Core.getNewName(ast.name, freevarInDst), exset);
                this.replaceFreeVar(ast.nodes[1], ast.name, wrapVar(nn));
                ast.name = nn;
            }
            this.replaceFreeVar(ast.nodes[0], src, dst, freevarInDst);
            if (ast.name !== src) {
                this.replaceFreeVar(ast.nodes[1], src, dst, freevarInDst);
            }
        }
        else if (ast.nodes?.length === 2) {
            this.replaceFreeVar(ast.nodes[0], src, dst, freevarInDst);
            this.replaceFreeVar(ast.nodes[1], src, dst, freevarInDst);
        }
    }
    whnf(ast, context) {
        core.checkType({ type: "whnf", nodes: [ast, wrapVar("_")], name: "" }, context, true);
        return ast;
    }
}
//# sourceMappingURL=assist.js.map