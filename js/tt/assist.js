import { TR } from "../lang.js";
import { ASTParser } from "./astparser.js";
import { assignContext, Core, wrapApply, wrapLambda, wrapVar } from "./core.js";
let core = new Core;
let parser = new ASTParser;
export class Assist {
    // the target theorem ast
    theorem;
    // a goal has a context, a type (this is goal) and an ast pointer refered in elem
    goal;
    // inhabited elem : theorem
    elem;
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
        this.goal = [{ context: [], type: target, ast: this.elem }];
    }
    markTargets() {
        let count = 0;
        for (const g of this.goal) {
            g.ast.name = "(?#" + (count++) + ")";
            g.ast.checked = g.type;
        }
    }
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
            tactics.push("ex ??");
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
            return tactics;
        }
        else if (type.type === "->") {
            tactics.push("intro " + introVar("h"));
        }
        else {
            let matchEq = Core.match(type, parser.parse("eq $1 $2"), /^\$/);
            if (!matchEq)
                matchEq = Core.match(type, parser.parse("@eq $3 $4 $1 $2"), /^\$/);
            if (matchEq) {
                try {
                    if (core.checkType({ type: "===", name: "", nodes: [matchEq["$1"], matchEq["$2"]] }, g.context, false)) {
                        tactics.push("rfl");
                    }
                }
                catch (e) { }
            }
        }
        const s = new Set;
        for (const [val, typ] of g.context) {
            const matchEq = Core.match(typ, parser.parse("eq $2 $3"), /^\$/) || Core.match(typ, parser.parse("@eq $0 $1 $2 $3"), /^\$/);
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
        const ignore = new Set(["add", "mul", "addO", "mulO", "leqO", "pair", "natO", "eq"]);
        for (const v of defs) {
            if (vars.has(v) && !g.context.find(e => e[0] === v)) {
                if (ignore.has(v) || v.startsWith("ind_"))
                    continue;
                tactics.push("expand " + v);
            }
        }
        return tactics;
    }
    isIndType(typ) {
        return (typ.name === "nat" || typ.name === "Bool" || typ.name === "True" || typ.name === "False"
            || typ.type === "+" || typ.type === "X" || typ.type === "S") || typ.nodes?.[0]?.nodes?.[0]?.name === "eq";
    }
    intro(s) {
        if (!s)
            throw TR("意外的空表达式");
        s = s.trim();
        if (s.includes(" ")) {
            return this.intros(s);
        }
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.context.find(e => e[0] === s)) {
            this.goal.unshift(goal);
            throw TR("无法重复intro相同变量名");
        }
        const tartgetType = goal.type;
        if (tartgetType.type !== "P" && tartgetType.type !== "->") {
            this.goal.unshift(goal);
            throw TR("intro 只能作用于函数类型");
        }
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
            core.checkType(ast, context, false);
            throw TR("无法对类型") + parser.stringify(ast.checked) + TR("使用apply策略作用于类型") + parser.stringify(goal.type);
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
            matched = Core.match(t, parser.parse("eq $2 $3"), /^\$/) || Core.match(t, parser.parse("@eq $0 $1 $2 $3"), /^\$/);
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        if (!matched) {
            this.goal.unshift(goal);
            throw TR("使用rewrite策略必须提供一个相等类型");
        }
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
        matched["$eq"] = eq;
        matched["$type"] = matched[back ? "$3" : "$2"].checked;
        const y = Core.getNewName("y", ctxtSet);
        const m = Core.getNewName("m", ctxtSet);
        matched["$fn_2"] = Core.clone(fnbody);
        this.replaceFreeVar(matched["$fn_2"], fnparam, matched["$2"]);
        matched["$fn_y"] = Core.clone(fnbody);
        this.replaceFreeVar(matched["$fn_y"], fnparam, wrapVar(y));
        // let newAst = parser.parse(false ?
        let newAst = parser.parse(core.checkConst("trans", []) && (back || core.checkConst("inveq", [])) ?
            `trans $fn ` + (back ? `$eq` : `(inveq $eq)`) : `ind_eq $2 (L${y}:$type.L${m}:eq $2 ${y}. P${m}:` + (back ? `$fn_2, $fn_y` : `$fn_y, $fn_2`) + `) (Lx:_.x) $3 $eq`);
        Core.replaceByMatch(newAst, matched, /^\$/);
        core.checkType(newAst, goal.context, false);
        newAst = { type: "apply", name: "", nodes: [newAst, { type: "var", name: "(?#0)" }] };
        Core.assign(goal.ast, newAst, true);
        goal.ast.checked = goal.type;
        goal.ast = goal.ast.nodes[1];
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
    genReplaceFn(ast, search, varname, excludedNames) {
        if (Core.exactEqual(ast, search)) {
            return { type: "var", name: varname };
        }
        if (ast.type === "var") {
            excludedNames.add(ast.name);
            return ast;
        }
        if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            if (ast.type === search.type) {
                if (ast.name !== search.name) {
                    // todo
                }
                // todo
            }
            const nast = Core.clone(ast);
            nast.nodes[0] = this.genReplaceFn(nast.nodes[0], search, varname, excludedNames);
            nast.nodes[1] = this.genReplaceFn(nast.nodes[1], search, varname, excludedNames);
            return nast;
        }
        if (ast.nodes?.length === 2) {
            const nast = Core.clone(ast);
            nast.nodes[1] = this.genReplaceFn(nast.nodes[1], search, varname, excludedNames);
            nast.nodes[0] = this.genReplaceFn(nast.nodes[0], search, varname, excludedNames);
            return nast;
        }
    }
    rfl() {
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        let matched = Core.match(goal.type, parser.parse("eq $1 $2"), /^\$/);
        if (!matched)
            matched = Core.match(goal.type, parser.parse("@eq $3 $4 $1 $2"), /^\$/);
        if (!matched) {
            this.goal.unshift(goal);
            throw TR("无法对非相等类型使用rfl策略");
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
        return this;
    }
    qed() {
        if (this.goal.length)
            throw TR("证明尚未完成");
        // core.checkType({ type: ":", name: "", nodes: [Core.clone(this.elem), Core.clone(this.theorem)] }, [], false);
    }
    simpl() {
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        this.whnf(goal.type, goal.context);
        this.goal.unshift(goal);
        return this;
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
                type: ast
            };
            anotherGoal.ast.checked = ast;
            goal.ast = goal.ast.nodes[0].nodes[1];
            goal.ast.checked = goal.type;
            goal.context = goal.context.slice(0);
            goal.context.unshift([name, ast, 0]);
            this.goal.unshift(goal);
            this.goal.unshift(anotherGoal);
        }
        catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
    }
    destruct(n) {
        n = n.trim();
        const param = n.split(" ");
        n = param[0];
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        const nast = { type: "var", name: param[0] };
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
            throw TR("只能解构归纳类型的变量");
        }
        // for (const [k, v, id] of goal.context) {
        //     if (Core.getFreeVars(v).has(n)) {
        //         if (Core.getFreeVars(goal.type).has(k)) {
        //             this.goal.unshift(goal); throw TR("解构失败：其它变量依赖该变量");
        //         }
        //         // delete goal.context[k];
        //     }
        // }
        const excludedSet = new Set(goal.context.map(e => e[0]));
        const matched = { "$1": Core.clone(goal.type), "$nast": nast, "$typeN": nType };
        if (nType.name === "Bool") {
            let newAst = parser.parse(`ind_Bool (L${n}:$typeN.$1) (?#0) (?#0) $nast`);
            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            goal.ast.nodes[1].checked = nType;
            const t = core.checkType(goal.ast.nodes[0].nodes[0].nodes[0], goal.context, false);
            goal.ast.nodes[0].nodes[0].checked = t.nodes[1];
            goal.ast.nodes[0].checked = t.nodes[1].nodes[1];
            const type0b = Core.clone(goal.type);
            const type1b = Core.clone(goal.type);
            this.replaceFreeVar(type0b, n, { type: "var", name: "0b" });
            this.replaceFreeVar(type1b, n, { type: "var", name: "1b" });
            core.checkType(type0b, goal.context, false);
            core.checkType(type1b, goal.context, false);
            goal.type = type0b;
            const anotherGoal = {
                ast: goal.ast.nodes[0].nodes[1],
                context: goal.context.slice(0),
                type: type1b
            };
            goal.ast = goal.ast.nodes[0].nodes[0].nodes[1];
            goal.ast.checked = goal.type;
            anotherGoal.ast.checked = anotherGoal.type;
            this.goal.unshift(goal);
            this.goal.unshift(anotherGoal);
        }
        else if (nType.name === "True") {
            let newAst = parser.parse(`ind_True (L${n}:$typeN.$1) (?#0) $nast`);
            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            goal.ast.nodes[1].checked = nType;
            const t = core.checkType(goal.ast.nodes[0].nodes[0], goal.context, false);
            goal.ast.nodes[0].checked = t.nodes[1];
            this.replaceFreeVar(goal.type, n, { type: "var", name: "true" });
            core.checkType(goal.type, goal.context, false);
            goal.ast = goal.ast.nodes[0].nodes[1];
            this.goal.unshift(goal);
        }
        else if (nType.nodes?.[0]?.nodes?.[0]?.name === "eq") {
            const x = nType.nodes?.[0]?.nodes?.[1];
            const y = nType.nodes?.[1];
            matched["$x"] = Core.clone(x);
            matched["$y"] = Core.clone(y);
            matched["$typex"] = core.checkType(x, goal.context, false);
            const excludedSet = new Set(goal.context.map(e => e[0]));
            const ny = Core.getNewName(y.type === "var" ? y.name : "y", excludedSet);
            // m: eq f(x) f(y)
            // ind_eq f(x) Ly':T.Lm:eq f(x) y'.goal[f(y)/y']??.
            let newAst = parser.parse(`ind_eq $x (L${ny}:$typex.L${n}:eq $x ${ny}.$1) (?#0) $y $nast`);
            matched["$1"] = this.genReplaceFn(matched["$1"], y, ny, excludedSet);
            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            this.replaceFreeVar(goal.type, n, wrapApply(wrapVar("rfl")));
            const replaced = this.genReplaceFn(goal.type, y, ny, excludedSet);
            Core.replaceByMatch(replaced, { [ny]: x }, /./);
            Core.assign(goal.type, replaced);
            goal.ast = goal.ast.nodes[0].nodes[0].nodes[1];
            this.goal.unshift(goal);
            // delete goal.context[n];
        }
        else if (nType.name === "False") {
            let newAst = parser.parse(`ind_False (L${n}:$typeN.$1) $nast`);
            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            core.checkType(goal.ast, goal.context, false);
        }
        else if (nType.name === "nat") {
            const fromParam1 = param[1];
            if (fromParam1 && excludedSet.has(fromParam1)) {
                this.goal.unshift(goal);
                throw TR("destruct引入了重复的变量名");
            }
            const destructed = fromParam1 || Core.getNewName(n, excludedSet);
            excludedSet.add(fromParam1);
            const fromParam2 = param[2];
            if (fromParam2 && excludedSet.has(fromParam2)) {
                this.goal.unshift(goal);
                throw TR("destruct引入了重复的变量名");
            }
            const induced = fromParam2 || Core.getNewName("H" + n, excludedSet);
            let newAst = parser.parse(`ind_nat (L${n}:$typeN.$1) (?#0) (L${destructed}:nat.L${induced}:$indType.(?#0)) $nast`);
            const type0 = Core.clone(goal.type);
            const typen = Core.clone(goal.type);
            const typeSn = Core.clone(goal.type);
            this.replaceFreeVar(type0, n, { type: "var", name: "0" });
            this.replaceFreeVar(typen, n, { type: "var", name: destructed });
            this.replaceFreeVar(typeSn, n, { type: "apply", name: "", nodes: [{ type: "var", name: "succ" }, { type: "var", name: destructed }] });
            matched["$indType"] = typen;
            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            goal.ast.checked = goal.type;
            goal.type = type0;
            const t = core.checkType(goal.ast.nodes[0].nodes[0].nodes[0], goal.context, false);
            goal.ast.nodes[0].nodes[0].checked = t.nodes[1];
            goal.ast.nodes[0].checked = t.nodes[1].nodes[1];
            core.checkType(goal.ast.nodes[0].nodes[1].nodes[0], goal.context, false);
            goal.ast.nodes[0].nodes[1].nodes[1].checked = wrapLambda("->", "", typen, typeSn);
            goal.ast.nodes[1].checked = wrapVar("nat");
            const anotherGoal = {
                ast: goal.ast.nodes[0].nodes[1].nodes[1].nodes[1],
                context: goal.context.slice(0),
                type: typeSn
            };
            anotherGoal.context.unshift([destructed, { type: "var", name: "nat", checked: wrapVar("nat") }, 0]);
            anotherGoal.context.unshift([induced, typen, 0]);
            core.checkType(goal.ast.nodes[0].nodes[1].nodes[1].nodes[0], anotherGoal.context, false);
            // delete anotherGoal.context[n];
            goal.ast = goal.ast.nodes[0].nodes[0].nodes[1];
            // delete goal.context[n];
            this.goal.unshift(anotherGoal);
            this.goal.unshift(goal);
        }
        else if (nType.type === "+") {
            const fnl = Core.getNewName(n + "l", excludedSet);
            const fnr = Core.getNewName(n + "r", excludedSet);
            matched["$typel"] = nType.nodes[0];
            matched["$typer"] = nType.nodes[1];
            let newAst = parser.parse(`ind_Sum (L${n}:$typeN.$1) (L${fnl}:$typel.(?#0)) (L${fnr}:$typer.(?#0)) $nast`);
            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            const newTypeL = matched["$1"];
            const newTypeR = Core.clone(goal.type);
            this.replaceFreeVar(newTypeL, n, wrapApply(wrapVar("inl"), wrapVar(fnl)));
            this.replaceFreeVar(newTypeR, n, wrapApply(wrapVar("inr"), wrapVar(fnr)));
            const anotherGoal = {
                ast: goal.ast.nodes[0].nodes[1].nodes[1],
                context: assignContext([fnr, nType.nodes[1], 0], goal.context),
                type: newTypeR
            };
            goal.ast = goal.ast.nodes[0].nodes[0].nodes[1].nodes[1];
            goal.context.unshift([fnl, nType.nodes[0], 0]);
            goal.type = newTypeL;
            this.goal.unshift(anotherGoal);
            this.goal.unshift(goal);
        }
        else if (nType.type === "X") {
            const fnl = Core.getNewName(n + "0", excludedSet);
            const fnr = Core.getNewName(n + "1", excludedSet);
            matched["$typel"] = nType.nodes[0];
            matched["$typer"] = nType.nodes[1];
            let newAst = parser.parse(`ind_Prod (Lx:$typel.$typer) (L${n}:$typeN.$1) (L${fnl}:$typel.L${fnr}:$typer.(?#0))  $nast`);
            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            const newType = matched["$1"];
            // refering
            this.replaceFreeVar(newType, n, wrapLambda(",", "", wrapVar(fnl), wrapVar(fnr)));
            goal.ast = goal.ast.nodes[0].nodes[1].nodes[1].nodes[1];
            goal.context.unshift([fnl, nType.nodes[0], 0]);
            goal.context.unshift([fnr, nType.nodes[1], 0]);
            goal.type = newType;
            // delete goal.context[n];
            this.goal.unshift(goal);
        }
        else if (nType.type === "S") {
            const fnl = Core.getNewName(n + "0", excludedSet);
            const fnr = Core.getNewName(n + "1", excludedSet);
            matched["$typel"] = nType.nodes[0];
            matched["$typer"] = nType.nodes[1];
            matched["$typerepl"] = Core.clone(nType.nodes[1]);
            this.replaceFreeVar(matched["$typerepl"], nType.name, wrapVar(fnl));
            let newAst = parser.parse(`ind_Prod (L${nType.name}:$typel.$typer) (L${n}:$typeN.$1) (L${fnl}:$typel.L${fnr}:$typerepl.(?#0))  $nast`);
            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            const newType = matched["$1"];
            // refering
            this.replaceFreeVar(newType, n, wrapApply(wrapVar("pair"), { type: "L", name: nType.name, nodes: nType.nodes }, wrapVar(fnl), wrapVar(fnr)));
            goal.ast = goal.ast.nodes[0].nodes[1].nodes[1].nodes[1];
            goal.context.unshift([fnl, nType.nodes[0], 0]);
            goal.context.unshift([fnr, matched["$typerepl"], 0]);
            goal.type = newType;
            // delete goal.context[n];
            this.goal.unshift(goal);
        }
        return this;
    }
    ex(n) {
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type !== "S")
            throw TR("ex策略只能作用于依赖积类型");
        const dfn = Core.clone(goal.type);
        dfn.type = "L";
        const val = parser.parse(n);
        Core.assign(goal.ast, wrapApply(wrapVar("pair"), dfn, val, wrapVar("(?#0)")), true);
        goal.ast.checked = goal.type;
        core.checkType(goal.ast.nodes[0], goal.context, false);
        goal.ast = goal.ast.nodes[1];
        goal.type = Core.clone(dfn.nodes[1]);
        this.replaceFreeVar(goal.type, dfn.name, val);
        core.checkType(goal.type, goal.context, false);
        this.goal.unshift(goal);
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
            type: goal.type.nodes[1]
        };
        anotherGoal.ast.checked = anotherGoal.type;
        goal.ast.checked = goal.type;
        goal.ast = goal.ast.nodes[0];
        goal.type = goal.type.nodes[0];
        goal.ast.checked = goal.type;
        this.goal.unshift(anotherGoal);
        this.goal.unshift(goal);
    }
    expand(n) {
        n = n?.trim();
        const goal = this.goal.shift();
        if (!goal)
            throw TR("无证明目标，请使用qed命令结束证明");
        try {
            if (!core.expandDef(goal.type, goal.context, n)) {
                this.goal.unshift(goal);
                throw TR("未找到任何指定展开的项");
            }
            ;
            this.whnf(goal.type, goal.context);
            core.checkType(goal.type, goal.context, false);
        }
        catch (e) { }
        this.goal.unshift(goal);
        return this;
    }
    replaceFreeVar(ast, src, dst) {
        if (ast.type === "var") {
            if (ast.name === src) {
                Core.assign(ast, dst);
            }
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            this.replaceFreeVar(ast.nodes[0], src, dst);
            if (ast.name !== src) {
                this.replaceFreeVar(ast.nodes[1], src, dst);
            }
        }
        else if (ast.nodes?.length === 2) {
            this.replaceFreeVar(ast.nodes[0], src, dst);
            this.replaceFreeVar(ast.nodes[1], src, dst);
        }
    }
    whnf(ast, context) {
        core.checkType({ type: "whnf", nodes: [ast, wrapVar("_")], name: "" }, context, true);
        return ast;
    }
}
//# sourceMappingURL=assist.js.map