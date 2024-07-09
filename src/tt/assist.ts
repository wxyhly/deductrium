import { AST, ASTParser } from "./astparser.js";
import { Compute, Context, Core, wrapApply, wrapVar } from "./core.js";
let core = new Core;
let parser = new ASTParser;
export class Assist {
    theorem: AST;
    goal: { context: Context, type: AST, ast: AST }[];
    elem: AST;
    constructor(h: Core, target: AST | string) {
        core = h;
        if (typeof target === "string") { target = parser.parse(target); }
        this.theorem = Core.clone(target);
        this.elem = { type: "var", name: "(?#0)", checked: target };
        this.goal = [{ context: {}, type: target, ast: this.elem }];
    }
    ls() {
        // console.log(this.goal.length + "个证明目标：");
        // const logGoal = (goal: { context: Context, type: AST, ast: AST }) => {
        //     for (const [k, v] of Object.entries(goal.context)) {
        //         console.log("  " + k + " : " + core.print(v));
        //     }
        //     console.log("-------------------");
        //     console.log(core.print(goal.type));
        // }
        // this.goal.forEach(g => logGoal(g));
        // return this;
    }
    markTargets() {
        let count = 0;
        for (const g of this.goal) {
            g.ast.name = "?#" + (count++);
            g.ast.checked = g.type;
        }
    }
    autofillTactics() {
        const tactics = [];
        const g = this.goal[0];
        if (!g) { return ["qed"]; }
        const type = g.type;
        const introVar = (n: string) => !type.name || g.context[type.name] ? Core.getNewName(n, new Set(Object.keys(g.context))) : type.name;
        if (type.type === "+") {
            tactics.push("left");
            tactics.push("right");
        } else if (type.type === "S") {
            tactics.push("ex ??");
        } else if (type.type === "P") {
            tactics.push("intro " + introVar(type.name));
        } else if (type.name === "True") {
            tactics.push("apply true");
            return tactics;
        } else if (type.type === "->") {
            tactics.push("intro " + introVar("h"));
        } else {
            let matchEq = Core.match(type, parser.parse("eq $1 $2"), /^\$/);
            if (!matchEq) matchEq = Core.match(type, parser.parse("@eq $3 $4 $1 $2"), /^\$/);
            if (matchEq && core.equal(matchEq["$1"], matchEq["$2"], g.context)) {
                tactics.push("rfl");
                return tactics;
            }
        }
        const ntype = Core.clone(type); core.reduce(ntype); Compute.exec(ntype);
        if (!Core.exactEqual(type, ntype)) {
            tactics.push("simpl");
        }
        for (const [val, typ] of Object.entries(g.context)) {
            //todo eq'''
            const matchEq = Core.match(typ, parser.parse("eq $1 $2"), /^\$/)
            if (matchEq) {
                tactics.push("rw " + val);
                tactics.push("rwb " + val);
            }
            if (core.equal(typ, type, g.context)) tactics.push("apply " + val);
            if (this.isIndType(typ)) {
                tactics.push("destruct " + val);
            }
            if (typ.type === "->" && core.equal(typ.nodes[1], type, g.context)) {
                tactics.push("apply " + val);
            }
        }
        return tactics;
    }
    isIndType(typ: AST) {
        return (typ.name === "nat" || typ.name === "Bool" || typ.name === "True" || typ.name === "False"
            || typ.type === "+");
    }
    intro(s: string) {
        s = s.trim();
        if (s.includes(" ")) {
            return this.intros(s);
        }
        const goal = this.goal.shift();
        if (!goal) throw "无证明目标，请使用qed命令结束证明";
        if (Object.keys(goal.context).includes(s)) { this.goal.unshift(goal); throw "无法重复intro相同变量名"; }
        const tartgetType = goal.type;
        if (tartgetType.type !== "P" && tartgetType.type !== "->") {
            this.goal.unshift(goal);
            throw "intro 只能作用于函数类型";
        }
        goal.context[s] = tartgetType.nodes[0];
        // goal.ast is refferd at outter level hole,  we fill the hole first
        Core.assign(goal.ast, { "type": "L", name: s, nodes: [tartgetType.nodes[0], { type: "var", name: "(?#0)" }] });
        // console.log(s + " : " + core.print(tartgetType.nodes[0]));
        const newtype = Core.clone(tartgetType.nodes[1]);
        core.replaceVar(newtype, goal.type.name, { type: "var", name: s })
        Core.assign(goal.type, newtype);
        // then set goal.ast to refer the new smaller hole
        goal.ast = goal.ast.nodes[1];
        this.goal.unshift(goal);
        return this;
    }
    intros(s: string) {
        if (!s.trim()) throw "意外的空表达式";
        s.split(" ").map(ss => ss ? this.intro(ss) : "");
        return this;
    }
    apply(ast: AST | string) {
        if (typeof ast === "string") { ast = parser.parse(ast); }
        const goal = this.goal.shift();
        if (!goal) throw "无证明目标，请使用qed命令结束证明";
        const astType = core.check(ast, goal.context, false);
        if (core.equal(astType, goal.type, goal.context)) {
            Core.assign(goal.ast, ast);
            return this;
            // todo: skip for dependent fn, it can throw error: var not defined in the scope of the fn.
        } else if (astType.type === "P" && core.equal(astType.nodes[1], goal.type, goal.context)) {
            // goal.ast is refferd at outter level hole,  we fill the hole first
            Core.assign(goal.ast, { type: "apply", name: "", nodes: [ast, { type: "var", name: "(?#0)" }] });
            // then set goal.ast to refer the new smaller hole
            goal.ast = goal.ast.nodes[1];
            goal.type = astType.nodes[0];
            this.goal.unshift(goal);
            return this;
        } else {
            this.goal.unshift(goal);
            throw "无法对类型" + parser.stringify(astType) + "使用apply策略作用于类型" + parser.stringify(goal.type);
        }
    }
    rw(eq: string | AST) {
        if (typeof eq === "string") eq = parser.parse(eq);
        const goal = this.goal.shift();
        if (!goal) throw "无证明目标，请使用qed命令结束证明";
        const matched = Core.match(core.check(eq, goal.context, false), parser.parse("eq $2 $3"), /^\$/) || Core.match(core.check(eq, goal.context, false), parser.parse("@eq $0 $1 $2 $3"), /^\$/);
        if (!matched) {
            this.goal.unshift(goal);
            throw "使用rewrite策略必须提供一个相等类型";
        }
        const fnparam = Core.getNewName("repl", goal.context);
        const fnbody = this.genReplaceFn(goal.type, matched["$2"], fnparam, goal.context);

        // eq: eleq: eq t a b
        // type: F(a) 
        // F(a)->F(a), eleq  |- F(b)->F(a) 
        // newgoal: F(b)
        const fn = { type: "L", name: fnparam, nodes: [matched["$2"].checked, fnbody] };
        matched["$fn"] = fn;
        matched["$eq"] = eq;
        matched["$type"] = matched["$2"].checked;
        const ctxtSet = new Set(Object.keys(goal.context));
        const x = Core.getNewName("x", ctxtSet);
        const y = Core.getNewName("y", ctxtSet);
        const m = Core.getNewName("m", ctxtSet);
        let newAst = parser.parse(`ind_eq $2 (L${y}:$type.L${m}:eq $2 ${y}. P${m}:$fn ${y}, $fn $2) (L${m}:$fn $2.${m}) $3 $eq`);
        Core.replaceByMatch(newAst, matched, /^\$/);
        newAst = { type: "apply", name: "", nodes: [newAst, { type: "var", name: "(?#0)" }] };
        core.reduce(newAst);
        Core.assign(goal.ast, newAst);
        goal.ast = goal.ast.nodes[1];
        goal.type = { type: "apply", name: "", nodes: [fn, matched["$3"]] };
        core.reduce(goal.type);
        this.goal.unshift(goal);
        return this;
    }
    rwb(eq: string | AST) {
        if (typeof eq === "string") eq = parser.parse(eq);
        const goal = this.goal.shift();
        if (!goal) throw "无证明目标，请使用qed命令结束证明";
        const matched = Core.match(core.check(eq, goal.context, false), parser.parse("eq $2 $3"), /^\$/) || Core.match(core.check(eq, goal.context, false), parser.parse("@eq $0 $1 $2 $3"), /^\$/);
        if (!matched) {
            this.goal.unshift(goal);
            throw "使用rewrite策略必须提供一个相等类型";
        }

        const fnparam = Core.getNewName("repl", goal.context);
        const fnbody = this.genReplaceFn(goal.type, matched["$3"], fnparam, goal.context);

        // eq: eleq: eq t a b
        // type: F(b) 
        // F(b)->F(b), eleq  |- F(a)->F(b) 
        // newgoal: F(b)
        const fn = { type: "L", name: fnparam, nodes: [matched["$3"].checked, fnbody] };
        matched["$fn"] = fn;
        matched["$eq"] = eq;
        matched["$type"] = matched["$3"].checked;
        const ctxtSet = new Set(Object.keys(goal.context));
        const x = Core.getNewName("x", ctxtSet);
        const y = Core.getNewName("y", ctxtSet);
        const m = Core.getNewName("m", ctxtSet);
        let newAst = parser.parse(`ind_eq $2 (L${y}:$type.L${m}:eq $2 ${y}. P${m}:$fn $2, $fn ${y}) (L${m}:$fn $2.${m}) $3 $eq`);
        Core.replaceByMatch(newAst, matched, /^\$/);
        newAst = { type: "apply", name: "", nodes: [newAst, { type: "var", name: "(?#0)" }] };
        core.reduce(newAst);
        Core.assign(goal.ast, newAst);
        goal.ast = goal.ast.nodes[1];
        goal.type = { type: "apply", name: "", nodes: [fn, matched["$2"]] };
        core.reduce(goal.type);

        this.goal.unshift(goal);
        return this;
    }
    genReplaceFn(ast: AST, search: AST, varname: string, context: Context): AST {
        if (Core.exactEqual(ast, search)) {
            return { type: "var", name: varname };
        }
        if (ast.type === "var") {
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
            nast.nodes[1] = this.genReplaceFn(nast.nodes[1], search, varname, context);
            return nast;
        }
        if (ast.nodes?.length === 2) {
            const nast = Core.clone(ast);
            nast.nodes[1] = this.genReplaceFn(nast.nodes[1], search, varname, context);
            nast.nodes[0] = this.genReplaceFn(nast.nodes[0], search, varname, context);
            return nast;
        }
    }
    rfl() {
        const goal = this.goal.shift();
        if (!goal) throw "无证明目标，请使用qed命令结束证明";
        let matched = Core.match(goal.type, parser.parse("eq $1 $2"), /^\$/);
        if (!matched) matched = Core.match(goal.type, parser.parse("@eq $3 $4 $1 $2"), /^\$/);
        if (!matched) {
            this.goal.unshift(goal);
            throw "无法对非相等类型使用rfl策略";
        }
        if (!core.equal(matched["$1"], matched["$2"], goal.context)) {
            this.goal.unshift(goal);
            throw "使用rfl策略失败：等式两边无法化简至相等";
        }
        const newAst = parser.parse("rfl");
        Core.replaceByMatch(newAst, matched, /^\$/);
        Core.assign(goal.ast, newAst);
        return this;
    }
    qed() {
        if (this.goal.length) throw "证明尚未完成";
        core.checkType({ type: ":", name: "", nodes: [this.elem, this.theorem] });
    }
    simpl() {
        const goal = this.goal.shift();
        if (!goal) throw "无证明目标，请使用qed命令结束证明";
        if (!core.reduce(goal.type)) {
            Compute.exec(goal.type);
        };
        this.goal.unshift(goal);
        return this;
    }
    destruct(n: string) {
        n = n.trim();
        const param = n.split(" ");
        n = param[0];
        const goal = this.goal.shift();
        if (!goal) throw "无证明目标，请使用qed命令结束证明";
        const nast = { type: "var", name: param[0] };
        const nType = core.check(nast, goal.context, false);
        if (!this.isIndType(nType)) { this.goal.unshift(); throw "只能解构归纳类型的变量"; }
        const matched = { "$1": Core.clone(goal.type), "$nast": nast, "$typeN": nType };
        if (nType.name === "Bool") {
            let newAst = parser.parse(`ind_Bool (L${n}:$typeN.$1) (?#0) (?#0) $nast`);
            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            const type0b = Core.clone(goal.type);
            const type1b = Core.clone(goal.type);
            core.replaceVar(type0b, n, { type: "var", name: "0b" });
            core.replaceVar(type1b, n, { type: "var", name: "1b" })
            goal.type = type0b;
            const anotherGoal = {
                ast: goal.ast.nodes[0].nodes[1],
                context: Object.assign({}, goal.context),
                type: type1b
            };
            goal.ast = goal.ast.nodes[0].nodes[0].nodes[1];
            this.goal.unshift(goal);
            this.goal.unshift(anotherGoal);
            delete goal.context[n];
            delete anotherGoal.context[n];
        } else if (nType.name === "True") {
            let newAst = parser.parse(`ind_True (L${n}:$typeN.$1) (?#0) $nast`);
            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            core.replaceVar(goal.type, n, { type: "var", name: "true" });
            goal.ast = goal.ast.nodes[0].nodes[1];
            this.goal.unshift(goal);
            delete goal.context[n];
        } else if (nType.name === "False") {
            let newAst = parser.parse(`ind_False (L${n}:$typeN.$1) $nast`);
            Core.replaceByMatch(newAst, matched, /^\$/);
        } else if (nType.name === "nat") {
            const fromParam1 = param[1];
            if (fromParam1 && goal.context[fromParam1]) {
                this.goal.unshift(goal);
                throw "destruct引入了重复的变量名";
            }
            const fromParam2 = param[2];
            if (fromParam2 && (goal.context[fromParam1] || fromParam2 === fromParam1)) {
                this.goal.unshift(goal);
                throw "destruct引入了重复的变量名";
            }
            const destructed = fromParam1 || Core.getNewName(n, new Set(Object.keys(goal.context)));
            const induced = fromParam2 || Core.getNewName("H" + n, new Set(Object.keys(goal.context)));
            let newAst = parser.parse(`ind_nat (L${n}:$typeN.$1) (?#0) (L${destructed}:nat.L${induced}:$indType.(?#0)) $nast`);

            const type0 = Core.clone(goal.type);
            const typen = Core.clone(goal.type);
            const typeSn = Core.clone(goal.type);

            core.replaceVar(type0, n, { type: "var", name: "0" });
            core.replaceVar(typen, n, { type: "var", name: destructed });
            core.replaceVar(typeSn, n, { type: "apply", name: "", nodes: [{ type: "var", name: "succ" }, { type: "var", name: destructed }] });

            matched["$indType"] = typen;

            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);
            goal.type = type0;
            const anotherGoal = {
                ast: goal.ast.nodes[0].nodes[1].nodes[1].nodes[1],
                context: Object.assign({}, goal.context),
                type: typeSn
            };
            anotherGoal.context[destructed] = { type: "var", name: "nat" };
            anotherGoal.context[induced] = typen;
            delete anotherGoal.context[n];
            goal.ast = goal.ast.nodes[0].nodes[0].nodes[1];
            delete goal.context[n];
            this.goal.unshift(anotherGoal);
            this.goal.unshift(goal);
        } else if (nType.type === "+") {
            const fnl=Core.getNewName(n + "l", goal.context);
            const fnr=Core.getNewName(n + "r", goal.context);
            matched["$typel"] = nType.nodes[0];
            matched["$typer"] = nType.nodes[1];
            let newAst = parser.parse(`ind_Sum (L${n}:$typeN.$1) (L${fnl}:$typel.(?#0)) (L${fnr}:$typer.(?#0)) $nast`);

            Core.replaceByMatch(newAst, matched, /^\$/);
            Core.assign(goal.ast, newAst);

            const anotherGoal = {
                ast: goal.ast.nodes[0].nodes[1].nodes[1],
                context: Object.assign({ [fnr]: nType.nodes[1] }, goal.context),
                type: matched["$1"]
            };
            delete anotherGoal.context[n];
            goal.ast = goal.ast.nodes[0].nodes[0].nodes[1].nodes[1];
            goal.context[fnl] = nType.nodes[0];
            delete goal.context[n];
            this.goal.unshift(anotherGoal);
            this.goal.unshift(goal);
        }
        return this;
    }
    ex(n: string) {
        const goal = this.goal.shift();
        if (!goal) throw "无证明目标，请使用qed命令结束证明";
        if (goal.type.type !== "S") throw "ex策略只能作用于依赖积类型";
        const dfn = Core.clone(goal.type); dfn.type = "L";
        const val = parser.parse(n);
        Core.assign(goal.ast, wrapApply(wrapVar("pair"), dfn, val, wrapVar("(?#0)")), true);
        goal.ast = goal.ast.nodes[1];
        goal.type = wrapApply(dfn, val);
        core.reduce(goal.type);
        this.goal.unshift(goal);
    }
    left() {
        const goal = this.goal.shift();
        if (!goal) throw "无证明目标，请使用qed命令结束证明";
        if (goal.type.type !== "+") throw "left策略只能作用于和类型";
        Core.assign(goal.ast, wrapApply(wrapVar("inl"), wrapVar("(?#0)")), true);
        goal.ast = goal.ast.nodes[1];
        goal.type = goal.type.nodes[0];
        this.goal.unshift(goal);
    }
    right() {
        const goal = this.goal.shift();
        if (!goal) throw "无证明目标，请使用qed命令结束证明";
        if (goal.type.type !== "+") throw "left策略只能作用于和类型";
        Core.assign(goal.ast, wrapApply(wrapVar("inr"), wrapVar("(?#0)")), true);
        goal.ast = goal.ast.nodes[1];
        goal.type = goal.type.nodes[1];
        this.goal.unshift(goal);
    }
}