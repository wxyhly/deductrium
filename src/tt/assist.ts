import { TR } from "../lang.js";
import { AST, ASTParser } from "./astparser.js";
import { assignContext, Context, Core, Varlist, wrapApply, wrapLambda, wrapVar } from "./core.js";
let core = new Core;
let parser = new ASTParser;
type GoalDependRel = { src: AST, dst: AST, goals: Goal[], varname: string };
export type Goal = { context: Context, type: AST, ast: AST, depend: GoalDependRel };
export class Assist {
    // the target theorem ast
    theorem: AST;
    // a goal has a context, a type (this is goal) and an ast pointer refered in elem
    goal: Goal[];
    // inhabited elem : theorem
    elem: AST;
    static disableMultipleApply = true;
    static disableDestructConds = true;
    static disableDestructEq = true;
    constructor(h: Core, target: AST | string) {
        core = h;
        core.clearState();
        if (typeof target === "string") { target = parser.parse(target); }
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
        if (!g) { return ["qed"]; }
        const type = g.type;
        const introVar = (n: string) => !type.name ? Core.getNewName(n, new Set(g.context.map(e => e[0]))) : type.name;
        if (type.type === "X") {
            tactics.push("case");
        } else if (type.type === "+" || type.type === "apply" && type.nodes?.[0]?.nodes?.[0]?.nodes?.[0]?.name === "Pushout") {
            tactics.push("left");
            tactics.push("right");
        } else if (type.type === "S") {
            // let found = false;
            for (const [k, v] of g.context) {
                if (Core.exactEqual(v, type.nodes[0])) {
                    tactics.push("ex " + k);
                    // found = true;
                }
            }
            tactics.push("ex");
        } else if (type.type === "P") {
            tactics.push("intro " + introVar(type.name));
        } else if (type.type === "W") {
            tactics.push("sup");
        } else if (type.name === "True") {
            tactics.push("exact true");
            return tactics;
        } else if (type.name === "Bool") {
            tactics.push("exact 0b");
            tactics.push("exact 1b");
        } else if (type.name === "nat") {
            tactics.push("exact 0");
            tactics.push("apply succ");
        } else if (type.name === "Z") {
            tactics.push("exact 0Z");
            tactics.push("apply pos");
            tactics.push("apply neg");
        } else if (type.name === "I") {
            tactics.push("apply 0I");
            tactics.push("apply 1I");
        } else if (type.type === "apply" && type.nodes[0].name === "Option") {
            tactics.push("exact none");
            tactics.push("apply some");
        } else if (type.type === "apply" && type.nodes[0].name === "List") {
            tactics.push("exact nil");
            tactics.push("apply cons");
        } else if (type.type === "apply" && type.nodes[0].name === "Sus") {
            const a = parser.stringify(type.nodes[1]);
            tactics.push("exact North " + a);
            tactics.push("exact South " + a);
        } else if (type.name === "S1") {
            tactics.push("exact base");
        } else if (type.name === "S2") {
            tactics.push("exact base2");
        } else if (type.type === "->") {
            tactics.push("intro " + introVar("h"));
        } else {
            let matchEq = Core.match(type, parser.parse("$1 = $2"), /^\$/);
            if (!matchEq) matchEq = Core.match(type, parser.parse("eq $1 $2"), /^\$/);
            if (!matchEq) matchEq = Core.match(type, parser.parse("@eq $3 $4 $1 $2"), /^\$/);
            if (matchEq) {
                if (matchEq["$1"].name === "0I" && matchEq["$2"].name === "1I") tactics.push("apply segI");
                else if (matchEq["$1"].name === "1I" && matchEq["$2"].name === "0I" && core.checkConst("inveq", [])) tactics.push("apply inveq segI");
                try {
                    if (core.checkType({ type: "===", name: "", nodes: [matchEq["$1"], matchEq["$2"]] }, g.context, false)) {
                        tactics.push("rfl");
                    }
                } catch (e) { }
                try {
                    if (core.checkType({ type: ":", name: "", nodes: [matchEq["$1"], wrapLambda("->", "", wrapVar("_"), wrapVar("_"))] }, g.context, false)) {
                        tactics.push("fnext");
                    }
                } catch (e) { }
            }
        }
        const s = new Set<string>;
        for (const [val, typ] of g.context) {
            const matchEq = Core.match(typ, parser.parse("$2 = $3"), /^\$/) || Core.match(typ, parser.parse("eq $2 $3"), /^\$/) || Core.match(typ, parser.parse("@eq $0 $1 $2 $3"), /^\$/)
            if (matchEq) {
                const fnparam = "*";
                const fnbody2 = this.genReplaceFn(g.type, matchEq["$2"], fnparam, s);
                if (Core.getFreeVars(fnbody2).has(fnparam)) tactics.push("rw " + val);

                const fnbody3 = this.genReplaceFn(g.type, matchEq["$3"], fnparam, s);
                if (Core.getFreeVars(fnbody3).has(fnparam)) tactics.push("rwb " + val);
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
            } catch (e) { }
            try {
                const k2 = {
                    type: "===", name: "", nodes: [
                        Core.clone(typ), wrapLambda("P", "_", wrapVar("_"), Core.clone(g.type))
                    ]
                };
                if (core.checkType(k2, g.context, false))
                    tactics.push("apply " + val);
            } catch (e) { }
        }
        const ntype = Core.clone(type); this.whnf(ntype, g.context);
        if (!Core.exactEqual(type, ntype)) {
            tactics.push("simpl");
        }
        const vars = Core.getFreeVars(type);
        const defs1 = Object.keys(core.state.userDefs);
        const defs2 = Object.keys(core.state.sysDefs);
        const types = new Set(Object.keys(core.state.sysTypes));
        const defs = new Set([...defs1, ...defs2]);
        const ignore = new Set(["add", "mul", "addZ", "mulZ", "addO", "mulO", "leqO", "pair", "natO", "eq", "ua", "liftU", "LiftU", "lowerU", "rfl", "refl", "inl", "inr", "pr0", "pr1", "prd1"]);
        for (const v of defs) {
            if (vars.has(v) && !g.context.find(e => e[0] === v)) {
                if (ignore.has(v) || v.startsWith("ind_") || types.has("@" + v)) continue;
                tactics.push("expand " + v);
            }
        }
        const findEqv = (ast: AST) => {
            if (!ast) return false;
            if (ast.type === "~=") return true;
            if (ast.nodes?.length) return findEqv(ast.nodes[0]) || findEqv(ast.nodes[1]);
        }
        if (findEqv(type)) tactics.push("expand eqv");
        if (this.eq(true)) tactics.push("eq");
        return tactics;
    }
    resolveDependGoal(d: GoalDependRel) {
        if (!d) return;
        const { src, dst, varname, goals } = d;
        this.replaceFreeVar(dst, varname, src);
        for (const goal of goals) {
            this.replaceFreeVar(goal.type, varname, src);
            for (const [k, v, id] of goal.context) {
                this.replaceFreeVar(v, varname, src);
            }
        }
    }
    isIndType(typ: AST) {
        return (typ.name === "nat" || typ.name === "Bool" || typ.name === "I" || typ.name === "Z" || typ.name === "S1" || typ.name === "Ord" || typ.name === "True" || typ.name === "False" || (typ.type === "apply" && (typ.nodes[0].name === "Sus" || typ.nodes[0].name === "List" || typ.nodes[0].name === "Option" || typ.nodes[0].name === "Even" || typ.nodes[0]?.nodes?.[0]?.nodes?.[0]?.name === "Pushout"))
            || typ.type === "+" || typ.type === "[[]]" || typ.type === "X" || typ.type === "S" || typ.type === "W" || (!Assist.disableDestructEq && ((typ.type === "=") || typ.nodes?.[0]?.nodes?.[0]?.name === "eq")));
    }
    intro(s: string) {
        s = s.trim();
        if (s.includes(" ")) {
            return this.intros(s);
        }
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
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
    intros(s: string) {
        if (!s?.trim()) throw TR("意外的空表达式");
        s.split(" ").map(ss => ss ? this.intro(ss) : "");
        return this;
    }

    static eq_matches = ([
        ["$1*rfl", "rightrfl $1", ["rightrfl"]],
        ["$1*(refl $2)", "rightrfl $1", ["rightrfl"]],
        ["inveq (inveq $1)", "invinveq $1", ["invinveq"]],
        ["$1 * (inveq $1)", "rightinveq $1", ["rightinveq"]],
        ["(inveq $1) * $1", "leftinveq $1", ["leftinveq"]],
        ["inveq ($1*$2)", "compinveq $1 $2", ["compinveq"]],
        ["($1*$2)*(inveq $2)", "compeqassoc $1 $2 (inveq $2)", ["compeqassoc"]],
        ["($1*(inveq $2))*$2", "compeqassoc $1 (inveq $2) $2", ["compeqassoc"]],
        ["(inveq $2)*($2*$1)", "inveq(compeqassoc (inveq $2) $2 $1)", ["compeqassoc"]],
        ["$2*((inveq $2)*$1)", "inveq(compeqassoc $2 (inveq $2) $1)", ["compeqassoc"]],
        ["trans (eq $x0) $p $q", "transright $p $q", ["transright"]],
        ["happly (fnext $x)", "happly_fnext $x"],
        ["fnext (happly $x)", "fnext_happly $x"],
        ["ua (id2eqv $x)", "ua_id2eqv $x"],
        ["id2eqv (ua $x)", "id2eqv_ua $x"],
        ["predZ (succZ $x)", "pred_succZ $x", ["pred_succZ"]],
        ["succZ (predZ $x)", "succ_predZ $x", ["succ_predZ"]],
        ["apd $C (ind_S1 $C $cb $cl) loop", "apd_loop $cl", ["apd_loop"]],
        ["ap (rec_S1 $cb $cl) loop", "ap_loop $cl", ["ap_loop"]],
        ["ap (ind_S1 $C $cb (transconst loop $cb)*$cl) loop", "ap_loop $cl", ["ap_loop"]],
        ["ap $apfn $p", "_"],// special case
        ["trans $transfn $p $x", "_"], // special case
    ] as [string, string, string[]][]).map(e => [parser.parse(e[0]), parser.parse(e[1]), e[2] || []] as [AST, AST, string[]]);
    eq(test?: boolean) {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        this.goal.unshift(goal);
        const recurse = (ast: AST, pattern: AST, resArr: Varlist[] = []) => {
            let res: Varlist;
            res = Core.match(ast, pattern, /^\$/);
            if (res) resArr.push(res);
            if (ast.nodes?.length === 2) {
                recurse(ast.nodes[0], pattern, resArr);
                recurse(ast.nodes[1], pattern, resArr);
            }
            return resArr;
        }
        const fvs = Core.getFreeVars(goal.type);
        for (let [pattern, eq, evidences] of Assist.eq_matches) {
            let unlock_yet = false;
            for (let e of evidences) {
                if (!core.checkConst(e, [])) unlock_yet = true; break;
            }
            if (unlock_yet) continue;
            const resarr = recurse(goal.type, pattern);
            for (const res of resarr) {
                const npattern = Core.clone(pattern); Core.replaceByMatch(npattern, res, /^\$/);
                for (const v of Core.getFreeVars(npattern)) {
                    // if a freevar is captured, fail
                    if (!fvs.has(v)) return false;
                }
                let tfn = res["$transfn"];
                if (tfn?.type === "L") {
                    const paramType = tfn.nodes[0];
                    const fnbody = tfn.nodes[1];
                    if (!Core.getFreeVars(fnbody).has(tfn.name) && core.checkConst("transconst", [])) {
                        eq = wrapApply(wrapVar("transconst"), res["$p"], res["$x"]);
                    } else if (fnbody.type === "=" || (fnbody.nodes?.[0]?.nodes?.[0]?.name === "eq")) {
                        let l: AST, r: AST;
                        if (fnbody.type === "=") [l, r] = fnbody.nodes;
                        else { l = fnbody.nodes[0].nodes[1]; r = fnbody.nodes[1]; }
                        if (l.type == "var" && l.name === tfn.name) {
                            if (r.type == "var" && r.name === tfn.name && core.checkConst("transleftright", [])) {
                                eq = wrapApply(wrapVar("transleftright"), res["$p"], res["$x"]);
                            } else if (!Core.getFreeVars(r).has(tfn.name) && core.checkConst("transleft", [])) {
                                eq = wrapApply(wrapVar("transleft"), res["$p"], res["$x"]);
                            } else if (core.checkConst("transeq", [])) {
                                eq = wrapApply(wrapVar("transeq"), wrapLambda("L", tfn.name, paramType, l), wrapLambda("L", tfn.name, paramType, r), res["$p"], res["$x"]);
                            }
                        } else if (r.type == "var" && r.name === tfn.name && !Core.getFreeVars(l).has(tfn.name)) {
                            eq = wrapApply(wrapVar("transright"), res["$p"], res["$x"]);
                        } else if (core.checkConst("transeq", [])) {
                            eq = wrapApply(wrapVar("transeq"), wrapLambda("L", tfn.name, paramType, l), wrapLambda("L", tfn.name, paramType, r), res["$p"], res["$x"]);
                        }
                    } else continue;
                }
                tfn = res["$apfn"];
                if (tfn?.type === "L") {
                    const fnbody = tfn.nodes[1];
                    if (!Core.getFreeVars(fnbody).has(tfn.name) && core.checkConst("apconst", [])) {
                        eq = wrapApply(wrapVar("apconst"), res["$p"], fnbody);
                    } else if (fnbody.type === "var" && fnbody.name === tfn.name && core.checkConst("apid", [])) {
                        eq = wrapApply(wrapVar("apid"), res["$p"]);
                    } else continue;
                }
                if (eq.name === "_") continue;
                if (!test) {
                    const neq = Core.clone(eq); Core.replaceByMatch(neq, res, /^\$/);
                    this.rw(neq, false, npattern);
                } else {
                    return true;
                }
            }
        }
    }
    exact(ast: AST | string) {
        if (typeof ast === "string") { ast = parser.parse(ast); }
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
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
        } catch (e) {
            try {
                core.checkType(ast, context, false);
            } catch (e) {
                throw e;
            }
            throw TR("无法对类型") + parser.stringify(ast.checked) + TR("使用exact策略作用于类型") + parser.stringify(goal.type);
        }
    }
    apply(ast: AST | string) {
        if (typeof ast === "string") { ast = parser.parse(ast); }
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
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
        } catch (e) { }
        let applyType: AST = null;
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
        } catch (e) {
            this.goal.unshift(goal);
            try {
                if (Assist.disableMultipleApply) throw e;
                this.apply2(ast); return;
            } catch (e) {
                try {
                    core.checkType(ast, context, false);
                } catch (e) {
                    throw e;
                }
                throw TR("无法对类型") + parser.stringify(ast.checked) + TR("使用apply策略作用于类型") + parser.stringify(goal.type);
            }
        }
        try {
            core.checkType(ast, context, false);
        } catch (e) {
            throw e;
        }
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
    apply2(ast: AST) {
        const goal = this.goal.shift();
        let fn: AST;
        try { fn = core.checkType(ast, goal.context, false); } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }

        let tail = fn;
        let holeNumbers = 1;
        let fnWith_ = ast;
        while (true) {
            fnWith_ = wrapApply(fnWith_, wrapVar("_"));
            if (tail.type === "->" || tail.type === "P") { tail = tail.nodes[1]; } else {
                this.goal.unshift(goal);
                throw TR("无法对类型") + parser.stringify(ast.checked) + TR("使用apply策略作用于类型") + parser.stringify(goal.type);
            }
            try {
                core.checkType(wrapLambda("===", "", Core.clone(tail), Core.clone(goal.type)), goal.context, true);
                core.checkType({ nodes: [fnWith_, Core.clone(goal.type)], type: ":", name: "" }, goal.context, false);
                break;
            } catch (e) { }
            holeNumbers++;
        }
        for (let i = holeNumbers; i > 0; i--) {
            fnWith_ = fnWith_.nodes[0];
        }
        fn = fnWith_.checked;
        const fnParams = this.flattenParams(fn, true);
        const fnParamNames = this.flattenParamNames(fn);

        const fnBody = [];
        const newGoals: Goal[] = [];
        const dependence: number[][] = [];

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
                    if (j === i) continue;
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
            if (!d.length) continue;
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
    rw(eq: string | AST, back: boolean = false, forcingMatchAST?: AST) {
        if (typeof eq === "string") eq = parser.parse(eq);
        if (!eq) throw TR("请输入用于改写的相等假设");
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        let matched: { [variable: string]: AST; };
        try {
            const t = core.checkType(eq, goal.context, false);
            matched = Core.match(t, parser.parse("$2 = $3"), /^\$/) || Core.match(t, parser.parse("eq $2 $3"), /^\$/) || Core.match(t, parser.parse("@eq $0 $1 $2 $3"), /^\$/);
        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        let isRfl = false;
        try {
            core.checkType(wrapLambda("===", "", eq, wrapVar("rfl")), goal.context, false);
            isRfl = true;
        } catch (e) {

        }

        if (!matched) {
            this.goal.unshift(goal);
            throw TR("使用rewrite策略必须提供一个相等类型");
        }
        matched["$eq"] = eq;
        const ctxtSet = new Set(goal.context.map(e => e[0]));
        const fnbody = this.genReplaceFn(goal.type, forcingMatchAST || matched[back ? "$3" : "$2"], "(?#)", ctxtSet);
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
            // F(a/b)
            matched["$fn_2"] = Core.clone(fnbody); this.replaceFreeVar(matched["$fn_2"], fnparam, matched["$2"]);
            // F(a/#y)
            matched["$fn_y"] = Core.clone(fnbody); this.replaceFreeVar(matched["$fn_y"], fnparam, wrapVar(y));
            let compeq = {};
            Core.match(fnbody, parser.parse("$1 = " + fnparam), /^\$/, compeq) ||
                Core.match(fnbody, parser.parse("eq $1 " + fnparam), /^\$/, compeq = {}) ||
                Core.match(fnbody, parser.parse("eq " + fnparam + " $2"), /^\$/, compeq = {}) ||
                Core.match(fnbody, parser.parse(fnparam + " = $2"), /^\$/, compeq = {});
            let newAst: AST;
            const wrapInvOrNot = (ast: AST, wrap: boolean) => wrap ? wrapApply(wrapVar("inveq"), ast) : ast;
            if (compeq["$2"] && !Core.getFreeVars(compeq['$2']).has(fnparam) && (!back || core.checkConst("inveq", [])) && core.checkConst("compeq", [])) {
                // h:a0=a1, a0=b -> ?:a1=b =>  h * ? 
                // h:a0=a1, a1=b -> ?:a0=b =>  inv(h) * ? 
                const newGoalAst = { type: "var", name: "(?#0)" };
                newAst = wrapLambda("*", "", wrapInvOrNot(eq, back), newGoalAst);
                Core.assign(goal.ast, newAst);
                goal.ast.checked = goal.type;
                goal.ast = goal.ast.nodes[1];
            } else if (compeq["$1"] && !Core.getFreeVars(compeq['$1']).has(fnparam) && (back || core.checkConst("inveq", [])) && core.checkConst("compeq", [])) {
                // h:b0=b1, a=b0 -> ?:a=b1 =>  ? * inv(h) 
                // h:b0=b1, a=b1 -> ?:a=b0 =>  ? * h 
                const newGoalAst = { type: "var", name: "(?#0)" };
                newAst = wrapLambda("*", "", newGoalAst, wrapInvOrNot(eq, !back));
                Core.assign(goal.ast, newAst);
                goal.ast.checked = goal.type;
                goal.ast = goal.ast.nodes[0];
            } else {
                const useTrans = core.checkConst("trans", []) && (back || core.checkConst("inveq", []));
                newAst = parser.parse(useTrans ?
                    `trans $fn ` + (back ? `$eq` : `(inveq $eq)`) : `ind_eq $2 (L${y}:$type.L${m}:${core.state.disableSimpleEq ? `eq $2 ` + y : `$2=${y}`}. P${m}:` + (back ? `$fn_2, $fn_y` : `$fn_y, $fn_2`) + `) (Lx:_.x) $3 $eq`);
                Core.replaceByMatch(newAst, matched, /^\$/);
                try { core.checkType(newAst, goal.context, false); } catch (e) {
                    this.goal.unshift(goal);
                    throw e;
                }
                newAst = { type: "apply", name: "", nodes: [newAst, { type: "var", name: "(?#0)" }] };
                Core.assign(goal.ast, newAst, true);
                goal.ast.checked = goal.type;
                goal.ast = goal.ast.nodes[1];
            }
        }
        goal.type = Core.clone(fn.nodes[1]);
        this.replaceFreeVar(goal.type, fnparam, matched[back ? "$2" : "$3"]);
        goal.ast.checked = goal.type;
        this.goal.unshift(goal);
        return this;
    }
    rwb(eq: string | AST) {
        this.rw(eq, true);
        return this;
    }
    trunc(n: string | AST) {
        // todo: 1. goal is [[a]] -> apply Lx.[x],then goal is a
        // todo: 2. goal is a = b -> apply trunc a b 
        // in autofill, there will be a condition: goal is [[a]] = b or [[a]] = [[b]] or a = [[b]]
    }
    // replace "search" in ast by "varname"
    genReplaceFn(ast: AST, search: AST, varname: string, excludedNames: Set<string>, freevarsinSearch = Core.getFreeVars(search), scope: string[] = []): AST {

        if (this.exactEqualByAlphaConversion(ast, search)) {
            let bounded = false;
            for (const v of scope) {
                if (freevarsinSearch.has(v)) {
                    bounded = true; break;
                }
            }
            if (!bounded) return { type: "var", name: varname };
        }
        if (ast.type === "var") {
            excludedNames.add(ast.name);
            return ast;
        }
        if (ast.nodes?.length === 2) {
            const nast = Core.clone(ast);
            const nscope = scope.slice(0);
            nscope.push(ast.name);
            nast.nodes[1] = this.genReplaceFn(nast.nodes[1], search, varname, excludedNames, freevarsinSearch, nscope);
            nast.nodes[0] = this.genReplaceFn(nast.nodes[0], search, varname, excludedNames, freevarsinSearch, scope);
            return nast;
        }
    }
    boundId = 0;
    exactEqualByAlphaConversion(ast1: AST, ast2: AST) {
        if (ast1 === ast2) return true;
        if (ast1.type !== ast2.type) return false;
        if (ast1.type === "var") return ast1.name === ast2.name;
        if (ast1.nodes?.length !== ast2.nodes?.length) return false;
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
                if (!this.exactEqualByAlphaConversion(ast1.nodes[i], ast2.nodes[i])) return false;
            }
        }
        return true;
    }
    search(ast: AST, search: AST): boolean {
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
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        let matched = Core.match(goal.type, parser.parse("$1 = $2"), /^\$/);
        if (!matched) matched = Core.match(goal.type, parser.parse("eq $1 $2"), /^\$/);
        if (!matched) matched = Core.match(goal.type, parser.parse("@eq $3 $4 $1 $2"), /^\$/);
        if (!matched) {
            this.goal.unshift(goal);
            throw TR("无法对非相等类型使用该策略");
        }
        try {
            if (!core.checkType({ type: "===", name: "", nodes: [matched["$1"], matched["$2"]] }, goal.context, false)) {
                throw TR("使用rfl策略失败：等式两边无法化简至相等");
            }
        } catch (e) {
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
        if (this.goal.length) throw TR("证明尚未完成");
        // core.checkType({ type: ":", name: "", nodes: [Core.clone(this.elem), Core.clone(this.theorem)] }, [], true);
    }
    simpl(str?: string) {
        if (str) {
            str = str.trim();
        }
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        const type = goal.context.find(e => e[0] === str)?.[1];
        if (!type && str) {
            this.goal.unshift(goal);
            throw TR("未知的变量：") + str;
        }
        try {
            this.whnf(type ?? goal.type, type ? goal.context.slice(0, goal.context.findIndex(e => e[0] === str)) : goal.context);
        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        this.goal.unshift(goal);
        return this;
    }
    fnext() {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        let matched: Varlist;
        try {
            const t = goal.type;
            matched = Core.match(t, parser.parse("$2 = $3"), /^\$/) || Core.match(t, parser.parse("eq $2 $3"), /^\$/) || Core.match(t, parser.parse("@eq $0 $1 $2 $3"), /^\$/);
            if (!matched) throw TR("无法对非相等类型使用该策略");
            if (!core.checkType({ type: ":", name: "", nodes: [matched["$2"], wrapLambda("->", "", wrapVar("_"), wrapVar("_"))] }, goal.context, false)) {
                throw TR("无法对非函数相等类型使用fnext策略");
            }
            this.goal.unshift(goal);
        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        this.apply(wrapApply(wrapVar("fnext")));
    }
    sup() {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        this.goal.unshift(goal);
        if (goal.type.type !== "W") throw TR("无法对非W类型使用该策略");
        const L = Core.clone(goal.type);
        L.type = "L";
        this.apply2(wrapApply(wrapVar("sup"), L));
    }
    hyp(astr: string) {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        try {
            let ast = parser.parse(astr);
            const ctxtNames = new Set(goal.context.map(e => e[0]));
            let name = Core.getNewName("hyp", ctxtNames);
            if (ast.type === ":" && ast.nodes[0].type === "var") {
                if (ctxtNames.has(ast.nodes[0].name)) throw TR("无法引入重复名称的假设变量");
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

        } catch (e) { this.goal.unshift(goal); throw e; }

    }
    private flattenParams(typ: AST, withEnd?: boolean) {
        let params: AST[] = [];
        while (typ.type === "P" || typ.type === "->") {
            params.push(typ.nodes[0]);
            typ = typ.nodes[1];
        }
        if (withEnd) params.push(typ);
        return params;
    }
    private flattenParamNames(typ: AST) {
        let names: string[] = [];
        while (typ.type === "P" || typ.type === "->") {
            names.push(typ.name);
            typ = typ.nodes[1];
        }
        return names;
    }
    destruct(n: string) {
        n = n.trim();
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        const nast = { type: "var", name: n };
        let nType: AST;
        try { nType = core.checkType(nast, goal.context, false); } catch (e) {
            this.goal.unshift(goal); throw e;
        }
        if (!this.isIndType(nType)) { this.goal.unshift(goal); throw TR("只能解构解锁的归纳类型的变量"); }

        const excludedSet = new Set(goal.context.map(e => e[0]));
        Core.getFreeVars(goal.type, excludedSet);


        const indFnName = "ind_" + ((nType.nodes?.[0]?.name === "Sus" || nType.nodes?.[0]?.name === "List" || nType.nodes?.[0]?.name === "Option" || nType.nodes?.[0]?.name === "Even") ? nType.nodes[0].name : (nType.nodes?.[0]?.nodes?.[0]?.name === "eq" || nType.type === "=") ? "eq" : nType.type === "+" ? "Sum" : nType.type === "X" ? "Prod" : nType.type === "[[]]" ? "Trunc" : nType.type === "S" ? "Prod" : nType.type === "W" ? "W" : nType.nodes?.[0]?.nodes?.[0]?.nodes?.[0]?.name === "Pushout" ? "Pushout" : nType.name);
        // x in x=y, just parameter for types 

        // nType.nodes?.[0]?.name === "Sus" ? [nType.nodes[1]] :
        const typeParams = nType.nodes?.[0]?.nodes?.[0]?.name === "eq" ? [nType.nodes[0].nodes[1]] : nType.type === "=" ? [nType.nodes[0]] : nType.type === "X" ? [wrapLambda("L", Core.getNewName("x", excludedSet), nType.nodes[0], nType.nodes[1])] : nType.type === "S" || nType.type === "W" ? [wrapLambda("L", nType.name, nType.nodes[0], nType.nodes[1])] : [];
        // y in x=y: induction on this group of types
        const groupParam = (nType.nodes?.[0]?.nodes?.[0]?.name === "eq" || nType.type === "=" || nType.nodes?.[0]?.name === "Even") ? nType.nodes[1] : null;

        // destruct with other variables in context as condition added in target C
        const conds = [];
        if (!Assist.disableDestructConds) {
            for (const [k, v, id] of goal.context) {
                if (k === n) continue;
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
            const newY = Core.getNewName(groupParam.type === "var" ? groupParam.name : indFnName === "ind_Even" ? "n" : "y", excludedSet);
            C = wrapLambda("L", newY, eqType, Core.clone(C, true));
            C.nodes[1] = this.genReplaceFn(C.nodes[1], groupParam, newY, excludedSet);
        }
        const indFn = wrapVar(indFnName);
        const indFnHead = wrapApply(indFn, ...typeParams.map(e => Core.clone(e)), Core.clone(C));
        let headType: AST;
        try {
            headType = core.checkType(indFnHead, goal.context, false);
        } catch (e) {
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
        const newGoals: Goal[] = [];
        const introNums: string[][] = [];
        const ctorOffset = typeParams.length + 1;
        const dependence: number[][] = [];
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
                    if (j === i) continue;
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
            if (!d.length) continue;
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
        if (groupParam) indFnBody.push(groupParam);
        conds.reverse();
        Core.assign(goal.ast, wrapApply(indFnHead, ...indFnBody, nast, ...conds.map(e => {
            const k = wrapVar(e[0]); k.checked = e[1]; return k;
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
    ex(n: string) {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type !== "S") throw TR("ex策略只能作用于依赖积类型");
        const dfn = Core.clone(goal.type); dfn.type = "L";
        n = n?.trim();
        if (n?.startsWith("?") || n === "_") n = null;
        try {
            let val = n ? parser.parse(n) : wrapVar("(?#0)");
            Core.assign(goal.ast, wrapApply(wrapVar("pair"), dfn, val, wrapVar("(?#0)")), true);
            goal.ast.checked = goal.type;
            if (n) {
                core.checkType(goal.ast.nodes[0], goal.context, false);
            } else {
                const newGoal: Goal = {
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

        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
    }
    left() {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type === "apply" && goal.type.nodes?.[0]?.nodes?.[0]?.nodes?.[0]?.name === "Pushout") {
            this.goal.unshift(goal);
            return this.apply(wrapApply(wrapVar("pol"), goal.type.nodes[0].nodes[0].nodes[1], goal.type.nodes[0].nodes[1], goal.type.nodes[1]));
        }
        if (goal.type.type !== "+") throw TR("left策略只能作用于和类型");
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
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type === "apply" && goal.type.nodes?.[0]?.nodes?.[0]?.nodes?.[0]?.name === "Pushout") {
            this.goal.unshift(goal);
            return this.apply(wrapApply(wrapVar("por"), goal.type.nodes[0].nodes[0].nodes[1], goal.type.nodes[0].nodes[1], goal.type.nodes[1]));
        }
        if (goal.type.type !== "+") throw TR("left策略只能作用于和类型");
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
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type !== "X") throw TR("case策略只能作用于积类型");
        Core.assign(goal.ast, { type: ",", name: "", nodes: [wrapVar("(?#0)"), wrapVar("(?#0)")] }, true);
        const anotherGoal: Goal = {
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
    expand(n: string) {
        n = n?.trim();
        if (!n) throw TR("意外的空表达式");
        const k = n.split(" ");
        if (k.length === 1) k.unshift("0");
        const pos = Number(k.shift());
        n = k.join(" ");
        if (Math.round(pos) !== pos) throw TR("未找到任何指定展开的项");
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        try {
            goal.type = core.markBondVars(core.desugar(goal.type, false), goal.context);
            if (!core.expandDef(goal.type, goal.context, n, [pos, 1])) {
                this.goal.unshift(goal);
                throw TR("未找到任何指定展开的项");
            };
            if (core.opaque.find(e => e[0] === n) && core.state.sysDefs["@" + n]) {
                core.expandDef(goal.type, goal.context, "@" + n, [0, 1])
            }
            core.markAndCheckInferedValue(goal.type, goal.context, false);
            const alphaConversionIds = new Set<number>;
            core.reduce(goal.type, goal.context, false, alphaConversionIds);
            core.doAlphaConversionByIds(goal.type, goal.context, alphaConversionIds);
            core.checkType(goal.type, goal.context, false);
        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        this.goal.unshift(goal);
        this.simpl();
        return this;
    }
    private replaceFreeVar(ast: AST, src: string, dst: AST, freevarInDst: Set<string> = Core.getFreeVars(dst)) {
        if (ast.type === "var") {
            if (ast.name === src) {
                Core.assign(ast, dst, true);
            }
        } else if (ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") {
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
        } else if (ast.nodes?.length === 2) {
            this.replaceFreeVar(ast.nodes[0], src, dst, freevarInDst);
            this.replaceFreeVar(ast.nodes[1], src, dst, freevarInDst);
        }
    }
    // private replaceVar(ast: AST, varname: string, dst: AST, context: Context = []) {
    //     Core.assign(ast, this.whnf(wrapApply(wrapLambda("L", varname, wrapVar("_"), Core.clone(ast)), Core.clone(dst)), context), true);
    // }
    private whnf(ast: AST, context: Context) {
        return core.checkType({ type: "whnf", nodes: [ast, wrapVar("_")], name: "" }, context, true);
    }
}