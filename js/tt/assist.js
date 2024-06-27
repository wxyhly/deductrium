import { HoTT } from "./check.js";
let hott = new HoTT;
export class Assist {
    theorem;
    theoremStr;
    goal;
    elem;
    constructor(h, target) {
        hott = h;
        if (typeof target === "string") {
            this.theoremStr = target;
            target = hott.parse(target);
        }
        this.theorem = hott.clone(target);
        this.elem = { type: "var", name: "(?#0)" };
        this.goal = [{ context: {}, type: target, ast: this.elem }];
    }
    ls() {
        console.log(this.goal.length + "个证明目标：");
        const logGoal = (goal) => {
            for (const [k, v] of Object.entries(goal.context)) {
                console.log("  " + k + " : " + hott.print(v));
            }
            console.log("-------------------");
            console.log(hott.print(goal.type));
        };
        this.goal.forEach(g => logGoal(g));
        return this;
    }
    markTargets() {
        let count = 0;
        for (const g of this.goal) {
            g.ast.name = "?#" + (count++);
        }
    }
    autofillTactics() {
        const tactics = [];
        const g = this.goal[0];
        if (!g) {
            return ["qed"];
        }
        const type = g.type;
        const introVar = (n) => g.context[type.name] ? hott.getNewName(n, new Set(Object.keys(g.context))) : type.name;
        if (type.type === "P") {
            tactics.push("intro " + introVar(type.name));
        }
        else if (type.name === "True") {
            tactics.push("apply true");
            return tactics;
        }
        else if (type.type === "->") {
            tactics.push("intro " + introVar("k"));
        }
        else {
            //todo eq'''
            const matchEq = hott.match(type, hott.parse("eq $1 $2 $3"));
            if (matchEq && hott.equal(matchEq["$2"], matchEq["$3"], g.context)) {
                tactics.push("reflexivity");
                return tactics;
            }
        }
        const ntype = hott.clone(type);
        hott.expandDefinition(ntype, g.context);
        if (!hott.exactEqual(type, ntype)) {
            tactics.push("simpl");
        }
        for (const [val, typ] of Object.entries(g.context)) {
            //todo eq'''
            const matchEq = hott.match(typ, hott.parse("eq $1 $2 $3"));
            if (matchEq) {
                tactics.push("rewrite " + val);
                tactics.push("rewriteBack " + val);
            }
            if (hott.equal(typ, type, g.context))
                tactics.push("apply " + val);
            if (this.isIndType(typ)) {
                tactics.push("destruct " + val);
            }
            if (type.type === "->" && hott.equal(typ.nodes[1], type, g.context)) {
                tactics.push("apply " + val);
            }
        }
        return tactics;
    }
    isIndType(typ) {
        return typ.name === "nat" || typ.name === "Bool" || typ.name === "True" || typ.name === "False";
    }
    intro(s) {
        s = s.trim();
        if (s.includes(" ")) {
            return this.intros(s);
        }
        const goal = this.goal.shift();
        if (!goal)
            throw "无证明目标，请使用qed命令结束证明";
        if (Object.keys(goal.context).includes(s)) {
            this.goal.unshift(goal);
            throw "无法重复intro相同变量名";
        }
        const tartgetType = goal.type;
        if (tartgetType.type !== "P") {
            this.goal.unshift(goal);
            throw "intro 只能作用于函数类型";
        }
        goal.context[s] = tartgetType.nodes[0];
        // goal.ast is refferd at outter level hole,  we fill the hole first
        hott.assign(goal.ast, { "type": "L", name: s, nodes: [tartgetType.nodes[0], { type: "var", name: "(?#0)" }] });
        // console.log(s + " : " + hott.print(tartgetType.nodes[0]));
        const newtype = hott.clone(tartgetType.nodes[1]);
        hott.replaceVar(newtype, goal.type.name, { type: "var", name: s });
        hott.assign(goal.type, newtype);
        // then set goal.ast to refer the new smaller hole
        goal.ast = goal.ast.nodes[1];
        this.goal.unshift(goal);
        return this;
    }
    intros(s) {
        if (!s.trim())
            throw "意外的空表达式";
        s.split(" ").map(ss => ss ? this.intro(ss) : "");
        return this;
    }
    apply(ast) {
        if (typeof ast === "string") {
            ast = hott.parse(ast);
        }
        const goal = this.goal.shift();
        if (!goal)
            throw "无证明目标，请使用qed命令结束证明";
        const astType = hott.check(ast, goal.context);
        if (hott.equal(astType, goal.type, goal.context)) {
            hott.assign(goal.ast, ast);
            return this;
            // todo: skip for dependent fn, it can throw error: var not defined in the scope of the fn.
        }
        else if (astType.type === "P" && hott.equal(astType.nodes[1], goal.type, goal.context)) {
            // goal.ast is refferd at outter level hole,  we fill the hole first
            hott.assign(goal.ast, { type: "apply", name: "", nodes: [ast, { type: "var", name: "(?#0)" }] });
            // then set goal.ast to refer the new smaller hole
            goal.ast = goal.ast.nodes[1];
            goal.type = astType.nodes[0];
            this.goal.unshift(goal);
            return this;
        }
        else {
            this.goal.unshift(goal);
            throw "无法对类型" + hott.print(astType) + "使用apply策略作用于类型" + hott.print(goal.type);
        }
    }
    rewrite(eq) {
        if (typeof eq === "string")
            eq = hott.parse(eq);
        const goal = this.goal.shift();
        if (!goal)
            throw "无证明目标，请使用qed命令结束证明";
        const matched = hott.match(hott.check(eq, goal.context), hott.parse("eq $1 $2 $3"));
        if (!matched) {
            this.goal.unshift(goal);
            throw "使用rewrite策略必须提供一个相等类型";
        }
        const fn = this.genReplaceFn(goal.type, matched["$2"], goal.context);
        // eq: eleq: eq t a b
        // type: F(a) 
        // F(a)->F(a), eleq  |- F(b)->F(a) 
        // newgoal: F(b)
        matched["$fn"] = fn;
        matched["$eq"] = eq;
        const ctxtSet = new Set(Object.keys(goal.context));
        const x = hott.getNewName("x", ctxtSet);
        const y = hott.getNewName("y", ctxtSet);
        const m = hott.getNewName("m", ctxtSet);
        let newAst = hott.parse(`ind_eq $1 (L${x}:$1.L${y}:$1.L${m}:eq $1 ${x} ${y}. P${m}:$fn ${y}, $fn ${x}) (L${x}:$1.L${m}:$fn ${x}.${m}) $2 $3 $eq`);
        hott.replaceByMatch(newAst, matched);
        newAst = { type: "apply", name: "", nodes: [newAst, { type: "var", name: "(?#0)" }] };
        hott.assign(goal.ast, newAst);
        goal.ast = goal.ast.nodes[1];
        goal.type = { type: "apply", name: "", nodes: [fn, matched["$3"]] };
        hott.expandDefinition(goal.type, goal.context);
        this.goal.unshift(goal);
        return this;
    }
    rewriteBack(eq) {
        if (typeof eq === "string")
            eq = hott.parse(eq);
        const goal = this.goal.shift();
        if (!goal)
            throw "无证明目标，请使用qed命令结束证明";
        const matched = hott.match(hott.check(eq, goal.context), hott.parse("eq $1 $2 $3"));
        if (!matched) {
            this.goal.unshift(goal);
            throw "使用rewrite策略必须提供一个相等类型";
        }
        const fn = this.genReplaceFn(goal.type, matched["$3"], goal.context);
        // eq: eleq: eq t a b
        // type: F(b) 
        // F(b)->F(b), eleq  |- F(a)->F(b) 
        // newgoal: F(b)
        matched["$fn"] = fn;
        matched["$eq"] = eq;
        const ctxtSet = new Set(Object.keys(goal.context));
        const x = hott.getNewName("x", ctxtSet);
        const y = hott.getNewName("y", ctxtSet);
        const m = hott.getNewName("m", ctxtSet);
        let newAst = hott.parse(`ind_eq $1 (L${x}:$1.L${y}:$1.L${m}:eq $1 ${x} ${y}. P${m}:$fn ${x}, $fn ${y}) (L${y}:$1.L${m}:$fn ${y}.${m}) $2 $3 $eq`);
        hott.replaceByMatch(newAst, matched);
        newAst = { type: "apply", name: "", nodes: [newAst, { type: "var", name: "(?#0)" }] };
        hott.assign(goal.ast, newAst);
        goal.ast = goal.ast.nodes[1];
        goal.type = { type: "apply", name: "", nodes: [fn, matched["$2"]] };
        hott.expandDefinition(goal.type, goal.context);
        this.goal.unshift(goal);
        return this;
    }
    genReplaceFn(ast, search, context = {}, searchType = hott.check(search, context), searchFVs = hott.getFreeVars(search), newCtxt = context) {
        const x = hott.getNewName("repl", new Set(Object.keys(context)));
        if (hott.equal(ast, search, context)) {
            return { type: "L", name: x, nodes: [searchType, { type: "var", name: x }] };
        }
        if (ast.type === "var") {
            return { type: "L", name: x, nodes: [searchType, hott.clone(ast)] };
        }
        if (ast.type === "apply") {
            const l1 = { type: "apply", name: "", nodes: [this.genReplaceFn(ast.nodes[0], search, context, searchType, searchFVs), { type: "var", name: x }] };
            const l2 = { type: "apply", name: "", nodes: [this.genReplaceFn(ast.nodes[1], search, context, searchType, searchFVs), { type: "var", name: x }] };
            const fn = {
                type: "L", name: x, nodes: [searchType, { type: "apply", name: "", nodes: [l1, l2] }]
            };
            hott.expandDefinition(fn, newCtxt);
            return fn;
        }
        if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            const x = hott.getNewName("repl", new Set([ast.name, ...Object.keys(context)]));
            const l1 = { type: "apply", name: "", nodes: [this.genReplaceFn(ast.nodes[0], search, context, searchType, searchFVs), { type: "var", name: x }] };
            let l2;
            if (searchFVs.has(ast.name)) {
                l2 = ast.nodes[1];
            }
            else {
                const ctxt = Object.assign({}, context);
                if (hott.getFreeVars(ast.nodes[0]).has(ast.name)) {
                    // cancel dangerous loop quote by alpha conversion
                    // x:c, x: f(x) => x':c, x:f(x')
                    const newVarname = hott.getNewName(ast.name, new Set(Object.keys(ctxt)));
                    ctxt[newVarname] = ctxt[ast.name];
                    const newtype = hott.clone(ast.nodes[0]);
                    hott.replaceVar(newtype, ast.name, { type: "var", name: newVarname });
                    ctxt[ast.name] = newtype;
                }
                ctxt[ast.name] = ast.nodes[0];
                const newCtxt = Object.assign({}, ctxt);
                newCtxt[ast.name] = l1;
                l2 = { type: "apply", name: "", nodes: [this.genReplaceFn(ast.nodes[1], search, ctxt, searchType, searchFVs, newCtxt), { type: "var", name: x }] };
            }
            const fn = {
                type: "L", name: x, nodes: [searchType, { type: ast.type, name: ast.name, nodes: [l1, l2] }]
            };
            hott.expandDefinition(fn, newCtxt);
            return fn;
        }
    }
    reflexivity() {
        const goal = this.goal.shift();
        if (!goal)
            throw "无证明目标，请使用qed命令结束证明";
        const matched = hott.match(goal.type, hott.parse("eq $1 $2 $3"));
        if (!matched) {
            this.goal.unshift(goal);
            throw "无法对非相等类型使用reflexivity策略";
        }
        if (!hott.equal(matched["$2"], matched["$3"], goal.context)) {
            this.goal.unshift(goal);
            throw "使用reflexivity策略失败：等式两边无法化简至相等";
        }
        const newAst = hott.parse("refl $1 $2");
        hott.replaceByMatch(newAst, matched);
        hott.assign(goal.ast, newAst);
        return this;
    }
    qed() {
        if (this.goal.length)
            throw "证明尚未完成";
        hott.checkProof(this.elem, this.theorem);
    }
    simpl() {
        const goal = this.goal.shift();
        if (!goal)
            throw "无证明目标，请使用qed命令结束证明";
        hott.expandDefinition(goal.type, goal.context);
        this.goal.unshift(goal);
        return this;
    }
    destruct(n) {
        n = n.trim();
        const param = n.split(" ");
        n = param[0];
        const goal = this.goal.shift();
        if (!goal)
            throw "无证明目标，请使用qed命令结束证明";
        const nast = { type: "var", name: param[0] };
        const nType = hott.check(nast, goal.context);
        if (!this.isIndType(nType)) {
            this.goal.unshift();
            throw "只能解构归纳类型的变量";
        }
        const matched = { "$1": hott.clone(goal.type), "$nast": nast, "$typeN": nType };
        if (nType.name === "Bool") {
            let newAst = hott.parse(`ind_Bool (L${n}:$typeN.$1) (?#0) (?#0) $nast`);
            hott.replaceByMatch(newAst, matched);
            hott.assign(goal.ast, newAst);
            const type0b = hott.clone(goal.type);
            const type1b = hott.clone(goal.type);
            hott.replaceVar(type0b, n, { type: "var", name: "0b" });
            hott.replaceVar(type1b, n, { type: "var", name: "1b" });
            goal.type = type0b;
            const anotherGoal = {
                ast: goal.ast.nodes[0].nodes[1],
                context: Object.assign({}, goal.context),
                type: type1b
            };
            goal.ast = goal.ast.nodes[0].nodes[0].nodes[1];
            this.goal.unshift(goal);
            this.goal.unshift(anotherGoal);
        }
        else if (nType.name === "True") {
            let newAst = hott.parse(`ind_True (L${n}:$typeN.$1) (?#0) $nast`);
            hott.replaceByMatch(newAst, matched);
            hott.assign(goal.ast, newAst);
            hott.replaceVar(goal.type, n, { type: "var", name: "true" });
            goal.ast = goal.ast.nodes[0].nodes[1];
            this.goal.unshift(goal);
        }
        else if (nType.name === "False") {
            let newAst = hott.parse(`ind_False (L${n}:$typeN.$1) $nast`);
            hott.replaceByMatch(newAst, matched);
        }
        else if (nType.name === "nat") {
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
            const destructed = fromParam1 || hott.getNewName(n, new Set(Object.keys(goal.context)));
            const induced = fromParam2 || hott.getNewName("H" + n, new Set(Object.keys(goal.context)));
            let newAst = hott.parse(`ind_nat (L${n}:$typeN.$1) (?#0) (L${destructed}:nat.L${induced}:$indType.(?#0)) $nast`);
            const type0 = hott.clone(goal.type);
            const typen = hott.clone(goal.type);
            const typeSn = hott.clone(goal.type);
            hott.replaceVar(type0, n, { type: "var", name: "0" });
            hott.replaceVar(typen, n, { type: "var", name: destructed });
            hott.replaceVar(typeSn, n, { type: "apply", name: "", nodes: [{ type: "var", name: "succ" }, { type: "var", name: destructed }] });
            matched["$indType"] = typen;
            hott.replaceByMatch(newAst, matched);
            hott.assign(goal.ast, newAst);
            goal.type = type0;
            const anotherGoal = {
                ast: goal.ast.nodes[0].nodes[1].nodes[1].nodes[1],
                context: Object.assign({}, goal.context),
                type: typeSn
            };
            anotherGoal.context[destructed] = { type: "var", name: "nat" };
            anotherGoal.context[induced] = typen;
            // delete anotherGoal.context[n];
            goal.ast = goal.ast.nodes[0].nodes[0].nodes[1];
            // delete goal.context[n];
            this.goal.unshift(anotherGoal);
            this.goal.unshift(goal);
        }
        return this;
    }
}
//# sourceMappingURL=assist.js.map