import { HoTT } from "./check.js";
const hott = new HoTT;
export class Assist {
    theorem;
    theoremStr;
    goal;
    elem;
    constructor(target) {
        if (typeof target === "string") {
            this.theoremStr = target;
            target = hott.parse(target);
        }
        this.theorem = hott.clone(target);
        this.elem = { type: "var", name: "(#0)" };
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
    intro(s) {
        s = s.trim();
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
        hott.assign(goal.ast, { "type": "L", name: s, nodes: [tartgetType.nodes[0], { type: "var", name: "(#0)" }] });
        // console.log(s + " : " + hott.print(tartgetType.nodes[0]));
        const newtype = hott.clone(tartgetType.nodes[1]);
        hott.replaceVar(newtype, goal.type.name, { type: "var", name: s });
        hott.assign(goal.type, newtype);
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
        }
        else if (astType.type === "P" && hott.equal(astType.nodes[1], goal.type, goal.context)) {
            hott.assign(goal.ast, { type: "apply", name: "", nodes: [ast, { type: "var", name: "(#0)" }] });
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
        newAst = { type: "apply", name: "", nodes: [newAst, { type: "var", name: "(#0)" }] };
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
        newAst = { type: "apply", name: "", nodes: [newAst, { type: "var", name: "(#0)" }] };
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
        return hott.print(this.elem);
    }
}
//# sourceMappingURL=assist.js.map