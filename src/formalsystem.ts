import { ASTMgr, AST, ASTMatchResult } from "./astmgr.js";
export type DeductionStep = { conditionIdxs: number[], deductionIdx: number, replaceValues: AST[] }
export type Deduction = { value: AST, conditions: AST[], netConditions: AST[], conclusion: AST, replaceNames: string[], from: string, steps?: DeductionStep[] };
export type MetaRule = { value: AST, conditions: AST[], conclusions: AST[], replaceNames: string[], from: string };
export type Proposition = { value: AST, from: DeductionStep };
export type DeductInlineMode = "inline" | "deep" | null;
const astmgr = new ASTMgr;
export class FormalSystem {
    hypothesisAmount: number = 0;
    deductions: Deduction[] = [];
    metaRules: { [key: string]: MetaRule } = {};
    deductionReplNameRule: RegExp = /^\$/g;
    localNameRule: RegExp = /^\#/g;
    replacedLocalNameRule: RegExp = /^&/g;
    consts = new Map<string, number>([["0", -1], ["1", -1], ["2", -1], ["3", -1], ["4", -1], ["5", -1], ["6", -1], ["7", -1], ["8", -1], ["9", -1]]); // [constName -> defineDeductionIdx]
    fns = new Map<string, number>([["S", -1], ["P", -1], ["Pow", -1], ["Union", -1]]); // [fnName -> defineDeductionIdx]
    fnParamNames = (n: number) => "#" + n;
    propositions: Proposition[] = [];
    private tempMQDs: number[] = [];
    private ast2deduction(ast: AST): Deduction {
        this.checkGrammer(ast, "d");
        const [conditions, conclusions] = ast.nodes;
        const netConditions = conditions.nodes.map(c => {
            const netC = astmgr.clone(c);
            this.getNetCondition(netC);
            return netC;
        });
        const allReplNames = this.getAllReplNames([...conditions.nodes, ...conclusions.nodes]);
        const conditionReplNames = this.getAllReplNames(netConditions);
        return {
            value: ast,
            conclusion: conclusions.nodes[0],
            conditions: conditions.nodes,
            replaceNames: Array.from(allReplNames).filter(e => !conditionReplNames.has(e)).sort(),
            netConditions,
            from: ""
        };
    }
    private ast2metaRule(ast: AST): MetaRule {
        let grammarCheck = ast.type === "meta" && ast.name === "⊢M" && ast.nodes?.length === 2;
        if (!grammarCheck) throw "未找到元推理符号";
        const [conditions, conclusions] = ast.nodes;
        if (!conclusions.nodes?.length) throw "元推理符号后面没有结论";
        return {
            value: ast,
            conclusions: conclusions.nodes,
            conditions: conditions.nodes,
            replaceNames: [],
            from: ""
        };
    }
    private getNetCondition(condition: AST) {
        if (condition.type === "fn" && condition.name === "#nf") {
            astmgr.assign(condition, condition.nodes[0]);
            this.getNetCondition(condition);
        } else if (condition.nodes?.length) {
            for (const n of condition.nodes) this.getNetCondition(n);
        }
    }
    private checkGrammer(ast: AST, type: "m" | "d" | "p" | "v" | "i") {
        if (ast.type.startsWith("$")) throw "意外的错误：循环替换标记$未被正确清除";
        if (type === "v") {
            const netAst = astmgr.clone(ast);
            this.getNetCondition(netAst);
            if (netAst.type !== "replvar") throw `表达式出现在了变量的位置中`;
            return netAst.name;
        }
        if (ast.type === "meta") {
            if (ast.name === "⊢M") if (type !== "m") throw "元推理符号⊢M只能出现在元推理规则中";
            if (ast.name === "⊢") if (type !== "d") throw "推理符号⊢只能出现在推理规则中";
            if (ast.name === "⊢" || ast.name === "⊢M") {
                //check arrays
                if (ast.nodes?.length !== 2) throw "元推理/推理符号子节点数目必须为2";
                const [cond, conc] = ast.nodes;
                if (cond.type !== "fn" || cond.name !== "#array") throw "元推理/推理符号的条件格式必须为数组";
                if (conc.type !== "fn" || conc.name !== "#array") throw "元推理/推理符号的结论格式必须为数组";
                if (ast.name === "⊢" && conc.nodes?.length !== 1) throw "推理符号的结论数必须为1";
                if (ast.name === "⊢M" && !conc.nodes?.length) throw "元推理符号的结论不能为空";
                if (type === "m") return; // skip metarule check: check it by hand
                if (cond.nodes?.length) {
                    for (const cd of cond.nodes) {
                        try {
                            this.checkGrammer(cd, "p");
                        } catch (e) {
                            throw `条件中` + e;
                        }
                    }
                }
                for (const cc of conc.nodes) {
                    try {
                        this.checkGrammer(cc, "p");
                    } catch (e) {
                        throw `结论中` + e;
                    }
                }
                return;
            }
        }
        if (ast.type === "sym") {
            if (type === "m") throw "未找到元推理符号";
            if (type === "d") throw "未找到推理符号";
            if (ast.name === "E" || ast.name === "V" || ast.name === "E!") {
                let varName: string;
                try {
                    varName = this.checkGrammer(ast.nodes[0], "v");
                } catch (e) {
                    throw `量词${ast.name}的变量中：${e}`;
                }
                if (this.consts.has(varName)) {
                    throw `在d${this.consts.get(varName)}中定义的常数符号${varName}禁止出现在量词${ast.name}的约束变量中`;
                }
                this.checkGrammer(ast.nodes[1], "p");
                return;
            }
            if (ast.name === "U" || ast.name === "I") {
                if (type !== "i") throw "意外出现集合表达式";
                this.checkGrammer(ast.nodes[0], "i");
                this.checkGrammer(ast.nodes[1], "i");
                return;
            }

            if (ast.name === "@" || ast.name === "=" || ast.name === "<") {
                if (type !== "p") throw "意外出现原子谓词公式";
                this.checkGrammer(ast.nodes[0], "i");
                this.checkGrammer(ast.nodes[1], "i");
                return;
            }
        }
        if (type === "m") return "未找到元推理符号";
        if (type === "d") return "未找到推理符号";
        if (ast.type === "fn") {
            if (ast.name === "#repl" || ast.name === "#canrepl") {
                if (ast.nodes?.length !== 3) throw `系统函数${ast.name}的参数个数必须为三个`;
            }
            if (ast.name === "#nf") {
                if (!(ast.nodes?.length > 1)) throw `系统函数${ast.name}的参数个数必须至少有两个`;
                for (let i = 1; i < ast.nodes.length; i++) {
                    try {
                        this.checkGrammer(ast.nodes[i], "v");
                    } catch (e) {
                        throw `系统函数${ast.name}第${i + 1}个参数中：${e}`;
                    }
                }
            }
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) this.checkGrammer(n, "p");
        }
    }
    private getReplNames(ast: AST): Set<string> {
        const replNames = new Set<string>;
        if (ast.name.match(this.deductionReplNameRule)) {
            if (ast.type === "fn") {
                replNames.add(ast.name + `(${ast.nodes.map((v, idx) => this.fnParamNames(idx)).join(",")})`);
                for (const n of ast.nodes) this.getReplNames(n).forEach(v => replNames.add(v));
                return replNames;
            }
            replNames.add(ast.name);
            return replNames;
        }
        if (ast.nodes) for (const n of ast.nodes) this.getReplNames(n).forEach(v => replNames.add(v));
        return replNames;
    }
    private getAllReplNames(asts: AST[]): Set<string> {
        const replNames = new Set<string>;
        for (const ast of asts) {
            this.getReplNames(ast).forEach(str => replNames.add(str));
        }
        return replNames;
    }
    addDeduction(d: AST, from: string, macro?: DeductionStep[]) {
        const deduction = this.ast2deduction(d);
        deduction.from = from;
        deduction.steps = macro;
        return this.deductions.push(deduction) - 1;
    }
    addMetaRule(name: string, m: AST, from: string) {
        const metaRule = this.ast2metaRule(m);
        metaRule.from = from;
        this.metaRules[name] = metaRule;
    }
    addHypothese(m: AST) {
        this.checkGrammer(m, "p");
        if (this.hypothesisAmount !== this.propositions.length) return false;
        if (this._hasLocalNames(m)) throw "假设中不能出现局部变量";
        if (!this.expandNofreeFn(m, this.deductionReplNameRule, null, this.replacedLocalNameRule)) throw "假设中的附加条件自相矛盾";
        this.propositions.push({ value: m, from: null });
        this.hypothesisAmount++;
    }
    private _replaceLocalNames(ast: AST, prefix: string) {
        if (ast.type === "replvar" && ast.name.match(this.localNameRule)) {
            ast.name = prefix + ast.name;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this._replaceLocalNames(n, prefix);
            }
        }
    }
    private _hasLocalNames(ast: AST) {
        if (ast.type === "replvar" && ast.name.match(this.localNameRule)) {
            return true;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                if (this._hasLocalNames(n)) return true;
            }
        }
        return false;
    }
    addMacro(propositionIdx: number, from: string) {
        if (propositionIdx < this.hypothesisAmount) throw "无有效定理推导步骤，创建宏推导失败";
        const conditions: AST[] = [];
        for (let i = 0; i < this.hypothesisAmount; i++) {
            conditions.push(this.propositions[i].value);
        }
        const conclusion = this.propositions[propositionIdx].value;
        if (this._hasLocalNames(conclusion)) {
            throw "局部变量不能出现在推理宏的结论中";
        }
        const macro: DeductionStep[] = [];
        for (let i = this.hypothesisAmount; i <= propositionIdx; i++) {
            const step = this.propositions[i].from;
            macro.push({
                conditionIdxs: step.conditionIdxs.map(
                    cidx => cidx < this.hypothesisAmount ? cidx : cidx - i
                ),
                replaceValues: step.replaceValues.map(v => {
                    const newv = astmgr.clone(v);
                    this._replaceLocalNames(newv, "&" + this.deductions.length);
                    return newv;
                }),
                deductionIdx: step.deductionIdx
            });
        }
        return this.addDeduction({
            type: "meta", name: "⊢", nodes: [
                { type: "fn", name: "#array", nodes: conditions },
                { type: "fn", name: "#array", nodes: [conclusion] },
            ]
        }, from, macro);
    }
    removePropositions(amount?: number) {
        if (!isFinite(amount)) {
            this.propositions = [];
            this.hypothesisAmount = 0;
        } else {
            while (amount--) {
                this.propositions.pop();
            }
            this.hypothesisAmount = Math.min(this.propositions.length, this.hypothesisAmount);
        }
    }
    setPropositions(ps: Proposition[]) {
        this.propositions = ps;
        this.hypothesisAmount = Math.max(0, ps.findIndex(p => p.from));
    }
    removeLastDeduction() {
        const didx = this.deductions.length - 1;
        for (const [name, idx] of this.consts) {
            if (didx === idx) { this.consts.delete(name); break; }
        }
        for (const [idx, target] of this.tempMQDs.entries()) {
            if (target === idx) {
                this.tempMQDs[idx] = null; break;
            }
        }
        this.deductions.pop();
    }
    isNameCanBeNewConst(name: string) {
        if (this.consts.has(name)) return `"${name}" 已在d${this.consts.get(name)}中被定义，无法重复定义`;
        for (const [idx, d] of this.deductions.entries()) {
            if (this.isNameQuantVarIn(name, d.value)) return `"${name}" 已作为量词中的约束变量出现在了d${idx}中，无法定义为常量符号`;
        }
        for (const [idx, p] of this.propositions.entries()) {
            if (this.isNameQuantVarIn(name, p.value)) return `"${name}" 已作为量词中的约束变量出现在了p${idx}中，无法定义为常量符号`;
        }
        return true;
    }
    isNameQuantVarIn(name: string, ast: AST) {
        if (ast.type === "sym" && (ast.name === "E" || ast.name === "V" || ast.name === "E!")) {
            const netVar = astmgr.clone(ast.nodes[0]);
            this.getNetCondition(netVar);
            if (name === netVar.name) return true;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                if (this.isNameQuantVarIn(name, n)) return true;
            }
        }
        return false;
    }
    deduct(step: DeductionStep, inlineMode?: DeductInlineMode | ((step: DeductionStep, conclusion: AST) => DeductInlineMode)) {
        const { conditionIdxs, deductionIdx, replaceValues } = step;
        const deduction = this.deductions[deductionIdx];
        const { conditions, conclusion, replaceNames, steps, netConditions } = deduction;
        const errorMsg = `d${deductionIdx} 推理失败: `;

        // find repls provided by user, replfns must be by user

        // firstly, check and reduce nf fns in user's inputs
        replaceValues.forEach((ast, idx) => {
            try { this.checkGrammer(ast, "p"); } catch (e) { throw errorMsg + `替代${replaceNames[idx]}的表达式中发生语法错误：` + e; }
            if (!this.expandNofreeFn(ast, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule)) {
                throw errorMsg + `替代${replaceNames[idx]}的表达式中的附加条件自相矛盾`;
            }
        });

        // build repl table for matching

        let replsMatchTable: ASTMatchResult = Object.fromEntries(replaceNames.map((replname: string, idx: number) => [replname, replaceValues[idx]]));

        // then match given condition props with net condition (with #nf peeled)
        for (const [conditionIdx, condition] of conditions.entries()) {
            const condPropIdx = conditionIdxs[conditionIdx];
            const condProp = this.propositions[condPropIdx];
            if (!condProp) throw errorMsg + `第${conditionIdx + 1}个条件对应的定理p${condPropIdx}不存在`;
            // before matching, expand user defined fns in net condition
            const expandedNetCondition = astmgr.clone(netConditions[conditionIdx]);
            astmgr.expandReplFn(expandedNetCondition, this.fnParamNames, replsMatchTable);
            replsMatchTable = astmgr.mergeMatchResults(
                replsMatchTable,
                astmgr.match(condProp.value, expandedNetCondition, this.deductionReplNameRule)
            );
            if (!replsMatchTable) throw errorMsg + `无法匹配第${conditionIdx + 1}个条件`;
        }

        // replace replvars in conditions, test and expand #nf

        // preventCircularReplace in fn's contents
        for (const [key, ast] of Object.entries(replsMatchTable)) {
            const clonedAst = astmgr.clone(ast);
            astmgr.preventCircularReplace(clonedAst, this.deductionReplNameRule);
            replsMatchTable[key] = clonedAst;
        }

        for (const [conditionIdx, condition] of conditions.entries()) {
            const condPropIdx = conditionIdxs[conditionIdx];
            const condProp = this.propositions[condPropIdx];
            const replacedCondition = astmgr.clone(condition);
            astmgr.expandReplFn(replacedCondition, this.fnParamNames, replsMatchTable);
            astmgr.replaceByMatchResult(replacedCondition, replsMatchTable);
            astmgr.finishReplace(replacedCondition);
            if (!this.expandNofreeFn(replacedCondition, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule)) throw errorMsg + `第${conditionIdx + 1}个条件中的附加条件无法满足`;
            this.expandCanreplFn(replacedCondition, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule);
            this.expandReplFn(replacedCondition, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule);
            if (!astmgr.equal(replacedCondition, condProp.value)) throw errorMsg + `第${conditionIdx + 1}个条件中的附加条件无法满足`;
        }

        let replacedConclusion = astmgr.clone(conclusion);
        astmgr.expandReplFn(replacedConclusion, this.fnParamNames, replsMatchTable);
        astmgr.replaceByMatchResult(replacedConclusion, replsMatchTable);
        astmgr.finishReplace(replacedConclusion);
        if (!this.expandNofreeFn(replacedConclusion, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule)) throw errorMsg + "结论中的附加条件无法满足";
        this.expandCanreplFn(replacedConclusion, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule);
        this.expandReplFn(replacedConclusion, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule);
        try { this.checkGrammer(replacedConclusion, "p"); } catch (e) { throw "结论中出现语法错误：" + e }
        // if it isn't macro or not inineMode, done
        let netInlineMode = inlineMode;
        if (typeof netInlineMode === "function") netInlineMode = netInlineMode(step, replacedConclusion);
        if (!steps?.length || !netInlineMode) {
            return this.propositions.push({ value: replacedConclusion, from: step }) - 1;
        }

        // if it is macro and inline, expand substeps 

        let startPropositions = this.propositions.length;
        let propsOffset = [];
        for (const [substepIdx, substep] of steps.entries()) {
            // if condition number is positive, use given macro condition props
            // if condition number is negative, this implies newly deducted props, which is relative to the end of prop list
            const replacedConditionIdxs = substep.conditionIdxs.map(idx => {
                if (idx >= 0) return conditionIdxs[idx];
                let newIdx = this.propositions.length + idx;
                for (let i = 0; i < -1 - idx; i++) {
                    newIdx -= propsOffset[i];
                }
                return newIdx;
            });
            const replaceValues = substep.replaceValues.map(ast => {
                const replaced = astmgr.clone(ast);
                astmgr.replaceByMatchResult(replaced, replsMatchTable);
                astmgr.finishReplace(replaced); //in replsMatchTable, there are $replvar typed vars
                return replaced;
            });
            let firstPos = this.propositions.length - 1;
            let lastPos: number;
            try {
                lastPos = this.deduct({ deductionIdx: substep.deductionIdx, replaceValues, conditionIdxs: replacedConditionIdxs }, netInlineMode === "deep" ? inlineMode : null);
            } catch (e) {
                // if one substep is wrong, remove newly added substeps from proplist
                const substepErrMsg = errorMsg + `子步骤中 ` + e;
                while (this.propositions.length > startPropositions) {
                    this.propositions.pop();
                }
                throw substepErrMsg;
            }
            propsOffset.unshift(lastPos - firstPos - 1);

        }
        const propLength = this.propositions.length;
        return propLength - 1;
    }
    private _reconstructNoFreeFn(ast: AST, nofreeVars: Set<string>) {
        if (!nofreeVars.size) {
            astmgr.assign(ast, ast.nodes[0]);
        } else {
            ast.nodes = [ast.nodes[0], ...Array.from(nofreeVars).map(v => ({ type: "replvar", name: v }))];
        }
    }
    private _isFreeIn(name: string, ast: AST, replNameRule: RegExp, localNameRule: RegExp, ignoreNameRule: RegExp) {
        if (ast.type === "replvar") {
            // a is free in a 
            // $0 is free in $0
            if (ast.name === name) return 1;
            // cannot decide a is free in $1
            // cannot decide $0 is free in $1
            // cannot decide $0 is free in a
            if (name.match(ignoreNameRule) || ast.name.match(ignoreNameRule)) return -1;
            if (name.match(localNameRule) || ast.name.match(localNameRule)) return -1;
            if (name.match(replNameRule) || ast.name.match(replNameRule)) return 0;
            // a is not free in b
            return -1;
        }
        if (ast.type === "fn" && ast.name === "#nf") {
            const subNofreeAsts = ast.nodes.slice(1);
            let subNofreeVars = new Set(subNofreeAsts.map(n => n.name));
            // a is not free in .(a)
            // $0 is not free in .($0)
            if (subNofreeVars.has(name)) return -1;
            const testSubAst = ast.nodes[0];
            if (testSubAst.type !== "replvar") throw "cannot reached";
            // is A free in B([^A]) => is A free in B
            return this._isFreeIn(name, testSubAst, replNameRule, localNameRule, ignoreNameRule);
        }
        if (ast.type === "sym" && (ast.name === "V" || ast.name === "E" || ast.name === "E!")) {
            let localVar = ast.nodes[0].name;
            // a is not free in Va:.
            if (name === localVar) return -1;
            // else: is a free in Vb:A => is a free in A
            let subAst = ast.nodes[1];
            return this._isFreeIn(name, subAst, replNameRule, localNameRule, ignoreNameRule);
        }
        if (ast.nodes?.length) {
            let res = -1;
            for (const n of ast.nodes) {
                // free + notsure + notfree => free
                // notsure + notfree => notsure
                // notfree + notfree => notfree
                res = Math.max(res, this._isFreeIn(name, n, replNameRule, localNameRule, ignoreNameRule));
                if (res === 1) return 1;
            }
            return res;
        }

    }
    private expandCanreplFn(ast: AST, replNameRule: RegExp, localNameRule: RegExp, ignoreNameRule: RegExp) {
        if (ast.type === "fn" && ast.name === "#canrepl") {
            const testAst = ast.nodes[0];
            const srcAst = ast.nodes[1];
            if (testAst.type === "fn" && testAst.name === "#canrepl") {
                this.expandCanreplFn(testAst, replNameRule, localNameRule, ignoreNameRule);
            }
            if (testAst.type === "fn" && testAst.name === "#canrepl") {
                // two layers of the same assertion, merge into one
                if (astmgr.equal(testAst.nodes[1], srcAst) && astmgr.equal(testAst.nodes[2], ast.nodes[2])) {
                    astmgr.assign(ast, testAst);
                }
                return;
            }
            const rawSrcAst = astmgr.clone(srcAst);
            const srcIsNot = new Set<string>;
            if (srcAst.type === "fn" && srcAst.name === "#nf") {
                for (let i = 1; i < srcAst.nodes.length; i++) {
                    srcIsNot.add(srcAst.nodes[i].name);
                }
            }
            this.getNetCondition(srcAst);
            if (srcAst.type !== "replvar") throw "#canrepl函数验证失败：只能替换变量，不能替换表达式";
            const src = srcAst.name;

            const dst2 = astmgr.clone(ast.nodes[2]);
            this.getNetCondition(dst2);
            if (dst2.type === "replvar" && dst2.name === src) {
                // #canrepl(.,A,A) -> .
                astmgr.assign(ast, testAst);
                return;
            }
            if (testAst.type === "replvar") {
                if (!testAst.name.match(replNameRule)) {
                    // #canrepl(a,.,.) -> a
                    astmgr.assign(ast, testAst);
                    return;
                }
                if (testAst.name === src) {
                    // #canrepl($0,$0(b),.) -> $0(b)
                    // #canrepl($0,$0,.) -> $0
                    astmgr.assign(ast, rawSrcAst);
                    return;
                }
                // else, noway to reduce it
                return;
            }
            if (testAst.type === "fn" && testAst.name === "#nf") {
                const subNofreeAsts = testAst.nodes.slice(1); // .map(n => (this.getNetCondition(n), n));
                let subNofreeVars = new Set(subNofreeAsts.map(n => n.name));
                if (subNofreeVars.has(src)) {
                    // #canrepl($0(a),a,.) -> $0(a)
                    // #canrepl($0($1),$1,.) -> $0($1)
                    astmgr.assign(ast, testAst);
                    return;
                }
                const testSubAst = testAst.nodes[0];
                if (testSubAst.type !== "replvar") throw "cannot reached";
                if (!testSubAst.name.match(replNameRule)) {
                    // #canrepl(a(.),.,.) -> a(.)
                    astmgr.assign(ast, testAst);
                    return;
                }
                if (testSubAst.name === src) {
                    // #canrepl($0(a),$0(b),.) -> $0(a,b)
                    // #canrepl($0(a),$0,.) -> $0(a)
                    srcIsNot.forEach(e => subNofreeVars.add(e));
                    this._reconstructNoFreeFn(testAst, subNofreeVars);
                    astmgr.assign(ast, testAst);
                    return;
                }
                // else, noway to reduce it
                return;
            }
            if (testAst.type === "sym" && (testAst.name === "V" || testAst.name === "E" || testAst.name === "E!")) {
                let localVar = testAst.nodes[0].name;
                let subAst = testAst.nodes[1];
                if (src === localVar) {
                    // #canrepl(Va:.,a,.) -> Va:.
                    astmgr.assign(ast, testAst); return;
                }
                // #canrepl(Va:A,b,B(a)) -> Va:#canrepl(A,b,B(a))
                const testRes = this._isFreeIn(localVar, ast.nodes[2], replNameRule, localNameRule, ignoreNameRule);
                if (testRes === 1) {
                    throw `#canrepl函数验证失败：原先自由的变量${src}替换后将被${localVar}约束`;
                }
                if (testRes === 0) {
                    // throw `原先自由的变量${src}替换后可能被${localVar}约束`;
                    // no way to reduce it
                    return;
                }
                const newSubAst = {
                    type: "fn", name: "#canrepl", nodes: [
                        subAst, rawSrcAst, ast.nodes[2]
                    ]
                };
                astmgr.assign(ast, {
                    type: "sym", name: testAst.name, nodes: [
                        testAst.nodes[0],
                        newSubAst
                    ]
                });
                return this.expandCanreplFn(ast, replNameRule, localNameRule, ignoreNameRule);
            }
            if (testAst.nodes?.length) {
                const newTestAst = {
                    type: testAst.type,
                    name: testAst.name,
                    nodes: []
                }
                for (const subAst of testAst.nodes) {
                    newTestAst.nodes.push({
                        type: "fn", name: "#canrepl",
                        nodes: [subAst, astmgr.clone(rawSrcAst), ast.nodes[2]]
                    });
                }
                astmgr.assign(ast, newTestAst);
                return this.expandCanreplFn(ast, replNameRule, localNameRule, ignoreNameRule);
            }
            throw "cannot reached";
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) this.expandCanreplFn(n, replNameRule, localNameRule, ignoreNameRule);
        }
    }
    private _execReplFn(ast: AST, name: string, dstAst: AST): boolean {
        if (dstAst.type === "replvar") {
            if (name === dstAst.name) return true;
        }
        if (ast.type === "replvar") {
            if (ast.name === name) {
                astmgr.assign(ast, dstAst);
                return true;
            }
            return !(ast.name.match(this.deductionReplNameRule) || name.match(this.deductionReplNameRule));

        }
        if (ast.type === "fn" && ast.name === "#canrepl") {
            // throw "cannot resolve #canrepl in #repl";
            return false;
        }
        if (ast.type === "fn" && ast.name === "#nf") {
            const subAst = ast.nodes[0];
            if (subAst.name === name) {
                astmgr.assign(ast, dstAst);
                return true;
            }
            return !(subAst.name.match(this.deductionReplNameRule) || name.match(this.deductionReplNameRule));
        }
        if (ast.type === "sym" && (ast.name === "V" || ast.name === "E" || ast.name === "E!")) {
            let localVar = ast.nodes[0].name;
            let subAst = ast.nodes[1];
            if (name === localVar) return true;
            return this._execReplFn(subAst, name, dstAst);
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) if (!this._execReplFn(n, name, dstAst)) return false;
        }
        return true;
    }
    private expandReplFn(ast: AST, replNameRule: RegExp, localNameRule: RegExp, ignoreNameRule: RegExp, replFnName: string = "#repl") {
        if (ast.type === "fn" && ast.name === replFnName) {
            const [testAst, srcAst, dstAst] = ast.nodes;
            // verify we can do #repl fn
            const newAst = { type: "fn", name: "#canrepl", nodes: ast.nodes.map(n => astmgr.clone(n)) };
            this.expandCanreplFn(newAst, replNameRule, localNameRule, ignoreNameRule);
            this.getNetCondition(srcAst);
            if (this._execReplFn(testAst, srcAst.name, dstAst)) {
                astmgr.assign(ast, testAst);
            }
            return;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) this.expandReplFn(n, replNameRule, localNameRule, ignoreNameRule, replFnName);
        }
    }
    private expandNofreeFn(ast: AST, replNameRule: RegExp, localNameRule: RegExp, ignoreNameRule: RegExp): boolean {
        if (ast.type === "fn" && ast.name === "#nf") {
            const nofreeAsts = ast.nodes.slice(1).map(n => (this.getNetCondition(n), n));
            let nofreeVars = new Set(nofreeAsts.map(n => n.name));
            const testAst = ast.nodes[0];
            if (testAst.type === "replvar") {
                // #nf($0,..$0..), fail 
                // #nf(a,..a..), fail 
                if (nofreeVars.has(testAst.name)) {
                    return false;
                }
                if (testAst.name.match(ignoreNameRule)) {
                    this._reconstructNoFreeFn(ast, new Set);
                    return true;
                }
                // else a!=b:
                // #nf(a,..b..), delete b
                if (!testAst.name.match(replNameRule)) {
                    nofreeVars.forEach(b => {
                        if (b.match(ignoreNameRule) || !b.match(replNameRule)) {
                            nofreeVars.delete(b);
                        }
                    });
                } else {
                    // local vars
                    // #nf($0,..#b..), delete #b
                    nofreeVars.forEach(b => {
                        if (b.match(ignoreNameRule) || b.match(localNameRule)) {
                            nofreeVars.delete(b);
                        }
                    });
                }
                this._reconstructNoFreeFn(ast, nofreeVars);
                return true;
            }
            if (testAst.type === "fn" && testAst.name === "#nf") {
                const subNofreeAsts = testAst.nodes.slice(1).map(n => (this.getNetCondition(n), n));
                let subNofreeVars = new Set(subNofreeAsts.map(n => n.name));
                nofreeVars.forEach(e => subNofreeVars.add(e));
                astmgr.assign(ast, testAst);
                this._reconstructNoFreeFn(ast, subNofreeVars);
                return this.expandNofreeFn(ast, replNameRule, localNameRule, ignoreNameRule);
            }
            if (testAst.type === "sym" && (testAst.name === "V" || testAst.name === "E" || testAst.name === "E!")) {
                let localVar = testAst.nodes[0].name;
                let subAst = testAst.nodes[1];
                // #nf(Va:xxx,a) -> true
                if (nofreeVars.has(localVar)) {
                    nofreeVars.delete(localVar);
                }
                const newSubAst = { type: "fn", name: "#nf", nodes: [testAst.nodes[1]] };
                this._reconstructNoFreeFn(newSubAst, nofreeVars);
                astmgr.assign(ast, {
                    type: "sym", name: testAst.name, nodes: [
                        testAst.nodes[0],
                        newSubAst
                    ]
                });
                return this.expandNofreeFn(ast, replNameRule, localNameRule, ignoreNameRule);
            }
            if (testAst.nodes?.length) {
                const newTestAst = {
                    type: testAst.type,
                    name: testAst.name,
                    nodes: []
                }
                for (const subAst of testAst.nodes) {
                    newTestAst.nodes.push({
                        type: "fn", name: "#nf",
                        nodes: [subAst, ...nofreeAsts.map(e => astmgr.clone(e))]
                    });
                }
                astmgr.assign(ast, newTestAst);
                return this.expandNofreeFn(ast, replNameRule, localNameRule, ignoreNameRule);
            }
            throw "cannot reached";
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) if (!this.expandNofreeFn(n, replNameRule, localNameRule, ignoreNameRule)) return false;
        }
        return true;
    }
    expandMacroWithProp(propositionIdx: number) {
        const p = this.propositions[propositionIdx];
        if (!p.from) throw "该定理为假设，无推理步骤可展开";
        const { deductionIdx, conditionIdxs, replaceValues } = p.from;
        if (!this.deductions[deductionIdx].steps) throw `该定理由来自<${this.deductions[deductionIdx].from}>的原子推理规则得到，无子步骤`;
        const hyps = conditionIdxs.map(c => this.propositions[c].value);
        this.removePropositions();
        hyps.forEach(h => this.addHypothese(h));
        this.deduct({
            deductionIdx, conditionIdxs: hyps.map((v, idx) => idx), replaceValues
        }, "inline");
    }
    expandMacroWithDefaultValue(deductionIdx: number) {
        const d = this.deductions[deductionIdx];
        if (!d) throw `推理规则${deductionIdx}不存在`;
        if (!d.steps) throw `无法展开原子推理规则`;
        this.removePropositions();
        d.conditions.forEach(dcond => this.addHypothese(dcond));
        this.deduct({
            deductionIdx, conditionIdxs: d.conditions.map((v, idx) => idx), replaceValues: d.replaceNames.map(str => str.includes("(") ?
                {
                    type: "fn", name: str.replace(/^(.+)\(.*\)$/g, "$1"),
                    nodes: str.replace(/^.+\((.*)\)$/g, "$1").split(",").map(e => ({
                        type: "replvar", name: e
                    }))
                }
                :
                {
                    type: "replvar", name: str
                })
        }, "inline");
    }
    metaDeductTheorem(deductionIdx: number) {
        const d = this.deductions[deductionIdx];
        const errorMsg = "演绎元定理执行失败：";
        if (!d) throw errorMsg + "条件中的推理规则不存在";
        if (!d.conditions.length) throw errorMsg + "推理规则不包含假设，无法与条件匹配";
        const oldPropositions = this.propositions;
        const oldHypothesisAmount = this.hypothesisAmount;

        try {

            // expand macro in propositions, store it in const refPropositions

            this.removePropositions();
            d.conditions.forEach(dcond => this.addHypothese(dcond));
            this.deduct({
                deductionIdx, conditionIdxs: d.conditions.map((v, idx) => idx), replaceValues: d.replaceNames.map(str => str.includes("(") ?
                    {
                        type: "fn", name: str.replace(/^(.+)\(.*\)$/g, "$1"),
                        nodes: str.replace(/^.+\((.*)\)$/g, "$1").split(",").map(e => ({
                            type: "replvar", name: e
                        }))
                    }
                    :
                    {
                        type: "replvar", name: str
                    })
            }, step => step.conditionIdxs.length ? "deep" : null);
            const refPropositions = this.propositions;

            // write required deduction step in current proposition list according to refsteps

            this.removePropositions();
            const newConditions = d.conditions.slice(0, -1);
            // const newNetCoditions = netConditions.slice(0, -1);
            newConditions.forEach(dcond => this.addHypothese(dcond));
            // refPropositions.forEach(p => p.from ? p.from = [p.from[p.from.length - 1]] : null);
            const HYP = 0, CND = 1, AXM = 2, DDT = 3;
            const infoTable = [];
            const offsetTable = [];
            for (const [pidx, p] of refPropositions.entries()) {
                const step = p.from;
                if (!step) {
                    if (pidx < this.hypothesisAmount) {
                        // hypothese, skip
                        infoTable.push(HYP);
                        offsetTable.push(pidx);
                    } else if (pidx === this.hypothesisAmount) {
                        // condition for moving
                        infoTable.push(CND);
                        offsetTable.push(NaN); // removed, access forbidden
                    } else {
                        throw "assertion failed";
                    }
                    continue;
                }
                if (!step.conditionIdxs?.length) {
                    infoTable.push(AXM);
                    offsetTable.push(this.propositions.length);
                    this.deduct(step); // axiom, copy it
                    continue;
                }
                if (step.deductionIdx === 0) {
                    // MP law: c0: $0>$1 c1: $0   |-   $1
                    const s0_s1Info = infoTable[step.conditionIdxs[0]];
                    const s0Info = infoTable[step.conditionIdxs[1]];
                    const s0_s1 = offsetTable[step.conditionIdxs[0]];
                    const s0 = offsetTable[step.conditionIdxs[1]];
                    const s0_s1IsTrue = (s0_s1Info & 1) === 0;
                    const s0IsTrue = (s0Info & 1) === 0;
                    const s1Ast = p.value;
                    if (s0_s1IsTrue && s0IsTrue) {
                        // $0>$1, $0 |- $1 (d0)
                        infoTable.push(AXM);
                        offsetTable.push(this.deduct({
                            conditionIdxs: [s0_s1, s0],
                            deductionIdx: 0, replaceValues: []
                        })); continue;
                    }
                    if (s0_s1IsTrue && s0Info === CND) {
                        // CND > $1 |- CND > $1 , only mark it
                        offsetTable.push(s0_s1);
                        infoTable.push(DDT); continue;
                    }
                    if (s0_s1IsTrue && s0Info === DDT) {
                        // $0 > $1, CND > $0 |- CND > $1
                        infoTable.push(DDT);
                        offsetTable.push(this.deduct({
                            conditionIdxs: [s0, s0_s1],
                            deductionIdx: 93, replaceValues: []
                        }));
                        continue;
                    }
                    if (s0_s1Info === CND && s0IsTrue) {
                        // $0 |- ($0>$1)>$1
                        infoTable.push(DDT);
                        offsetTable.push(this.deduct({
                            conditionIdxs: [s0],
                            deductionIdx: 94, replaceValues: [s1Ast]
                        }));
                        continue;
                    }
                    if (s0_s1Info === CND && s0Info === DDT) {
                        // ($0>$1) > $0 |- ($0>$1) > $1
                        infoTable.push(DDT);
                        offsetTable.push(this.deduct({
                            conditionIdxs: [s0],
                            deductionIdx: 95, replaceValues: []
                        }));
                        continue;
                    }
                    if (s0_s1Info === CND && s0Info === CND) {
                        // s0 > s1  can't be  s0
                        throw "assertion failed";
                    }
                    if (s0_s1Info === DDT && s0IsTrue) {
                        // cnd > ($0 > $1), $0 |- cnd > $1
                        infoTable.push(DDT);
                        offsetTable.push(this.deduct({
                            conditionIdxs: [s0_s1, s0],
                            deductionIdx: 96, replaceValues: []
                        }));
                        continue;
                    }
                    if (s0_s1Info === DDT && s0Info === CND) {
                        // $0 > ($0 > $1) |- $0 > $1
                        infoTable.push(DDT);
                        offsetTable.push(this.deduct({
                            conditionIdxs: [s0_s1],
                            deductionIdx: 97, replaceValues: []
                        }));
                        continue;
                    }
                    if (s0_s1Info === DDT && s0Info === DDT) {
                        // cnd > ($0>$1), cnd > $0  |- cnd > $1
                        infoTable.push(DDT);
                        offsetTable.push(this.deduct({
                            conditionIdxs: [s0_s1, s0],
                            deductionIdx: 98, replaceValues: []
                        }));
                        continue;
                    }
                }
            }
            const lastInfo = infoTable.pop();
            const lastP = offsetTable.pop();

            if (lastInfo === HYP) throw "结论为假设";
            if (lastInfo === CND) throw "结论为假设";
            if (lastInfo === AXM) {
                this.deduct({
                    conditionIdxs: [],
                    deductionIdx: 1, replaceValues: [
                        this.propositions[lastP].value,
                        refPropositions[this.hypothesisAmount].value
                    ]
                });
                this.deduct({
                    conditionIdxs: [lastP + 1, lastP],
                    deductionIdx: 0, replaceValues: []
                });
            }
            while (this.propositions.length > 1 && astmgr.equal(
                this.propositions[this.propositions.length - 1].value,
                this.propositions[this.propositions.length - 2].value
            )) {
                this.removePropositions(1);
            }

            // add deduction as macro and recover proposition list

            const didx = this.addMacro(this.propositions.length - 1, "mdt " + deductionIdx);
            this.propositions = oldPropositions;
            this.hypothesisAmount = oldHypothesisAmount;
            return didx;
        } catch (e) {
            this.propositions = oldPropositions;
            this.hypothesisAmount = oldHypothesisAmount;
            throw e;
        }
    }
    metaQuantifyAxiomSchema(deductionIdx: number, replaceValue: AST) {
        const d = this.deductions[deductionIdx];
        if (d.conditions?.length) throw "无法匹配带条件的推理规则";
        if (d.steps?.length) throw "无法匹配非公理推理规则";
        const didx = this.addDeduction({
            type: "meta", name: "⊢",
            nodes: [
                { type: "fn", name: "#array", nodes: [] },
                {
                    type: "fn", name: "#array", nodes: [
                        {
                            type: "sym", name: "V", nodes: [
                                replaceValue,
                                d.conclusion
                            ]
                        }
                    ]
                },
            ]
        }, "mq " + deductionIdx);
        return didx;
    }
    metaNewConstant(replaceValues: AST[]) {
        const [constAst, varAst, exprAst] = replaceValues;
        if (constAst.type !== "replvar") throw "$$0只能为纯变量名";
        if (constAst.name.startsWith("$")) throw "以$开头的变量名称被系统保留";
        if (constAst.name.startsWith("#")) throw "以#开头的变量名称被系统保留";
        const constCheckRes = this.isNameCanBeNewConst(constAst.name);
        if (constCheckRes !== true) throw "匹配条件##newconst($$0)时：" + constCheckRes;
        const deduction = astmgr.clone(this.metaRules["c"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": constAst,
            "$$1": varAst,
            "$$2": exprAst
        }
        astmgr.replaceByMatchResult(deduction, replTable);
        this.expandReplFn(deduction, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule, "##repl");
        this.consts.set(constAst.name, this.deductions.length);
        return this.addDeduction(deduction, "mc '" + constAst.name + "'");
    }
    metaUniversalTheorem(deductionIdx: number, replaceValue: AST) {
        const didxVaMP = 99;
        const d = this.deductions[deductionIdx];
        const errorMsg = "普遍化元定理执行失败：";
        if (!d) throw errorMsg + "条件中的推理规则不存在";
        if (replaceValue.type !== "replvar") throw "$$0只能为变量";
        const variable = replaceValue.name;
        if (this.consts.has(variable)) throw "$$0不能为常量";
        for (const [idx, cond] of d.conditions.entries()) {
            if (-1 !== this._isFreeIn(variable, cond, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule)) {
                throw errorMsg + `条件${idx + 1}中##nofree函数无法满足`;
            }
        }


        const oldTempMQDs = this.tempMQDs;
        const oldPropositions = this.propositions;
        const oldDeductions = this.deductions;
        const oldHypothesisAmount = this.hypothesisAmount;

        try {

            // expand macro in propositions, store it in const refPropositions

            this.removePropositions();
            d.conditions.forEach(dcond => this.addHypothese(dcond));
            this.deduct({
                deductionIdx, conditionIdxs: d.conditions.map((v, idx) => idx), replaceValues: d.replaceNames.map(str => str.includes("(") ?
                    {
                        type: "fn", name: str.replace(/^(.+)\(.*\)$/g, "$1"),
                        nodes: str.replace(/^.+\((.*)\)$/g, "$1").split(",").map(e => ({
                            type: "replvar", name: e
                        }))
                    }
                    :
                    {
                        type: "replvar", name: str
                    })
            }, (step, conclusion) => (-1 !== this._isFreeIn(variable, conclusion, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule) ? "deep" : null));
            const refPropositions = this.propositions;

            // write required deduction step in current proposition list according to refsteps

            this.removePropositions();
            d.conditions.forEach(dcond => this.addHypothese(dcond));

            const NOFREE = 1, AXM = 2, MP = 3;
            const infoTable = [];
            const newTable = [];
            const offsetVarTable = []; // with V:
            const offsetTable = []; // without V:
            for (const [pidx, p] of refPropositions.entries()) {
                const step = p.from;
                if (!step) {
                    infoTable.push(NOFREE); // already checked hypotheses satisfy nf
                    offsetTable.push(pidx);
                    continue;
                }
                if (-1 === this._isFreeIn(variable, p.value, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule)) {
                    infoTable.push(NOFREE);
                    continue;
                }
                if (step.deductionIdx === 0) {
                    infoTable.push(MP);
                    continue;
                }
                if (!this.deductions[step.deductionIdx].steps?.length) {
                    infoTable.push(AXM);
                    continue;
                }
                throw "cannot reached";
            }
            const generate = (idx: number, quantified: boolean) => {
                const oldStep = refPropositions[idx].from;
                const didx = oldStep?.deductionIdx;
                if (!quantified) {
                    // avoid repeated deductions on the same prop (here includes hyps)
                    if (isFinite(offsetTable[idx])) return offsetTable[idx];
                    // axiom or macros
                    offsetTable[idx] = this.deduct({
                        deductionIdx: didx, replaceValues: oldStep.replaceValues,
                        conditionIdxs: oldStep.conditionIdxs.map(id => generate(id, false))
                    });
                    return offsetTable[idx];
                }
                // avoid repeated deductions on the same prop
                if (isFinite(offsetVarTable[idx])) return offsetVarTable[idx];
                let targetInfo = infoTable[idx];
                if (targetInfo === NOFREE) {
                    const id0 = this.deduct({ deductionIdx: 6, conditionIdxs: [], replaceValues: [replaceValue, refPropositions[idx].value] });
                    const id = this.deduct({ deductionIdx: 0, conditionIdxs: [id0, generate(idx, false)], replaceValues: [] });
                    offsetVarTable[idx] = id;
                    return id;
                }
                if (targetInfo === AXM) {
                    const newVariable = "$&" + didx;
                    const newdIdx = this.tempMQDs[didx] ?? this.metaQuantifyAxiomSchema(didx, { type: "replvar", name: newVariable });
                    this.tempMQDs[didx] = newdIdx;
                    const oldd = this.deductions[didx];
                    const newd = this.deductions[newdIdx];
                    const newReplaceValues = new Array(newd.replaceNames.length);
                    for (const [nidx, name] of oldd.replaceNames.entries()) {
                        newReplaceValues[newd.replaceNames.indexOf(name)] = refPropositions[idx].from.replaceValues[nidx];
                    }
                    const variableReplaceValuesIdx = newd.replaceNames.indexOf(newVariable);
                    newReplaceValues[variableReplaceValuesIdx] = replaceValue;
                    const id = this.deduct({
                        deductionIdx: newdIdx, conditionIdxs: [], replaceValues: newReplaceValues
                    });
                    offsetVarTable[idx] = id;
                    return id;
                }
                if (targetInfo === MP) {
                    const id = this.deduct({
                        deductionIdx: didxVaMP, replaceValues: [], conditionIdxs: [
                            generate(oldStep.conditionIdxs[0], true),
                            generate(oldStep.conditionIdxs[1], true),
                        ]
                    });
                    offsetVarTable[idx] = id;
                    return id;
                }
            }
            generate(infoTable.length - 1, true);

            // add deduction as macro and recover proposition list

            const didx = this.addMacro(this.propositions.length - 1, "mqt " + deductionIdx);
            this.propositions = oldPropositions;
            this.hypothesisAmount = oldHypothesisAmount;
            return didx;
        } catch (e) {
            this.tempMQDs = oldTempMQDs;
            this.deductions = oldDeductions; // no risk here because no const/fn added
            this.hypothesisAmount = oldHypothesisAmount;
            this.propositions = oldPropositions; // no risk here because we have updated hypothesisAmount by hand
            throw e;
        }
    }
    metaNewFunction(replaceValues: AST[]) {
        const [fnAst, varAst1, varAst2, exprAst] = replaceValues;
        if (fnAst.type !== "replvar") throw "$$0只能为纯变量名";
        if (fnAst.name.startsWith("#")) throw "以#开头的函数被系统保留";
        if (fnAst.name.startsWith("$")) throw "以$开头的函数被系统保留";
        const fnCheckRes = this.fns.has(fnAst.name);
        if (fnCheckRes) throw `匹配条件##newfn($$0)时：函数已于d${this.fns.get(fnAst.name)}中定义`;
        const deduction = astmgr.clone(this.metaRules["f"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": fnAst,
            "$$1": varAst1,
            "$$2": varAst2,
            "$$3": exprAst
        }
        astmgr.replaceByMatchResult(deduction, replTable);
        this._replaceFnName(deduction, "$$0", fnAst.name);
        this.expandReplFn(deduction, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule, "##repl");
        this.fns.set(fnAst.name, this.deductions.length);
        return this.addDeduction(deduction, "mf '" + fnAst.name + "(#0)'");
    }
    _replaceFnName(ast: AST, src: string, dst: string) {
        if (ast.type === "fn" && ast.name === src) {
            ast.name = dst;
            return;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this._replaceFnName(n, src, dst);
            }
        }
    }
}