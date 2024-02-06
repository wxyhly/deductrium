import { ASTMgr } from "./astmgr.js";
const astmgr = new ASTMgr;
export class FormalSystem {
    hypothesisAmount = 0;
    deductions = [];
    metaRules = [];
    deductionReplNameRule = /^\$/g;
    fnParamNames = (n) => "#" + n;
    propositions = [];
    ast2deduction(ast) {
        let grammarCheck = ast.type === "meta" && ast.name === "⊢" && ast.nodes?.length === 2;
        if (!grammarCheck)
            throw "未找到推理符号";
        const [conditions, conclusions] = ast.nodes;
        if (conclusions.nodes?.length !== 1)
            throw "推理符号后面的结论数量必须为1";
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
    ast2metaRule(ast) {
        let grammarCheck = ast.type === "meta" && ast.name === "⊢M" && ast.nodes?.length === 2;
        if (!grammarCheck)
            throw "未找到元推理符号";
        const [conditions, conclusions] = ast.nodes;
        if (!conclusions.nodes?.length)
            throw "元推理符号后面没有结论";
        return {
            value: ast,
            conclusions: conclusions.nodes,
            conditions: conditions.nodes,
            replaceNames: [],
            from: ""
        };
    }
    getNetCondition(condition) {
        if (condition.type === "fn" && condition.name === "#nofree") {
            astmgr.assign(condition, condition.nodes[0]);
            this.getNetCondition(condition);
        }
        else if (condition.nodes?.length) {
            for (const n of condition.nodes)
                this.getNetCondition(n);
        }
    }
    getReplNames(ast) {
        const replNames = new Set;
        if (ast.name.match(this.deductionReplNameRule)) {
            if (ast.type === "fn") {
                replNames.add(ast.name + `(${ast.nodes.map((v, idx) => this.fnParamNames(idx)).join(",")})`);
                for (const n of ast.nodes)
                    this.getReplNames(n).forEach(v => replNames.add(v));
                return replNames;
            }
            replNames.add(ast.name);
            return replNames;
        }
        if (ast.nodes)
            for (const n of ast.nodes)
                this.getReplNames(n).forEach(v => replNames.add(v));
        return replNames;
    }
    getAllReplNames(asts) {
        const replNames = new Set;
        for (const ast of asts) {
            this.getReplNames(ast).forEach(str => replNames.add(str));
        }
        return replNames;
    }
    addDeduction(d, from, macro) {
        const deduction = this.ast2deduction(d);
        deduction.from = from;
        deduction.steps = macro;
        return this.deductions.push(deduction) - 1;
    }
    addMetaRule(m, from) {
        const metaRule = this.ast2metaRule(m);
        metaRule.from = from;
        // this.calculateMetaRuleReplaceValues(metaRule);
        this.metaRules.push(metaRule);
    }
    addHypothese(m) {
        if (this.hypothesisAmount !== this.propositions.length)
            return false;
        if (!this.expandNofreeFn(m, this.deductionReplNameRule))
            throw "假设中的附加条件自相矛盾";
        this.propositions.push({ value: m, from: [] });
        this.hypothesisAmount++;
    }
    addMacro(propositionIdx) {
        if (propositionIdx < this.hypothesisAmount)
            throw "无有效定理推导步骤，创建宏推导失败";
        const conditions = [];
        for (let i = 0; i < this.hypothesisAmount; i++) {
            conditions.push(this.propositions[i].value);
        }
        const conclusion = this.propositions[propositionIdx].value;
        const macro = [];
        for (let i = this.hypothesisAmount, cursor = i; i <= propositionIdx; i++) {
            const stepStack = this.propositions[i].from;
            const step = stepStack[0];
            if (step.isSubstep)
                continue;
            macro.push({
                conditionIdxs: step.conditionIdxs.map(cidx => cidx < this.hypothesisAmount ? cidx : cidx - cursor),
                replaceValues: step.replaceValues,
                deductionIdx: step.deductionIdx
            });
            cursor = i + 1;
        }
        return this.addDeduction({
            type: "meta", name: "⊢", nodes: [
                { type: "fn", name: "#array", nodes: conditions },
                { type: "fn", name: "#array", nodes: [conclusion] },
            ]
        }, "", macro);
    }
    getMacroLayers(stepStack) {
        for (let i = 0; i < stepStack.length; i++) {
            if (!stepStack[i].isSubstep)
                return i;
        }
        return 0;
    }
    removePropositions(amount) {
        if (!isFinite(amount)) {
            this.propositions = [];
            this.hypothesisAmount = 0;
        }
        else {
            while (amount--) {
                this.propositions.pop();
            }
            this.hypothesisAmount = Math.min(this.propositions.length, this.hypothesisAmount);
        }
    }
    deduct(step, inlineMode) {
        const { conditionIdxs, deductionIdx, replaceValues } = step;
        const deduction = this.deductions[deductionIdx];
        const { conditions, conclusion, replaceNames, steps, netConditions } = deduction;
        const errorMsg = `d${deductionIdx} 推理失败: `;
        replaceValues.forEach((ast, idx) => {
            if (!this.expandNofreeFn(ast, this.deductionReplNameRule)) {
                throw `替代${replaceNames[idx]}的表达式中的附加条件自相矛盾`;
            }
        });
        // find repls provided by user, replfns must be by user
        let replsMatchTable = Object.fromEntries(replaceNames.map((replname, idx) => [replname, replaceValues[idx]]));
        // then match given condition props with net condition (with #nofree peeled)
        for (const [conditionIdx, condition] of conditions.entries()) {
            const condPropIdx = conditionIdxs[conditionIdx];
            const condProp = this.propositions[condPropIdx];
            if (!condProp)
                throw errorMsg + `第${conditionIdx + 1}个条件对应的定理p${condPropIdx}不存在`;
            // before matching, expand user defined fns in net condition
            const expandedNetCondition = astmgr.clone(netConditions[conditionIdx]);
            astmgr.expandReplFn(expandedNetCondition, this.fnParamNames, replsMatchTable);
            replsMatchTable = astmgr.mergeMatchResults(replsMatchTable, astmgr.match(condProp.value, expandedNetCondition, this.deductionReplNameRule));
            if (!replsMatchTable)
                throw errorMsg + `无法匹配第${conditionIdx + 1}个条件`;
        }
        // replace replvars in conditions, test and expand #nofree
        for (const [conditionIdx, condition] of conditions.entries()) {
            const condPropIdx = conditionIdxs[conditionIdx];
            const condProp = this.propositions[condPropIdx];
            const replacedCondition = astmgr.clone(condition);
            astmgr.expandReplFn(replacedCondition, this.fnParamNames, replsMatchTable);
            astmgr.replaceByMatchResult(replacedCondition, replsMatchTable);
            if (!this.expandNofreeFn(replacedCondition, this.deductionReplNameRule))
                throw errorMsg + `第${conditionIdx + 1}个条件中的附加条件无法满足`;
            if (!astmgr.equal(replacedCondition, condProp.value))
                throw errorMsg + `第${conditionIdx + 1}个条件中的附加条件无法满足`;
        }
        let replacedConclusion = astmgr.clone(conclusion);
        astmgr.expandReplFn(replacedConclusion, this.fnParamNames, replsMatchTable);
        astmgr.replaceByMatchResult(replacedConclusion, replsMatchTable);
        if (!this.expandNofreeFn(replacedConclusion, this.deductionReplNameRule))
            throw errorMsg + "结论中的附加条件无法满足";
        // if it isn't macro, done
        if (!steps?.length || inlineMode) {
            return this.propositions.push({ value: replacedConclusion, from: [step] }) - 1;
        }
        // if it is macro verify substeps 
        let startPropositions = this.propositions.length;
        for (const substep of steps) {
            // if condition number is positive, use given macro condition props
            // if condition number is negative, this implies newly deducted props, which is relative to the end of prop list
            const replacedConditionIdxs = substep.conditionIdxs.map(idx => idx >= 0 ? conditionIdxs[idx] : this.propositions.length + idx);
            const replaceValues = substep.replaceValues.map(ast => {
                const replaced = astmgr.clone(ast);
                astmgr.replaceByMatchResult(replaced, replsMatchTable);
                return replaced;
            });
            try {
                this.deduct({ deductionIdx: substep.deductionIdx, replaceValues, conditionIdxs: replacedConditionIdxs });
            }
            catch (e) {
                // if one substep is wrong, remove newly added substeps from proplist
                const substepErrMsg = errorMsg + `子步骤中 ` + e;
                while (this.propositions.length > startPropositions) {
                    this.propositions.pop();
                }
                throw substepErrMsg;
            }
        }
        // mark macro layer
        const propLength = this.propositions.length;
        const stepMarkedSub = {
            conditionIdxs: step.conditionIdxs, deductionIdx: step.deductionIdx, replaceValues: step.replaceValues,
            isSubstep: true
        };
        for (let idx = startPropositions; idx < propLength; idx++) {
            this.propositions[idx].from.unshift(idx === propLength - 1 ? step : stepMarkedSub);
        }
        return propLength - 1;
    }
    _reconstructNoFreeFn(ast, nofreeVars) {
        if (!nofreeVars.size) {
            astmgr.assign(ast, ast.nodes[0]);
        }
        else {
            ast.nodes = [ast.nodes[0], ...Array.from(nofreeVars).map(v => ({ type: "replvar", name: v }))];
        }
    }
    expandNofreeFn(ast, replNameRule) {
        if (ast.type === "fn" && ast.name === "#nofree") {
            const nofreeAsts = ast.nodes.slice(1).map(n => (this.getNetCondition(n), n));
            let nofreeVars = new Set(nofreeAsts.map(n => n.name));
            const testAst = ast.nodes[0];
            if (testAst.type === "replvar") {
                // #nofree($0,..$0..), fail 
                // #nofree(a,..a..), fail 
                if (nofreeVars.has(testAst.name)) {
                    return false;
                }
                // else a!=b:
                // #nofree(a,..b..), delete b
                if (!testAst.name.match(replNameRule)) {
                    nofreeVars.forEach(b => {
                        if (!b.match(replNameRule)) {
                            nofreeVars.delete(b);
                        }
                    });
                }
                this._reconstructNoFreeFn(ast, nofreeVars);
                return true;
            }
            if (testAst.type === "fn" && testAst.name === "#nofree") {
                const subNofreeAsts = testAst.nodes.slice(1).map(n => (this.getNetCondition(n), n));
                let subNofreeVars = new Set(subNofreeAsts.map(n => n.name));
                nofreeVars.forEach(e => subNofreeVars.add(e));
                astmgr.assign(ast, testAst);
                this._reconstructNoFreeFn(ast, subNofreeVars);
                return this.expandNofreeFn(ast, replNameRule);
            }
            if (testAst.type === "sym" && (testAst.name === "V" || testAst.name === "E" || testAst.name === "E!")) {
                let localVar = testAst.nodes[0].name;
                let subAst = testAst.nodes[1];
                // #nofree(Va:xxx,a) -> true
                if (nofreeVars.has(localVar)) {
                    nofreeVars.delete(localVar);
                }
                const newSubAst = { type: "fn", name: "#nofree", nodes: [testAst.nodes[1]] };
                this._reconstructNoFreeFn(newSubAst, nofreeVars);
                astmgr.assign(ast, {
                    type: "sym", name: testAst.name, nodes: [
                        testAst.nodes[0],
                        newSubAst
                    ]
                });
                return this.expandNofreeFn(ast, replNameRule);
            }
            if (testAst.nodes?.length) {
                const newTestAst = {
                    type: testAst.type,
                    name: testAst.name,
                    nodes: []
                };
                for (const subAst of testAst.nodes) {
                    newTestAst.nodes.push({
                        type: "fn", name: "#nofree",
                        nodes: [subAst, ...nofreeAsts.map(e => astmgr.clone(e))]
                    });
                }
                astmgr.assign(ast, newTestAst);
                return this.expandNofreeFn(ast);
            }
            throw "cannot reached";
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes)
                if (!this.expandNofreeFn(n, replNameRule))
                    return false;
        }
        return true;
    }
    metaDeduct0(deductionIdx) {
        const d = this.deductions[deductionIdx];
        const errorMsg = "m0 元推理失败：";
        if (!d)
            throw errorMsg + "条件中的推理规则不存在";
        if (!d.conditions.length)
            throw errorMsg + "推理规则不包含假设，无法与条件匹配";
        const oldPropositions = this.propositions;
        const oldHypothesisAmount = this.hypothesisAmount;
        // 假设中的函数设为同名函数，会不会发生递归？？
        // const netConditions = d.conditions.map(dc => this.getNetCondition(dc, {}));
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
            });
            const refPropositions = this.propositions;
            // write required deduction step in current proposition list according to refsteps
            this.removePropositions();
            const newConditions = d.conditions.slice(0, -1);
            // const newNetCoditions = netConditions.slice(0, -1);
            newConditions.forEach(dcond => this.addHypothese(dcond));
            refPropositions.forEach(p => p.from ? p.from = [p.from[p.from.length - 1]] : null);
            const HYP = 0, CND = 1, AXM = 2, DDT = 3;
            const infoTable = [];
            const offsetTable = [];
            for (const [pidx, p] of refPropositions.entries()) {
                const step = p.from[0];
                if (!step) {
                    if (pidx < this.hypothesisAmount) {
                        // hypothese, skip
                        infoTable.push(HYP);
                        offsetTable.push(pidx);
                    }
                    else if (pidx === this.hypothesisAmount) {
                        // condition for moving
                        infoTable.push(CND);
                        offsetTable.push(NaN); // removed, access forbidden
                    }
                    else {
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
                        }));
                        continue;
                    }
                    if (s0_s1IsTrue && s0Info === CND) {
                        // CND > $1 |- CND > $1 , only mark it
                        offsetTable.push(s0_s1);
                        infoTable.push(DDT);
                        continue;
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
                if (step.deductionIdx === 7) {
                    const s0Info = infoTable[step.conditionIdxs[0]];
                    const s0 = offsetTable[step.conditionIdxs[0]];
                    const s1Ast = p.value.nodes[0];
                    const s0IsTrue = (s0Info & 1) === 0;
                    if (s0IsTrue) {
                        infoTable.push(AXM);
                        offsetTable.push(this.propositions.length);
                        this.deduct({
                            deductionIdx: 7, conditionIdxs: [s0],
                            replaceValues: [s1Ast]
                        }); // axiom, copy it
                        continue;
                    }
                    else {
                        const s0Ast = p.value.nodes[1];
                        // |- $0 > V$1:$0
                        const p1 = this.deduct({
                            deductionIdx: 99, conditionIdxs: [],
                            replaceValues: [s0Ast, s1Ast]
                        });
                        if (s0Info === CND) {
                            // |- CND > V$1:CND, only mark it
                            offsetTable.push(p1);
                            infoTable.push(DDT);
                            continue;
                        }
                        else {
                            //  CND >  $0 , $0 > V$1:$0 |- CND > V$1:$0
                            offsetTable.push(this.deduct({
                                deductionIdx: 93, conditionIdxs: [s0, p1],
                                replaceValues: [s0Ast, s1Ast]
                            }));
                            infoTable.push(DDT);
                            continue;
                        }
                    }
                }
            }
            const lastInfo = infoTable.pop();
            const lastP = offsetTable.pop();
            if (lastInfo === HYP)
                throw "结论为假设";
            if (lastInfo === CND)
                throw "结论为假设";
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
            // add deduction as macro and recover proposition list
            const didx = this.addMacro(this.propositions.length - 1);
            this.propositions = oldPropositions;
            this.hypothesisAmount = oldHypothesisAmount;
            return didx;
        }
        catch (e) {
            this.propositions = oldPropositions;
            this.hypothesisAmount = oldHypothesisAmount;
            throw e;
        }
    }
}
//# sourceMappingURL=formalsystem.js.map