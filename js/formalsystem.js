import { ASTMgr } from "./astmgr.js";
import { AssertionSystem } from "./assertion.js";
const astmgr = new ASTMgr;
const assert = new AssertionSystem;
export class FormalSystem {
    deductions = {};
    metaRules = {};
    deductionReplNameRule = /^\$/g;
    localNameRule = /^\#/g;
    replacedLocalNameRule = /^&/g;
    ignoreNfNameRule = /^(&|#)/g;
    consts = new Set(); // [constName -> defineDeductionIdx]
    fns = new Set(); // [fnName -> defineDeductionIdx]
    fnParamNames = (n) => "#" + n;
    propositions = [];
    ast2deduction(ast) {
        assert.checkGrammer(ast, "d", this.consts);
        const [conditions, conclusions] = ast.nodes;
        const varLists = {};
        const allReplvars = new Set;
        const matchingReplvars = new Set;
        const netConditions = conditions.nodes.map(c => {
            assert.getReplVarsType(c, varLists, false);
            astmgr.getVarNames(c, allReplvars, /^\$/);
            const netC = astmgr.clone(c);
            assert.unwrapAssertions(netC);
            astmgr.getVarNames(netC, matchingReplvars, /^\$/);
            return netC;
        });
        assert.getReplVarsType(conclusions.nodes[0], varLists, false);
        astmgr.getVarNames(conclusions, allReplvars, /^\$/);
        return {
            value: ast,
            conclusion: conclusions.nodes[0],
            conditions: conditions.nodes,
            replaceNames: Array.from(allReplvars).filter(e => !matchingReplvars.has(e)),
            replaceTypes: varLists,
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
            replaceNames: [], conditionDeductionIdxs: [],
            from: ""
        };
    }
    removeDeduction(name) {
        if (!this.deductions[name])
            throw "规则名称 " + name + " 不存在";
        // if (this.deductions[name].from.match(/$/)) throw "无法删除系统规则";
        for (const [n, d] of Object.entries(this.deductions)) {
            if (!d.steps)
                continue;
            if (name === n)
                continue;
            for (const s of d.steps) {
                if (name === s.deductionIdx) {
                    throw "无法删除规则 " + name + "，请先删除对其有依赖的规则 " + n;
                }
            }
        }
        for (const [n, p] of this.propositions.entries()) {
            if (name === p.from?.deductionIdx) {
                throw "无法删除规则 " + name + "，请先删除对其有依赖的定理 p" + n;
            }
        }
        let res = (this.deductions[name].from.match(/^dc\((.+)\)$/g));
        if (res && res[1]) {
            if (!this.consts.delete(res[1]))
                throw "删除了不存在的常量的定义公理 " + name;
        }
        res = (this.deductions[name].from.match(/^df\((.+)\)$/g));
        if (res && res[1]) {
            if (!this.fns.delete(res[1]))
                throw "删除了不存在的函数的定义公理 " + name;
        }
        delete this.deductions[name];
        return true;
    }
    addDeduction(name, d, from, macro) {
        const deduction = this.ast2deduction(d);
        deduction.from = from;
        deduction.steps = macro;
        if (this.deductions[name])
            throw "规则名称 " + name + " 已存在";
        this.deductions[name] = deduction;
        return name;
    }
    addMetaRule(name, m, conditionDeductionIdxs, replaceNames, from) {
        const metaRule = this.ast2metaRule(m);
        metaRule.from = from;
        metaRule.conditionDeductionIdxs = conditionDeductionIdxs;
        metaRule.replaceNames = replaceNames;
        this.metaRules[name] = metaRule;
    }
    addHypothese(m, expandMode) {
        m = astmgr.clone(m);
        assert.checkGrammer(m, "p", this.consts);
        if (this.propositions.findIndex(e => e.from) !== -1)
            throw "无法添加假设条件：假设须添加在其它定理之前";
        if (!expandMode && this._hasLocalNames(m))
            throw "假设中不能出现以#号开头的局部变量";
        try {
            assert.expand(m, false);
        }
        catch (e) {
            throw "假设中" + e;
        }
        return this.propositions.push({ value: m, from: null }) - 1;
    }
    // find #0 in ast
    _hasLocalNames(ast) {
        if (ast.type === "replvar" && ast.name.match(this.localNameRule)) {
            return true;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                if (this._hasLocalNames(n))
                    return true;
            }
        }
        return false;
    }
    addMacro(name, from) {
        const propositionIdx = this.propositions.length - 1;
        let hypothesisAmount = this.propositions.findIndex(e => e.from);
        if (hypothesisAmount == -1)
            hypothesisAmount = this.propositions.length;
        if (propositionIdx < hypothesisAmount)
            throw "无有效定理推导步骤，创建宏推导失败";
        const conditions = [];
        for (let i = 0; i < hypothesisAmount; i++) {
            conditions.push(this.propositions[i].value);
        }
        const conclusion = this.propositions[propositionIdx].value;
        if (this._hasLocalNames(conclusion)) {
            throw "局部变量不能出现在推理宏的结论中";
        }
        const macro = [];
        for (let i = hypothesisAmount; i <= propositionIdx; i++) {
            const step = this.propositions[i].from;
            macro.push({
                conditionIdxs: step.conditionIdxs.map(cidx => cidx < hypothesisAmount ? cidx : cidx - i),
                replaceValues: step.replaceValues.map(v => {
                    const newv = astmgr.clone(v);
                    // replace #0 to name&0
                    astmgr.replaceVarNamesInAst(newv, this.localNameRule, /^#(.+)$/, name + "&$1");
                    return newv;
                }),
                deductionIdx: step.deductionIdx
            });
        }
        return this.addDeduction(name, {
            type: "meta", name: "⊢", nodes: [
                { type: "fn", name: "#array", nodes: conditions },
                { type: "fn", name: "#array", nodes: [conclusion] },
            ]
        }, from, macro);
    }
    removePropositions(amount) {
        if (!isFinite(amount)) {
            this.propositions = [];
        }
        else {
            while (amount--) {
                this.propositions.pop();
            }
        }
    }
    isNameCanBeNewConst(name) {
        if (this.consts.has(name))
            return `"${name}" 已有定义，无法重复定义`;
        for (const [idx, d] of Object.entries(this.deductions)) {
            if (assert.isNameQuantVarIn(name, d.value))
                return `"${name}" 已作为量词中的约束变量出现在了规则${idx}中，无法定义为常量符号`;
        }
        for (const [idx, p] of this.propositions.entries()) {
            if (assert.isNameQuantVarIn(name, p.value))
                return `"${name}" 已作为量词中的约束变量出现在了p${idx}中，无法定义为常量符号`;
        }
        return true;
    }
    generateDeduction(name) {
        if (this.deductions[name])
            return this.deductions[name];
        const d1name = name?.slice(1);
        if (!d1name)
            return null;
        const d1 = this.generateDeduction(d1name);
        if (!d1)
            return null;
        try {
            switch (name[0]) {
                case "<": return this.deductions[this.metaInvDeductTheorem(d1name, "元定理生成*")];
                case ">": return this.deductions[this.metaDeductTheorem(d1name, "元定理生成*")];
                case "c": return this.deductions[this.metaConditionTheorem(d1name, "元定理生成*")];
                case "v": return this.deductions[this.metaConditionUniversalTheorem(d1name, "元定理生成*")];
                case "u": return this.deductions[this.metaUniversalTheorem(d1name, "元定理生成*")];
                default: return null;
            }
        }
        catch (e) {
            throw `无法通过元推理生成推理规则${name}：` + e;
        }
    }
    deduct(step, inlineMode) {
        const { conditionIdxs, deductionIdx, replaceValues } = step;
        const deduction = this.generateDeduction(deductionIdx);
        const errorMsg = `规则${deductionIdx} 推理失败: `;
        if (!deduction)
            throw errorMsg + "规则不存在";
        const { conditions, conclusion, replaceNames, steps, replaceTypes } = deduction;
        // firstly, match condition, get matchtable ( partial initially provided by users)
        let replacedVarTypeTable = {};
        let matchTable = Object.fromEntries(replaceNames.map((replname, idx) => (assert.getReplVarsType(replaceValues[idx], replacedVarTypeTable, replaceTypes[replname]),
            [replname, replaceValues[idx]])));
        let assertions = [];
        let assertionsFrom = [];
        for (const [conditionIdx, condition] of conditions.entries()) {
            const condPropIdx = conditionIdxs[conditionIdx];
            const condProp = this.propositions[condPropIdx];
            if (!condProp)
                throw errorMsg + `第${conditionIdx + 1}个条件对应的定理p${condPropIdx}不存在`;
            try {
                assert.match(condProp.value, condition, /^\$/, false, matchTable, replacedVarTypeTable, assertions);
                while (assertionsFrom.length < assertions.length)
                    assertionsFrom.push(conditionIdx);
            }
            catch (e) {
                // match failed
                throw errorMsg + `第${conditionIdx + 1}个条件` + e;
            }
        }
        // then replace replvars in assertions by matchtable, and check them
        for (const [idx, ass] of assertions.entries()) {
            const cas = astmgr.clone(ass);
            astmgr.replaceByMatchTable(cas, matchTable);
            // todo: how to get assert's type
            try {
                assert.assertUnwrap(cas, replacedVarTypeTable);
            }
            catch (e) {
                // assertion in condition failed (first layer must be T)
                throw errorMsg + `第${assertionsFrom[idx] + 1}个条件中` + e;
            }
        }
        // finally replace conclusion
        let replacedConclusion = astmgr.clone(conclusion);
        astmgr.replaceByMatchTable(replacedConclusion, matchTable);
        try {
            assert.checkGrammer(replacedConclusion, "p", this.consts);
            // grammar in conclusion failed
        }
        catch (e) {
            throw "结论中出现语法错误：" + e;
        }
        try {
            assert.expand(replacedConclusion, true);
        }
        catch (e) {
            // assertion in conclusion failed (can be T or U, only F to fail)
            throw errorMsg + `结论中` + e;
        }
        // if it isn't macro or not inineMode, done
        let netInlineMode = inlineMode;
        if (typeof netInlineMode === "function")
            netInlineMode = netInlineMode(step, replacedConclusion);
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
                if (idx >= 0)
                    return conditionIdxs[idx];
                let newIdx = this.propositions.length + idx;
                for (let i = 0; i < -1 - idx; i++) {
                    newIdx -= propsOffset[i];
                }
                return newIdx;
            });
            const replaceValues = substep.replaceValues.map(ast => {
                const replaced = astmgr.clone(ast);
                astmgr.replaceByMatchTable(replaced, matchTable);
                return replaced;
            });
            let firstPos = this.propositions.length - 1;
            let lastPos;
            try {
                lastPos = this.deduct({ deductionIdx: substep.deductionIdx, replaceValues, conditionIdxs: replacedConditionIdxs }, netInlineMode === "deep" ? inlineMode : null);
            }
            catch (e) {
                // if one substep is wrong, remove newly added substeps from proplist
                const substepErrMsg = errorMsg + `子步骤${substepIdx + 1}(${substep.deductionIdx})中 ` + e;
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
    expandMacroWithProp(propositionIdx) {
        const p = this.propositions[propositionIdx];
        if (!p.from)
            throw "该定理为假设，无推理步骤可展开";
        const { deductionIdx, conditionIdxs, replaceValues } = p.from;
        if (!this.deductions[deductionIdx].steps)
            throw `该定理由来自<${this.deductions[deductionIdx].from}>的原子推理规则得到，无子步骤`;
        const hyps = conditionIdxs.map(c => this.propositions[c].value);
        this.removePropositions();
        // expandMode set true to skip local var check in addHypothese
        hyps.forEach(h => this.addHypothese(h, true));
        this.deduct({
            deductionIdx, conditionIdxs: hyps.map((v, idx) => idx), replaceValues
        }, "inline");
    }
    expandMacroWithDefaultValue(deductionIdx, inlineMode = "inline", expandAxiom) {
        const d = this.deductions[deductionIdx];
        if (!d)
            throw `推理规则${deductionIdx}不存在`;
        if (!expandAxiom && !d.steps)
            throw `无法展开原子推理规则`;
        this.removePropositions();
        d.conditions.forEach(dcond => this.addHypothese(dcond));
        this.deduct({
            deductionIdx, conditionIdxs: d.conditions.map((v, idx) => idx),
            replaceValues: d.replaceNames.map(str => ({ type: "replvar", name: str }))
        }, inlineMode);
    }
    _findNewReplName(deductionIdx) {
        const d = this.deductions[deductionIdx];
        let name = "$0", i = 0;
        let p = new Set;
        for (const c of d.conditions)
            astmgr.getVarNames(c, p, /^\$/);
        astmgr.getVarNames(d.conclusion, p, /^\$/);
        while (p.has(name)) {
            name = "$" + (i++);
        }
        return { type: "replvar", name };
    }
    metaQuantifyAxiomSchema(deductionIdx, from) {
        const d = this.generateDeduction(deductionIdx);
        if (!d)
            throw "推理规则 " + deductionIdx + " 不存在";
        if (d.conditions?.length)
            throw "无法匹配带条件的推理规则";
        if (d.steps?.length)
            throw "无法匹配非公理推理规则";
        if (this.deductions["v" + deductionIdx])
            return "v" + deductionIdx;
        return this.addDeduction("v" + deductionIdx, {
            type: "meta", name: "⊢",
            nodes: [
                { type: "fn", name: "#array", nodes: [] },
                {
                    type: "fn", name: "#array", nodes: [
                        {
                            type: "sym", name: "V", nodes: [
                                this._findNewReplName(deductionIdx),
                                d.conclusion
                            ]
                        }
                    ]
                },
            ]
        }, from);
    }
    metaNewConstant(replaceValues, from) {
        const [constAst, varAst, exprAst] = replaceValues;
        if (constAst.type !== "replvar")
            throw "$$0只能为纯变量名";
        if (constAst.name.startsWith("$"))
            throw "以$开头的变量名称被系统保留";
        if (constAst.name.startsWith("#"))
            throw "以#开头的变量名称被系统保留";
        const constCheckRes = this.isNameCanBeNewConst(constAst.name);
        if (constCheckRes !== true)
            throw "匹配条件##newconst($$0)时：" + constCheckRes;
        if (this.fns.has(constAst.name))
            throw "匹配条件##newconst($$0)时：$$0已有定义";
        const deduction = astmgr.clone(this.metaRules["c"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": constAst,
            "$$1": varAst,
            "$$2": exprAst
        };
        astmgr.replaceByMatchTable(deduction, replTable);
        throw "todo: not implemented yet";
        // this.expandReplFn(deduction, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule, "##repl");
        this.consts.add(constAst.name);
        return this.addDeduction("d" + constAst.name, deduction, from);
    }
    metaConditionUniversalTheorem(idx, from) {
        // mp
        if (this.deductions["v" + idx])
            return "v" + idx;
        const d = this.generateDeduction(idx);
        const s = this._findNewReplName(idx);
        // axiom
        if (!d.steps?.length) {
            return this.metaQuantifyAxiomSchema(idx, "元定理生成*");
        }
        // macro
        const offsetTable = [];
        const offsetCondTable = [];
        const generate = (condMode, idx) => {
            idx ??= d.steps.length - 1 + d.conditions.length;
            const step = d.steps[idx - d.conditions.length];
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            if (!condMode) {
                // avoid repeated deductions on the same prop (here reaching hyps are not possible)
                if (isFinite(offsetTable[idx]))
                    return offsetTable[idx];
                // mp, axiom or macros
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: step.replaceValues,
                    conditionIdxs: step.conditionIdxs.map(id => generate(false, id >= 0 ? id : idx + id))
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx]))
                return offsetCondTable[idx];
            return offsetCondTable[idx] = this.deduct({
                deductionIdx: this.metaConditionUniversalTheorem(sdidx, ""),
                replaceValues: sd.conditions.length ? step.replaceValues : [s, ...step.replaceValues],
                conditionIdxs: step.conditionIdxs.map(id => generate(true, id >= 0 ? id : idx + id))
            });
        };
        const oldP = this.propositions;
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => {
                this.addHypothese({ type: "sym", name: "V", nodes: [s, c] });
                offsetCondTable.push(id);
            });
            generate(true);
            const ret = this.addMacro("v" + idx, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaUniversalTheorem(idx, from) {
        if (this.deductions["u" + idx])
            return "u" + idx;
        const d = this.generateDeduction(idx);
        if (!d)
            throw "条件中的推理规则不存在";
        if (!d.conditions.length)
            return this.metaConditionUniversalTheorem(idx, from);
        const s = this._findNewReplName(idx);
        for (const [idx, cond] of d.conditions.entries()) {
            if (assert.nf(s.name, cond) === -1) {
                throw `元推理结论规则中的条件中的#nf函数永远无法通过验证`;
            }
        }
        // macro
        const offsetTable = [];
        const offsetCondTable = [];
        // find wrappers (e.g. #nf #vnf ..) for replvars in condition
        const replvarTable = {};
        const generate = (condMode, idx) => {
            idx ??= d.steps.length - 1 + d.conditions.length;
            const step = d.steps[idx - d.conditions.length];
            // step may not exists, e.g. hyp
            const stepReplaceValues = step?.replaceValues?.map(v => {
                const cv = astmgr.clone(v);
                astmgr.replaceByMatchTable(cv, replvarTable);
                return cv;
            });
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            if (!condMode) {
                // avoid repeated deductions on the same prop (here reaching hyps are not possible)
                if (isFinite(offsetTable[idx]))
                    return offsetTable[idx];
                // mp, axiom or macros
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: stepReplaceValues,
                    conditionIdxs: step.conditionIdxs.map(id => generate(false, id >= 0 ? id : idx + id))
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx]))
                return offsetCondTable[idx];
            return offsetCondTable[idx] = this.deduct({
                deductionIdx: this.metaConditionUniversalTheorem(sdidx, "元定理生成*"),
                replaceValues: sd.conditions.length ? stepReplaceValues : [s, ...stepReplaceValues],
                conditionIdxs: step.conditionIdxs.map(id => generate(true, id >= 0 ? id : idx + id))
            });
        };
        const oldP = this.propositions;
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => {
                const newHyp = { type: "fn", name: "#nf", nodes: [c, s] };
                this.addHypothese(newHyp);
                try {
                    assert.match(this.propositions[id].value, c, /^\$/, false, replvarTable, {}, []);
                }
                catch (e) {
                    throw `向第${id + 1}个条件添加不自由断言时出现不一致：` + e;
                }
            });
            d.conditions.forEach((c, id) => {
                const p0 = this.deduct({ deductionIdx: "a6", replaceValues: [this.propositions[id].value, s], conditionIdxs: [] });
                const p1 = this.deduct({ deductionIdx: "mp", conditionIdxs: [p0, id], replaceValues: [] });
                offsetCondTable[id] = p1;
            });
            generate(true);
            const ret = this.addMacro("u" + idx, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaNewFunction(replaceValues, from) {
        const [fnAst, varAst1, varAst2, exprAst] = replaceValues;
        if (fnAst.type !== "replvar")
            throw "$$0只能为纯变量名";
        if (fnAst.name.startsWith("#"))
            throw "以#开头的函数被系统保留";
        if (fnAst.name.startsWith("$"))
            throw "以$开头的函数被系统保留";
        const fnCheckRes = this.fns.has(fnAst.name) || this.consts.has(fnAst.name);
        if (fnCheckRes)
            throw `匹配条件##newfn($$0)时：$$0已有定义`;
        const deduction = astmgr.clone(this.metaRules["f"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": fnAst,
            "$$1": varAst1,
            "$$2": varAst2,
            "$$3": exprAst
        };
        throw "todo: not implemented yet";
        // astmgr.replaceByMatchResult(deduction, replTable);
        // this._replaceFnName(deduction, "$$0", fnAst.name);
        // this.expandReplFn(deduction, this.deductionReplNameRule, this.localNameRule, this.replacedLocalNameRule, "##repl");
        this.fns.add(fnAst.name);
        return this.addDeduction("d" + fnAst.name, deduction, from);
    }
    _replaceFnName(ast, src, dst) {
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
    metaConditionTheorem(idx, from) {
        // mp
        if (this.deductions["c" + idx])
            return "c" + idx;
        const d = this.generateDeduction(idx);
        const s = this._findNewReplName(idx);
        // axiom, |- A
        if (!d.conditions.length) {
            const oldP = this.propositions;
            try {
                this.expandMacroWithDefaultValue(idx, null, true);
                const value = this.propositions[0].value;
                this.deduct({
                    deductionIdx: "a1", conditionIdxs: [],
                    replaceValues: [value, s]
                });
                this.deduct({
                    deductionIdx: "mp", replaceValues: [],
                    conditionIdxs: [1, 0]
                });
                const ret = this.addMacro("c" + idx, from);
                this.propositions = oldP;
                return ret;
            }
            catch (e) {
                this.propositions = oldP;
                throw e;
            }
        }
        // ...A |- B
        const offsetTable = [];
        const offsetCondTable = [];
        const generate = (condMode, idx) => {
            idx ??= d.steps.length - 1 + d.conditions.length;
            const step = d.steps[idx - d.conditions.length];
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            if (!condMode) {
                // avoid repeated deductions on the same prop (here reaching hyps are not possible)
                if (isFinite(offsetTable[idx]))
                    return offsetTable[idx];
                // mp, axiom or macros
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: step.replaceValues,
                    conditionIdxs: step.conditionIdxs.map(id => generate(false, id >= 0 ? id : idx + id))
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx]))
                return offsetCondTable[idx];
            if (!sd.conditions.length) {
                const p0 = generate(false, idx);
                const value = this.propositions[p0].value;
                const p1 = this.deduct({
                    deductionIdx: "a1", conditionIdxs: [],
                    replaceValues: [value, s]
                });
                return offsetCondTable[idx] = this.deduct({
                    deductionIdx: "mp", replaceValues: [],
                    conditionIdxs: [p1, p0]
                });
            }
            this.metaConditionTheorem(sdidx, "中间步骤");
            return offsetCondTable[idx] = this.deduct({
                deductionIdx: "c" + sdidx, replaceValues: step.replaceValues,
                conditionIdxs: step.conditionIdxs.map(id => generate(true, id >= 0 ? id : idx + id))
            });
        };
        const oldP = this.propositions;
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => {
                this.addHypothese({ type: "sym", name: ">", nodes: [s, c] });
                offsetCondTable.push(id);
            });
            generate(true);
            const ret = this.addMacro("c" + idx, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaDeductTheorem(idx, from) {
        if (idx[0] === "<" && this.deductions[idx.slice(1)])
            return idx.slice(1);
        if (this.deductions[">" + idx])
            return ">" + idx;
        const d = this.generateDeduction(idx);
        // mp, axiom, |- A : error
        if (!d.conditions.length) {
            throw "推理规则不包含假设，无法与条件匹配";
        }
        if (idx === "mp")
            throw "元推理结论 >mp 为 (($0 > $1) ⊢ ($0 > $1))，假设与结论相同";
        // ...A, B |- C
        let offsetTable = [];
        let offsetCondTable = [];
        let s; // condAst
        const generate = (condMode, idx) => {
            idx ??= d.steps.length - 1 + d.conditions.length;
            const step = d.steps[idx - d.conditions.length];
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            if (!condMode) {
                // avoid repeated deductions on the same prop
                if (isFinite(offsetTable[idx]))
                    return offsetTable[idx];
                // here if reaching hyp B, roll back
                if (!step) {
                    return -1;
                }
                // mp, axiom or macros, if rely on hyp B, roll back recursively
                const state = [offsetTable.slice(0), this.propositions.slice(0)];
                const condIdxs = [];
                for (const id of step.conditionIdxs) {
                    const n = generate(false, id >= 0 ? id : idx + id);
                    if (n === -1) {
                        [offsetTable, this.propositions] = state;
                        return -1;
                    }
                    condIdxs.push(n);
                }
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: step.replaceValues,
                    conditionIdxs: condIdxs
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx]))
                return offsetCondTable[idx];
            // B: B>B
            if (idx === d.conditions.length - 1) {
                return offsetCondTable[idx] = this.deduct({ deductionIdx: ".i", conditionIdxs: [], replaceValues: [s] });
            }
            const p0 = generate(false, idx);
            // if deduction steps don't contain hyp B
            if (p0 !== -1) {
                const value = this.propositions[p0].value;
                const p1 = this.deduct({
                    deductionIdx: "a1", conditionIdxs: [],
                    replaceValues: [value, s]
                });
                return offsetCondTable[idx] = this.deduct({
                    deductionIdx: "mp", replaceValues: [],
                    conditionIdxs: [p1, p0]
                });
            }
            this.metaConditionTheorem(sdidx, "中间步骤");
            return offsetCondTable[idx] = this.deduct({
                deductionIdx: "c" + sdidx, replaceValues: step.replaceValues,
                conditionIdxs: step.conditionIdxs.map(id => generate(true, id >= 0 ? id : idx + id))
            });
        };
        const oldP = this.propositions;
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => {
                if (id !== d.conditions.length - 1) {
                    this.addHypothese(c);
                    offsetTable.push(id);
                }
                else {
                    s = c;
                }
            });
            generate(true);
            const ret = this.addMacro(">" + idx, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaInvDeductTheorem(idx, from) {
        // >a => a
        if (idx[0] === ">" && this.deductions[idx.slice(1)])
            return idx.slice(1);
        // a => <a
        if (this.deductions["<" + idx])
            return "<" + idx;
        const d = this.generateDeduction(idx);
        const oldP = this.propositions;
        const conclusion = d.conclusion;
        if (conclusion.type !== "sym" || conclusion.name !== ">")
            throw "条件推理规则(...$$0 ⊢ ($$1 > $$2))匹配失败";
        const [ss1, ss2] = conclusion.nodes;
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => this.addHypothese(c));
            const nhyp = this.addHypothese(ss1);
            const ss1_ss2 = this.deduct({
                deductionIdx: idx, conditionIdxs: d.conditions.map((v, id) => id),
                replaceValues: d.replaceNames.map(str => ({ type: "replvar", name: str }))
            });
            this.deduct({ deductionIdx: "mp", replaceValues: [], conditionIdxs: [ss1_ss2, nhyp] });
            const ret = this.addMacro("<" + idx, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaIffTheorem(idx, replaceValues, name, from) {
        const d = this.generateDeduction(idx);
        if (!d)
            throw "推理规则不存在";
        if (d.conditions?.length)
            throw "条件推理规则( ⊢ ($$0 <> $$1))匹配失败";
        const conclusion = d.conclusion;
        if (conclusion.type !== "sym" || conclusion.name !== "<>")
            throw "条件推理规则( ⊢ ($$0 <> $$1))匹配失败";
        const [A, B] = conclusion.nodes;
        const [C, N] = replaceValues;
        if (N.type !== "replvar")
            throw "匹配序号参数必须为非负整数";
        let nth = Number(N.name);
        if (!isFinite(nth) || Math.floor(nth) !== nth || nth < 0)
            throw "匹配序号参数必须为非负整数";
        nth -= 1;
        const oldP = this.propositions;
        const R = astmgr.clone(C);
        astmgr.replace(R, A, B, false, nth);
        let A_B;
        // generate a <> b or VxVyVz a<>b
        const generate = (a, b, Vs = []) => {
            const prefix = "".padEnd(Vs.length, "v");
            if (astmgr.equal(a, b)) {
                // a == b : a <> a
                return this.deduct({ deductionIdx: prefix + ".<>3", conditionIdxs: [], replaceValues: [...Vs, a] });
            }
            if (astmgr.equal(a, A) && astmgr.equal(b, B)) {
                // A <> B  (cannot reach B <> A)
                return this.deduct({
                    deductionIdx: prefix + idx, conditionIdxs: [],
                    replaceValues: [...Vs, ...d.replaceNames.map(str => ({ type: "replvar", name: str }))]
                });
            }
            if (!a.nodes?.length || a.nodes?.length !== b.nodes?.length) {
                throw "元推理函数中替换函数##crp执行失败";
            }
            if (a.type !== B.type || a.name !== b.name) {
                throw "元推理函数中替换函数##crp执行失败";
            }
            if (a.type === "sym") {
                if (a.name === ">" || a.name === "<>" || a.name === "&" || a.name === "|") {
                    return this.deduct({
                        deductionIdx: prefix + ".<>r" + a.name, replaceValues: [],
                        conditionIdxs: [generate(a.nodes[0], b.nodes[0], Vs), generate(a.nodes[1], b.nodes[1], Vs)],
                    });
                }
                if (a.name === "~") {
                    return this.deduct({
                        deductionIdx: prefix + ".<>r~", replaceValues: [],
                        conditionIdxs: [generate(a.nodes[0], b.nodes[0], Vs)],
                    });
                }
                if (a.name === "V") {
                    const vab = generate(a.nodes[1], b.nodes[1], [...Vs, a.nodes[0]]);
                    return this.deduct({
                        deductionIdx: prefix + "<.<>rV", replaceValues: [],
                        conditionIdxs: [vab],
                    });
                }
                if (a.name === "E") {
                    const nvnab = generate({
                        type: "sym", name: "~", nodes: [{
                                type: "sym", name: "V", nodes: [
                                    a.nodes[0], { type: "sym", name: "~", nodes: [a.nodes[1]] }
                                ]
                            }]
                    }, {
                        type: "sym", name: "~", nodes: [{
                                type: "sym", name: "V", nodes: [
                                    b.nodes[0], { type: "sym", name: "~", nodes: [b.nodes[1]] }
                                ]
                            }]
                    }, Vs);
                    return this.deduct({
                        deductionIdx: prefix + ".<>rE", replaceValues: [],
                        conditionIdxs: [nvnab],
                    });
                }
            }
        };
        try {
            this.removePropositions();
            generate(C, R);
            const ret = this.addMacro(name, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
}
//# sourceMappingURL=formalsystem.js.map