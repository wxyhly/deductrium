import { ASTMgr } from "./astmgr.js";
import { AssertionSystem } from "./assertion.js";
import { Proof } from "./proof.js";
import { ASTParser } from "./astparser.js";
import { TR } from "../lang.js";
const astmgr = new ASTMgr;
const assert = new AssertionSystem;
const parser = new ASTParser;
export class FormalSystem {
    deductions = {};
    metaRules = {};
    fastmetarules = "";
    disabledMetaRules = [];
    deductionReplNameRule = /^\$/g;
    localNameRule = /^\#/g;
    localReplacedNameRule = /^\#\#/g;
    // replacedLocalNameRule: RegExp = /^&/g;
    // ignoreNfNameRule: RegExp = /^(&|#)/g;
    // fnParamNames = (n: number) => "#" + n;
    consts = new Set(); // [constName -> defineDeductionIdx]
    fns = new Set(); // [fnName -> defineDeductionIdx]
    propositions = [];
    assert = assert;
    ast2deduction(ast) {
        assert.checkGrammer(ast, "d", this.consts);
        const [conditions, conclusions] = ast.nodes;
        const varLists = {};
        const allReplvars = new Set;
        const matchingReplvars = new Set;
        conditions.nodes.map(c => {
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
            from: "",
            tempvars: null
        };
    }
    ast2metaRule(ast) {
        let grammarCheck = ast.type === "meta" && ast.name === "⊢M" && ast.nodes?.length === 2;
        if (!grammarCheck)
            throw TR("未找到元推理符号");
        const [conditions, conclusions] = ast.nodes;
        if (!conclusions.nodes?.length)
            throw TR("元推理符号后面没有结论");
        return {
            value: ast,
            conclusions: conclusions.nodes,
            conditions: conditions.nodes,
            replaceNames: [], conditionDeductionIdxs: [],
            from: ""
        };
    }
    getdependency(name, deductionIdx) {
        if (!deductionIdx)
            return false;
        return name === deductionIdx || deductionIdx.match(new RegExp("^[vc<>ue:]*" + name + "(,.+$)?$"));
    }
    removeDeduction(name) {
        if (!this.deductions[name])
            throw TR("规则名称 ") + name + TR(" 不存在");
        // if (this.deductions[name].from.match(/$/)) throw "无法删除系统规则";
        for (const [n, d] of Object.entries(this.deductions)) {
            if (!d.steps)
                continue;
            if (name === n)
                continue;
            for (const s of d.steps) {
                if (this.getdependency(name, s.deductionIdx)) {
                    throw TR("无法删除规则 ") + name + TR("，请先删除对其有依赖的规则 ") + n;
                }
            }
        }
        for (const [n, p] of this.propositions.entries()) {
            if (this.getdependency(name, p.from?.deductionIdx)) {
                throw TR("无法删除规则 ") + name + TR("，请先删除对其有依赖的定理 p") + n;
            }
        }
        let res = (this.deductions[name].from.match(/^dc\((.+)\)$/g));
        if (res && res[1]) {
            if (!this.consts.delete(res[1]))
                throw TR("删除了不存在的常量的定义公理 ") + name;
        }
        res = (this.deductions[name].from.match(/^df\((.+)\)$/g));
        if (res && res[1]) {
            if (!this.fns.delete(res[1]))
                throw TR("删除了不存在的函数的定义公理 ") + name;
        }
        delete this.deductions[name];
        return true;
    }
    addDeduction(name, d, from, macro, tempvars) {
        const deduction = this.ast2deduction(d);
        deduction.from = from;
        deduction.steps = macro;
        deduction.tempvars = tempvars ?? this.findLocalNamesInDeductionStep(macro);
        if (this.deductions[name])
            throw TR("规则名称 ") + name + TR(" 已存在");
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
    _hasRpFn(m) {
        if (m.type === "fn" && m.name === "#rp") {
            return true;
        }
        if (!m.nodes)
            return false;
        for (const n of m.nodes) {
            if (this._hasRpFn(n))
                return true;
        }
        return false;
    }
    addHypothese(m, expandMode) {
        m = astmgr.clone(m);
        assert.checkGrammer(m, "p", this.consts);
        if (this.propositions.findIndex(e => e.from) !== -1)
            throw TR("无法添加假设条件：假设须添加在其它定理之前");
        if (!expandMode && this._hasLocalNames(m))
            throw TR("假设中不能出现以#号开头的局部变量");
        try {
            assert.expand(m, false);
        }
        catch (e) {
            throw TR("假设中") + e;
        }
        if (!expandMode && this._hasRpFn(m))
            throw TR("假设中不能包含未化简的#rp函数，否则匹配机制将失效");
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
    // find ##0 in ast
    findLocalNamesInAst(ast, reg, res = new Set) {
        if (ast.type === "replvar" && ast.name.match(reg)) {
            res.add(ast.name);
            return res;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this.findLocalNamesInAst(n, reg, res);
            }
        }
        return res;
    }
    // find ##0 in macro
    findLocalNamesInDeductionStep(steps, res = new Set) {
        if (!steps)
            return res;
        for (const step of steps) {
            for (const val of step.replaceValues) {
                this.findLocalNamesInAst(val, this.localReplacedNameRule, res);
                for (const subval of this.generateDeduction(step.deductionIdx).tempvars) {
                    res.add(subval);
                }
            }
        }
        return res;
    }
    replaceTempVar(ast, tempvarTable) {
        if (ast.type === "replvar" && ast.name.match(this.localNameRule)) {
            ast.name = ast.name.replace(/^#([^#].*)$/, "##$1");
            while (tempvarTable.has(ast.name)) {
                ast.name += "#";
            }
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this.replaceTempVar(n, tempvarTable);
            }
        }
    }
    // when inline, recover ##0 to #0. if outter has #0, change it to #0#
    recoverTempVar(ast, tempvarTable) {
        if (ast.type === "replvar" && ast.name.match(/^##.+$/)) {
            ast.name = ast.name.replace(/^##(.+)$/, "#$1");
            while (tempvarTable.has(ast.name)) {
                ast.name += "#";
            }
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this.recoverTempVar(n, tempvarTable);
            }
        }
    }
    addMacro(name, from) {
        const propositionIdx = this.propositions.length - 1;
        let hypothesisAmount = this.propositions.findIndex(e => e.from);
        if (hypothesisAmount == -1)
            hypothesisAmount = this.propositions.length;
        if (propositionIdx < hypothesisAmount)
            throw TR("无有效定理推导步骤，创建宏推导失败");
        const conditions = [];
        for (let i = 0; i < hypothesisAmount; i++) {
            conditions.push(this.propositions[i].value);
        }
        const conclusion = this.propositions[propositionIdx].value;
        if (this._hasLocalNames(conclusion)) {
            throw TR("局部变量不能出现在推理宏的结论中");
        }
        const macro = [];
        const subTempvars = new Set;
        for (let i = hypothesisAmount; i <= propositionIdx; i++) {
            for (const v of this.generateDeduction(this.propositions[i].from.deductionIdx).tempvars) {
                subTempvars.add(v);
            }
        }
        for (let i = hypothesisAmount; i <= propositionIdx; i++) {
            const step = this.propositions[i].from;
            macro.push({
                conditionIdxs: step.conditionIdxs.map(cidx => cidx < hypothesisAmount ? cidx : cidx - i),
                replaceValues: step.replaceValues.map(v => {
                    const newv = astmgr.clone(v);
                    // replace #0 to ##0, if conflict with substep, rename it as ##0#
                    this.replaceTempVar(newv, subTempvars);
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
        if (assert.isConst(name, this.consts))
            return `"${name}" ` + TR(`已有定义，无法重复定义`);
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
    generateDeductionNameTokens(name, cursor = 0, res) {
        switch (name[cursor]) {
            case "<":
            case ">":
            case "c":
            case "u":
            case "v":
            case "e":
                res.push(name[cursor]);
                return this.generateDeductionNameTokens(name, cursor + 1, res);
            case ":":
                res.push(name[cursor]);
                cursor = this.generateDeductionNameTokens(name, cursor + 1, res);
                return this.generateDeductionNameTokens(name, cursor + 1, res);
            case ",": throw TR("发现意外的“,”字符");
            default:
                let dname = "";
                for (; cursor < name.length && name[cursor] !== ","; cursor++) {
                    dname += name[cursor];
                }
                res.push(dname);
                return cursor;
        }
    }
    generateDeductionAndName(name, tokens, cursor = 0) {
        if (this.deductions[name])
            return [name, this.deductions[name], cursor + 1];
        let n;
        let n2;
        let d;
        let c;
        const unlocked = this.fastmetarules;
        switch (tokens[cursor]) {
            case "<":
                if (!unlocked.includes("<"))
                    throw "null";
                [n, d, c] = this.generateDeductionAndName(name, tokens, cursor + 1);
                return [tokens[cursor] + n, this.deductions[this.metaInvDeductTheorem(n, "元规则生成*")], c];
            case ">":
                if (!unlocked.includes(">"))
                    throw "null";
                [n, d, c] = this.generateDeductionAndName(name, tokens, cursor + 1);
                return [tokens[cursor] + n, this.deductions[this.metaDeductTheorem(n, "元规则生成*")], c];
            case "c":
                if (!unlocked.includes("c"))
                    throw "null";
                [n, d, c] = this.generateDeductionAndName(name, tokens, cursor + 1);
                return [tokens[cursor] + n, this.deductions[this.metaConditionTheorem(n, "元规则生成*")], c];
            case "e":
                if (!unlocked.includes("e"))
                    throw "null";
                [n, d, c] = this.generateDeductionAndName(name, tokens, cursor + 1);
                return [tokens[cursor] + n, this.deductions[this.metaExistTheorem(n, "元规则生成*")], c];
            case "v":
                if (!unlocked.includes("v")) {
                    if (!unlocked.includes("q"))
                        throw "null";
                    [n, d, c] = this.generateDeductionAndName(name, tokens, cursor + 1);
                    return ["v" + n, this.deductions[this.metaQuantifyAxiomSchema(n, "元规则生成*")], c];
                }
                [n, d, c] = this.generateDeductionAndName(name, tokens, cursor + 1);
                return [tokens[cursor] + n, this.deductions[this.metaConditionUniversalTheorem(n, "元规则生成*")], c];
            case "u":
                if (!unlocked.includes("u"))
                    throw "null";
                [n, d, c] = this.generateDeductionAndName(name, tokens, cursor + 1);
                return [tokens[cursor] + n, this.deductions[this.metaUniversalTheorem(n, "元规则生成*")], c];
            case ":":
                if (!unlocked.includes(":"))
                    throw "null";
                [n, d, cursor] = this.generateDeductionAndName(name, tokens, cursor + 1);
                [n2, d, cursor] = this.generateDeductionAndName(name, tokens, cursor);
                return [":" + n + "," + n2, this.deductions[this.metaCombineTheorem(n, n2, "元规则生成*")], c];
            case ",": throw ",";
            default:
                if (tokens[cursor].match(/^d[1-9][0-9]+$/) && unlocked.includes("#")) {
                    this.generateNatLiteralDef(tokens[cursor]);
                }
                this.generateNatLiteralOp(tokens[cursor]);
                if (this.deductions[tokens[cursor]])
                    return [tokens[cursor], this.deductions[tokens[cursor]], cursor + 1];
                throw "null";
        }
    }
    generateDeduction(name) {
        if (!name)
            return null;
        try {
            const tokens = [];
            this.generateDeductionNameTokens(name, 0, tokens);
            const ret = this.generateDeductionAndName(name, tokens)[1];
            return ret;
        }
        catch (e) {
            if (e === "null")
                return null;
            if (e === ",")
                throw TR(`使用元规则生成推理规则`) + name + TR(`时：意外出现了“,”`);
            throw TR(`使用元规则生成推理规则`) + name + TR(`时：`) + e;
        }
    }
    generateNatLiteralDef(name) {
        const n = name.match(/^d([1-9][0-9]+)$/);
        if (!n || !isFinite(Number(n[1])))
            return;
        if (this.deductions[name])
            return name;
        const num = Number(n[1]);
        return this.addDeduction(name, parser.parse(`⊢${num} =S(${num - 1})`), "算数符号定义");
    }
    generateNatLiteralOp(name, vnum = 0) {
        const vpre = "v".repeat(vnum);
        const vars = [];
        let V = "";
        for (let i = 0; i < vnum; i++) {
            vars.push({ type: "replvar", name: "$" + i });
            V += "V$" + i + ":";
        }
        const n = name.match(/^\.([1-9][0-9]*)([\+\*])([1-9][0-9]*)$/);
        if (!n || !isFinite(Number(n[1])) || !isFinite(Number(n[3])))
            return;
        if (this.deductions[vpre + name])
            return vpre + name;
        const a = Number(n[1]);
        const b = Number(n[3]);
        const op = n[2];
        const steps = [
            b > 1 ?
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "." + a + op + (b - 1) } :
                { conditionIdxs: [], replaceValues: [...vars, { type: "replvar", name: String(a) }], deductionIdx: vpre + "d" + op + "1" },
            { conditionIdxs: [], replaceValues: [...vars, { type: "replvar", name: String(a) }, { type: "replvar", name: String(b - 1) }], deductionIdx: vpre + "d" + op + "2" },
            { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "d" + b },
            op === "+" ? { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "d" + (a + b) } : b === 1 ? { conditionIdxs: [], replaceValues: [{ type: "replvar", name: String(a) }], deductionIdx: ".0+" } :
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + `.${a * (b - 1)}+${a}` },
            { conditionIdxs: [-4, -3], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" },
            op === "+" ? { conditionIdxs: [-2], replaceValues: [], deductionIdx: vpre + ".=s" } : { conditionIdxs: [-1, -2], replaceValues: [], deductionIdx: vpre + ".=t" },
            { conditionIdxs: [-4], replaceValues: [], deductionIdx: vpre + ".=s" },
            { conditionIdxs: [-1, -3], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" },
            op === "+" ? { conditionIdxs: [-3, -1], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" } :
                { conditionIdxs: [-1, -5], replaceValues: [], deductionIdx: vpre + ".=t" }
        ];
        return this.addDeduction(vpre + name, parser.parse(`⊢${V}(${a}${op}${b}=${op === "+" ? a + b : a * b})`), "元规则生成*", steps, new Set());
    }
    deduct(step, inlineMode) {
        const { conditionIdxs, deductionIdx, replaceValues } = step;
        const deduction = this.generateDeduction(deductionIdx);
        const errorMsg = TR(`规则 `) + deductionIdx + TR(` 推理失败:`);
        if (!deduction)
            throw errorMsg + TR("规则不存在");
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
                throw errorMsg + TR(`第${conditionIdx + 1}个`) + TR(`条件对应的定理p`) + condPropIdx + TR(`不存在`);
            try {
                assert.match(condProp.value, condition, /^\$/, false, matchTable, replacedVarTypeTable, assertions);
                while (assertionsFrom.length < assertions.length)
                    assertionsFrom.push(conditionIdx);
            }
            catch (e) {
                // match failed
                throw errorMsg + TR(`第${conditionIdx + 1}个`) + TR(`条件`) + e;
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
                throw errorMsg + TR(`第${assertionsFrom[idx] + 1}个`) + TR(`条件中:`) + e;
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
            throw TR("结论中出现语法错误：") + e;
        }
        try {
            assert.expand(replacedConclusion, false);
        }
        catch (e) {
            // assertion in conclusion failed (can be T or U, only F to fail)
            throw errorMsg + TR(`结论中：`) + e;
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
        // find outter tempvars
        let tempvars = new Set;
        Object.values(matchTable).forEach(v => this.findLocalNamesInAst(v, this.localNameRule, tempvars));
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
                this.recoverTempVar(replaced, tempvars);
                this.replaceTempVar;
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
                const substepErrMsg = errorMsg + TR(`子步骤`) + `${substepIdx + 1}(${substep.deductionIdx}` + TR(`)中 `) + e;
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
            throw TR("该定理为假设，无推理步骤可展开");
        const { deductionIdx, conditionIdxs, replaceValues } = p.from;
        if (!this.deductions[deductionIdx])
            this.deductions[deductionIdx] = this.generateDeduction(deductionIdx);
        const from = this.deductions[deductionIdx].from;
        if (!this.deductions[deductionIdx].steps)
            throw TR(`该定理由来自<`) + TR(deductionIdx[0] === "v" ? TR("一阶逻辑公理模式") : from) + TR(`>的原子推理规则得到，无子步骤`);
        const hyps = conditionIdxs.map(c => this.propositions[c].value);
        this.removePropositions();
        // expandMode set true to skip local var check in addHypothese
        hyps.forEach(h => this.addHypothese(h, true));
        this.deduct({
            deductionIdx, conditionIdxs: hyps.map((v, idx) => idx), replaceValues
        }, "inline");
    }
    inlineMacroInProp(propositionIdx) {
        const p = this.propositions[propositionIdx];
        if (!p.from)
            throw TR("该定理为假设，无推理步骤可展开");
        const { deductionIdx, conditionIdxs, replaceValues } = p.from;
        if (!this.deductions[deductionIdx])
            this.deductions[deductionIdx] = this.generateDeduction(deductionIdx);
        if (!this.deductions[deductionIdx].steps)
            throw TR(`该定理由来自<`) + TR(this.deductions[deductionIdx].from) + TR(`>的原子推理规则得到，无子步骤`);
        const suivant = [];
        while (true) {
            const p1 = this.propositions.pop();
            if (p1 !== p)
                suivant.unshift(p1);
            if (p1 === p) {
                break;
            }
        }
        const before = this.propositions.length;
        this.deduct({
            deductionIdx, conditionIdxs, replaceValues
        }, "inline");
        const offset = this.propositions.length - before - 1;
        while (true) {
            const p1 = suivant.shift();
            if (!p1)
                break;
            if (!p1.from)
                continue;
            this.propositions.push(p1);
            p1.from.conditionIdxs = p1.from.conditionIdxs.map(id => id < propositionIdx ? id : id + offset);
        }
    }
    expandMacroWithDefaultValue(deductionIdx, inlineMode = "inline", expandAxiom) {
        const d = this.deductions[deductionIdx] || this.generateDeduction(deductionIdx);
        if (!d)
            throw TR(`推理规则 `) + deductionIdx + TR(` 不存在`);
        if (!expandAxiom && !d.steps)
            throw TR(`无法展开原子推理规则`);
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
            throw TR(`推理规则 `) + deductionIdx + TR(` 不存在`);
        if (d.conditions?.length)
            throw TR("无法匹配带条件的推理规则");
        if (d.steps?.length)
            throw TR("无法匹配非公理推理规则");
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
    metaExistTheorem(idx, from) {
        // Hilbert公理体系还有哪些有用的比较通用的元定理，如我知道演绎元定理、概括元定理。
        const d = this.generateDeduction(idx);
        if (d.conditions.length !== 1)
            throw TR("匹配条件推理规则($$0 ⊢ $$1)失败");
        if (this.deductions["e" + idx])
            return "e" + idx;
        const oldP = this.propositions;
        try {
            this.removePropositions();
            const s = this._findNewReplName(idx);
            let pidx = 0;
            // |- Ea   |- v(a>b)  |- Ea > Eb
            this.addHypothese({
                type: "sym", name: "E", nodes: [
                    s, d.conditions[0]
                ]
            });
            pidx++;
            const vd = this.generateDeduction(("v>" + idx).replace("><", ""));
            this.deduct({
                deductionIdx: ("v>" + idx).replace("><", ""),
                replaceValues: vd.replaceNames.map(e => ({ type: "replvar", name: e })),
                conditionIdxs: []
            });
            pidx++;
            this.deduct({
                deductionIdx: ".Emp",
                replaceValues: [],
                conditionIdxs: [1, 0]
            });
            pidx++;
            const ret = this.addMacro("e" + idx, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaConditionUniversalTheorem(idx, from) {
        // mp
        if (this.deductions["v" + idx])
            return "v" + idx;
        const num = idx.match(/^(v*)/)?.[1]?.length;
        if (num >= 0 && this.generateNatLiteralOp(idx.slice(num), 1 + num)) {
            return "v" + idx;
        }
        const d = this.generateDeduction(idx);
        const s = this._findNewReplName(idx);
        // axiom
        if (!d.steps?.length && !d.conditions?.length) {
            return this.metaQuantifyAxiomSchema(idx, "元规则生成*");
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
            throw TR("条件中的推理规则不存在");
        if (!d.conditions.length)
            return this.metaConditionUniversalTheorem(idx, from);
        const s = this._findNewReplName(idx);
        for (const [idx, cond] of d.conditions.entries()) {
            if (assert.nf(s.name, cond) === -1) {
                throw TR(`元推理结论规则中的条件中的#nf函数永远无法通过验证`);
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
                deductionIdx: this.metaConditionUniversalTheorem(sdidx, "元规则生成*"),
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
                    throw TR(`向`) + TR(`第${id + 1}个`) + TR(`条件添加不自由断言时出现不一致：`) + e;
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
        const fnCheckRes = this.fns.has(fnAst.name) || assert.isConst(fnAst.name, this.consts);
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
            throw TR("推理规则不包含假设，无法与条件匹配");
        }
        if (idx === "mp")
            throw TR("元推理结论 >mp 为 (($0 > $1) ⊢ ($0 > $1))，假设与结论相同");
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
            throw TR("条件推理规则(...$$0 ⊢ ($$1 > $$2))匹配失败");
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
    metaCompleteTheorem(ast, name, from) {
        const proof = new Proof(this);
        const p = this.propositions;
        try {
            this.propositions = [];
            proof.prove(ast);
            this.addMacro(name, from);
            this.propositions = p;
        }
        catch (e) {
            this.propositions = p;
            throw e;
        }
        return name;
    }
    metaCombineTheorem(idx1, idx2, from) {
        const name = ":" + idx1 + "," + idx2;
        if (this.deductions[name])
            return name;
        const d1 = this.generateDeduction(idx1);
        const d2 = this.generateDeduction(idx2);
        if (d2.conditions.length !== 1)
            throw TR("匹配条件推理规则($$1b ⊢ $$2)失败");
        const oldP = this.propositions;
        try {
            this.removePropositions();
            d1.conditions.forEach((c, id) => this.addHypothese(c));
            const p1 = this.deduct({
                deductionIdx: idx1, conditionIdxs: d1.conditions.map((v, id) => id),
                replaceValues: d1.replaceNames.map(str => ({ type: "replvar", name: str }))
            });
            const p2 = this.deduct({
                deductionIdx: idx2, conditionIdxs: [p1],
                replaceValues: d2.replaceNames.map(str => ({ type: "replvar", name: str }))
            });
            const ret = this.addMacro(name, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaChangeNameTheorem(ast, newNames, name, from) {
        let oldNames = [];
        const VEs = []; // V for true, E for false
        let sub = ast;
        let count = 0;
        while (sub.type === "sym" && (sub.name === "V" || sub.name === "E")) {
            oldNames.push(sub.nodes[0].name);
            VEs.push(sub.name === "V");
            if (count++ >= newNames.length)
                break;
            sub = sub.nodes[1];
        }
        const oldP = this.propositions;
        let lastP;
        const uniq = "#";
        const replace = (ast, start, newNames, invOrder) => {
            const newNamesInv = newNames.slice(0).reverse();
            const oldNames = [];
            let sub = ast;
            let startCount = 0;
            let subBody;
            let subprefix = [];
            while (sub.type === "sym" && sub.name === "V") {
                if (startCount < start) {
                    subprefix.push(sub.nodes[0]);
                }
                else if (startCount === start) {
                    subBody = sub;
                }
                if (startCount++ >= start) {
                    oldNames.push(sub.nodes[0].name);
                }
                sub = sub.nodes[1];
            }
            lastP = this.deduct({
                deductionIdx: "v".repeat(start) + ".i",
                replaceValues: [...subprefix, subBody],
                conditionIdxs: [],
            });
            // VxVy: > V#xV#yVxVy:
            // for (const n of newNamesInv) {
            //     lastP = this.deduct({
            //         deductionIdx: "v".repeat(start) + "c<a6",
            //         replaceValues: [{ type: "replvar", name: oldNames.has(n) ? uniq + n : n }],
            //         conditionIdxs: [lastP],
            //     });
            // }
            // // lastP = this.deduct({
            // //     deductionIdx: ".i",
            // //     replaceValues: [{type:"replvar",name:"a"}],
            // //     conditionIdxs: [],
            // // });
            // //V#xV#yVxVy:f(x,y) > V#xV#y:f(#x,#y)
            // for (const n of newNames) {
            //     lastP = this.deduct({
            //         deductionIdx: "v".repeat(start) + "c" + ("v".repeat(newNames.length)) + "<a4",
            //         replaceValues: [
            //             { type: "replvar", name: oldNames.has(n) ? uniq + n : n }
            //         ],
            //         conditionIdxs: [lastP],
            //     });
            // }
            // V#xV#y: > V$xV$yV#xV#y:
            if (invOrder) { // replace from right to left
                for (let i = newNames.length - 1; i >= 0; i--) {
                    const n = newNames[i];
                    // V#xV$y: > V$xV#xV$y
                    if (oldNames[i] === n) {
                        continue;
                    }
                    lastP = this.deduct({
                        deductionIdx: "v".repeat(start) + "c" + ("v".repeat(i)) + "<a6",
                        replaceValues: [{ type: "replvar", name: n }],
                        conditionIdxs: [lastP],
                    });
                    // V$xV#xV$y: > V$xV$y
                    lastP = this.deduct({
                        deductionIdx: "v".repeat(start) + "c" + ("v".repeat(i + 1)) + "<a4",
                        replaceValues: [{ type: "replvar", name: n }],
                        conditionIdxs: [lastP],
                    });
                }
            }
            else { // replace from left to right
                let offset = 0;
                for (const n of newNames) {
                    // V#xV$y: > V$xV#xV$y
                    if (oldNames[offset] === n) {
                        offset++;
                        continue;
                    }
                    lastP = this.deduct({
                        deductionIdx: "v".repeat(start) + "c" + ("v".repeat(offset++)) + "<a6",
                        replaceValues: [{ type: "replvar", name: n }],
                        conditionIdxs: [lastP],
                    });
                    // V$xV#xV$y: > V$xV$y
                    lastP = this.deduct({
                        deductionIdx: "v".repeat(start) + "c" + ("v".repeat(offset)) + "<a4",
                        replaceValues: [{ type: "replvar", name: n }],
                        conditionIdxs: [lastP],
                    });
                }
            }
            // .....
            // #$$#$ .....
            // #$$#$
            // $$ #$$#$
            // $$$$$
            // Va1Va2Va3Va4Va5:f(a1,a2,a3,a4,a5)=0
            // V$xV$yV#xV#y:f(#x,#y) > V$xV$yf($x,$y)
            // offset = start + newNames.length;
            // for (const n of newNamesInv) {
            //     if (!oldNames.has(n)) {
            //         offset--;
            //         continue;
            //     }
            //     lastP = this.deduct({
            //         deductionIdx: "c" + ("v".repeat(offset--)) + "<a4",
            //         replaceValues: [
            //             { type: "replvar", name: n }
            //         ],
            //         conditionIdxs: [lastP],
            //     });
            // }
            return lastP;
        };
        const replace2 = (ast, start, newNames) => {
            ast = astmgr.clone(ast);
            let sub = ast;
            for (let i = 0; i < start; i++) {
                if (sub.type === "sym" && (sub.name === "E")) {
                    sub.name = "V";
                }
                sub = sub.nodes[1];
            }
            const piff1 = replace(ast, start, newNames, false);
            const oldNames = [];
            sub = ast;
            let startCount = 0;
            while (sub.type === "sym" && (sub.name === "V")) {
                if (startCount++ >= start) {
                    oldNames.push(sub.nodes[0].name);
                }
                sub = sub.nodes[1];
            }
            let sub2 = astmgr.clone(this.propositions[piff1].value);
            sub = sub2;
            startCount = 0;
            while (sub.type === "sym" && (sub.name === "V")) {
                if (startCount++ >= start) {
                    oldNames.push(sub.nodes[0].name);
                }
                sub = sub.nodes[1];
            }
            astmgr.assign(sub, sub.nodes[1]); // vvvv(a>b) -> vvvv(b)
            const piff2 = replace(sub2, start, oldNames, true);
            lastP = this.deduct({
                deductionIdx: "v".repeat(start) + ".<>", conditionIdxs: [piff1, piff2], replaceValues: []
            });
            return lastP;
        };
        const replaceE = (ast, starts, newName) => {
            const wrapName = { type: "replvar", name: newName };
            const replaced = {
                type: "fn", name: "#rp", nodes: [
                    ast.nodes[1], ast.nodes[0], wrapName
                ]
            };
            let temp;
            lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "dE", conditionIdxs: [],
                replaceValues: [...starts, ...ast.nodes]
            });
            temp = lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "<.<>1", conditionIdxs: [lastP], replaceValues: []
            });
            lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "cva4", conditionIdxs: [], replaceValues: [
                    ...starts, ast, ast.nodes[0], wrapName,
                    { type: "sym", name: "~", nodes: [replaced] },
                    ast.nodes[0]
                ]
            });
            lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "c<a5", conditionIdxs: [lastP], replaceValues: []
            });
            lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "c<.a30", conditionIdxs: [lastP], replaceValues: []
            });
            temp = lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "cmp", conditionIdxs: [lastP, temp], replaceValues: []
            });
            lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "ca6", conditionIdxs: [], replaceValues: [
                    ...starts, ast,
                    { type: "sym", name: "V", nodes: [wrapName, { type: "sym", name: "~", nodes: [replaced] }] },
                    ast.nodes[0]
                ]
            });
            lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "c<.a30", conditionIdxs: [lastP], replaceValues: []
            });
            temp = lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "cmp", conditionIdxs: [lastP, temp], replaceValues: []
            });
            lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "cdE", conditionIdxs: [], replaceValues: [
                    ...starts, ast, wrapName, replaced
                ]
            });
            lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + "c<<.<>2", conditionIdxs: [lastP, temp], replaceValues: []
            });
            return lastP;
        };
        const replaceE2 = (ast, starts, newName) => {
            const piff1 = replaceE(ast, starts, newName);
            let sub = this.propositions[piff1].value;
            for (let i = 0; i < starts.length; i++) {
                sub = sub.nodes[1];
            }
            const piff2 = replaceE(sub.nodes[1], starts, ast.nodes[0].name);
            lastP = this.deduct({
                deductionIdx: "v".repeat(starts.length) + ".<>", conditionIdxs: [piff1, piff2], replaceValues: []
            });
            return lastP;
        };
        let lastAst = ast;
        let steps = [];
        const replaceVE = (newNames) => {
            let cursor = 0;
            while (cursor < newNames.length) {
                if (VEs[cursor]) {
                    let lastV;
                    for (let i = cursor; i < newNames.length; i++) {
                        if (!VEs[i]) {
                            lastV = i;
                            break;
                        }
                    }
                    lastV ??= newNames.length;
                    let changed = false;
                    for (let i = cursor; i < lastV; i++) {
                        if (oldNames[i] !== newNames[i]) {
                            changed = true;
                            break;
                        }
                    }
                    if (!changed) {
                        cursor = lastV;
                        continue;
                    }
                    lastP = replace2(lastAst, cursor, newNames.slice(cursor, lastV));
                    for (let i = cursor - 1; i >= 0; i--) {
                        lastP = this.deduct({
                            deductionIdx: "v".repeat(i) + ".<>r" + (VEs[i] ? "V" : "E"),
                            conditionIdxs: [lastP], replaceValues: []
                        });
                    }
                    cursor = lastV;
                    steps.push(lastP);
                    console.log(parser.stringify(this.propositions[lastP].value));
                    lastAst = this.propositions[lastP].value.nodes[1];
                }
                else {
                    if (oldNames[cursor] === newNames[cursor]) {
                        cursor++;
                        continue;
                    }
                    sub = lastAst;
                    let i = 0;
                    const subprefix = [];
                    while (i++ !== cursor) {
                        subprefix.push({ type: "replvar", name: newNames[i - 1] });
                        sub = sub.nodes[1];
                    }
                    lastP = replaceE2(sub, subprefix, newNames[cursor]);
                    for (let i = cursor - 1; i >= 0; i--) {
                        lastP = this.deduct({
                            deductionIdx: "v".repeat(i) + ".<>r" + (VEs[i] ? "V" : "E"),
                            conditionIdxs: [lastP], replaceValues: []
                        });
                    }
                    steps.push(lastP);
                    console.log(parser.stringify(this.propositions[lastP].value));
                    lastAst = this.propositions[lastP].value.nodes[1];
                    cursor++;
                }
            }
        };
        try {
            this.removePropositions();
            // replace2(ast, 0, replaced);
            // replaceE2(ast, replaced[0]);
            const tempNames = [];
            for (let i = 0; i < newNames.length; i++) {
                const pos = oldNames.indexOf(newNames[i]);
                tempNames.push((pos === -1 || pos < i) ? newNames[i] : uniq + newNames[i]);
            }
            replaceVE(tempNames);
            oldNames = tempNames;
            replaceVE(newNames);
            let frontier = steps[0];
            if (!frontier)
                throw TR("无任何变量被改名");
            for (let i = 1; i < steps.length; i++) {
                frontier = this.deduct({
                    deductionIdx: ".<>t", conditionIdxs: [frontier, steps[i]], replaceValues: []
                });
            }
            const ret = this.addMacro(name, from);
            this.propositions = oldP;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaIffTheorem(idx, replaceValues, name, from, allowIFFT_RP) {
        const d = this.generateDeduction(idx);
        if (!d)
            throw TR("推理规则不存在");
        if (d.conditions?.length)
            throw TR("条件推理规则( ⊢ ($$0 <> $$1))匹配失败");
        const conclusion = d.conclusion;
        if (conclusion.type !== "sym" || conclusion.name !== "<>")
            throw TR("条件推理规则( ⊢ ($$0 <> $$1))匹配失败");
        const [A, B] = conclusion.nodes;
        const [C, N] = replaceValues;
        if (N.type !== "replvar")
            throw TR("匹配序号参数必须为非负整数");
        let nth = Number(N.name);
        if (!isFinite(nth) || Math.floor(nth) !== nth || nth < 0)
            throw TR("匹配序号参数必须为非负整数");
        nth -= 1;
        const oldP = this.propositions;
        const R = astmgr.clone(C);
        assert.matchSubAndReplace(R, A, B, nth, /^\$/, false, 0, assert.getReplVarsType(R, {}, false));
        let A_B;
        let replacedNth = 0;
        // generate a <> b or VxVyVz a<>b
        const generate = (a, b, Vs = []) => {
            const prefix = "".padEnd(Vs.length, "v");
            if (astmgr.equal(a, b)) {
                // example: (~~a>~~b) <> (~~a > b), also count ~~a one time
                try {
                    const matched = {};
                    assert.match(a, A, /^\$/, false, matched, {}, []);
                    replacedNth++;
                }
                catch (e) { }
                // a == b : a <> a
                return this.deduct({ deductionIdx: prefix + ".<>i", conditionIdxs: [], replaceValues: [...Vs, a] });
            }
            try {
                const matched = {};
                assert.match(a, A, /^\$/, false, matched, {}, []);
                replacedNth++;
                if (nth === -1 || nth + 1 === replacedNth) {
                    return this.deduct({
                        deductionIdx: prefix + idx, conditionIdxs: [],
                        replaceValues: [...Vs, ...d.replaceNames.map(str => matched[str])]
                    });
                }
            }
            catch (e) { }
            if (!a.nodes?.length || a.nodes?.length !== b.nodes?.length) {
                throw TR("元推理函数中替换函数##rp执行失败");
            }
            if (a.type !== b.type || a.name !== b.name) {
                throw TR("元推理函数中替换函数##rp执行失败");
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
                        deductionIdx: prefix + ".<>rn", replaceValues: [],
                        conditionIdxs: [generate(a.nodes[0], b.nodes[0], Vs)],
                    });
                }
                if (a.name === "V") {
                    const vab = generate(a.nodes[1], b.nodes[1], [...Vs, a.nodes[0]]);
                    return this.deduct({
                        deductionIdx: prefix + ".<>rV", replaceValues: [],
                        conditionIdxs: [vab],
                    });
                }
                if (a.name === "E") {
                    const vab = generate(a.nodes[1], b.nodes[1], [...Vs, a.nodes[0]]);
                    return this.deduct({
                        deductionIdx: prefix + ".<>rE", replaceValues: [],
                        conditionIdxs: [vab],
                    });
                }
                if (a.name === "E!") {
                    if (!allowIFFT_RP) {
                        throw TR("还未解锁跨越量词E!进行替换的功能");
                    }
                    const vab = generate(a.nodes[1], b.nodes[1], [...Vs, a.nodes[0]]);
                    return this.deduct({
                        deductionIdx: prefix + ".<>rE!", replaceValues: [],
                        conditionIdxs: [vab],
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
    expandDefs(ast) {
        //expand
        if (ast.type === "sym") {
            if (ast.name === "E") {
                astmgr.assign(ast, {
                    type: "sym", name: "~", nodes: [{
                            type: "sym", name: "V", nodes: [
                                ast.nodes[0],
                                { type: "sym", name: "~", nodes: [ast.nodes[1]] }
                            ]
                        }]
                });
                this.expandDefs(ast);
            }
            if (ast.name === "&") {
                astmgr.assign(ast, {
                    type: "sym", name: "~", nodes: [{
                            type: "sym", name: ">", nodes: [
                                ast.nodes[0],
                                { type: "sym", name: "~", nodes: [ast.nodes[1]] }
                            ]
                        }]
                });
                this.expandDefs(ast);
            }
            if (ast.name === "|") {
                astmgr.assign(ast, {
                    type: "sym", name: ">", nodes: [
                        { type: "sym", name: "~", nodes: [ast.nodes[0]] },
                        ast.nodes[1],
                    ]
                });
                this.expandDefs(ast);
            }
            if (ast.name === "<>") {
                astmgr.assign(ast, {
                    type: "sym", name: "&", nodes: [
                        { type: "sym", name: ">", nodes: [ast.nodes[0], ast.nodes[1]] },
                        { type: "sym", name: ">", nodes: [ast.nodes[1], ast.nodes[0]] },
                    ]
                });
                this.expandDefs(ast);
            }
        }
        //reduce ~~a : a
        if (ast.type === "sym" && ast.name === "~") {
            const ast2 = ast.nodes[0];
            if (ast2.type === "sym" && ast2.name === "~") {
                astmgr.assign(ast, ast2.nodes[0]);
            }
        }
        //reduce ~a > ~b : b > a
        if (ast.type === "sym" && ast.name === ">") {
            const a = ast.nodes[0];
            const b = ast.nodes[1];
            if (a.type === "sym" && a.name === "~" && b.type === "sym" && b.name === "~") {
                astmgr.assign(ast, {
                    type: "sym", name: ">", nodes: [
                        b.nodes[0], a.nodes[0]
                    ]
                });
            }
        }
        if (!ast.nodes)
            return;
        for (const n of ast.nodes)
            this.expandDefs(n);
    }
}
//# sourceMappingURL=formalsystem.js.map