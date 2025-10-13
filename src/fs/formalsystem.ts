import { ASTMgr, AST, ReplvarMatchTable } from "./astmgr.js";
import { AssertionSystem, ReplvarTypeTable } from "./assertion.js";
import { Proof } from "./proof.js";
import { ASTParser } from "./astparser.js";
import { TR } from "../lang.js";
import { RuleParser, RuleTree } from "./metarule.js";
export type DeductionStep = { conditionIdxs: number[], deductionIdx: string, replaceValues: AST[] }
export type Deduction = { value: AST, conditions: AST[], conclusion: AST, replaceNames: string[], replaceTypes: { [replvar: string]: boolean }, from: string, steps?: DeductionStep[], tempvars: Set<string> };
export type MetaRule = { value: AST, conditions: AST[], conclusions: AST[], replaceNames: string[], conditionDeductionIdxs: number[], from: string };
export type MetaMacro = { inputs: string[], output: RuleTree, from: string };
export type Proposition = { value: AST, from: DeductionStep };
export type DeductInlineMode = "inline" | "deep" | null;
const astmgr = new ASTMgr;
const assert = new AssertionSystem;
const parser = new ASTParser;
const ruleparser = new RuleParser();
export class FormalSystem {
    deductions: { [key: string]: Deduction } = {};
    metaRules: { [key: string]: MetaRule } = {};
    metaMacro: { [key: string]: MetaMacro } = {};
    fastmetarules = "";
    disabledMetaRules = [];
    deductionReplNameRule: RegExp = /^\$/g;
    localNameRule: RegExp = /^\#/g;
    localReplacedNameRule: RegExp = /^\#\#/g;
    // replacedLocalNameRule: RegExp = /^&/g;
    // ignoreNfNameRule: RegExp = /^(&|#)/g;
    // fnParamNames = (n: number) => "#" + n;
    consts = new Set<string>();
    fns = new Set<string>();
    verbs = new Set<string>();
    propositions: Proposition[] = [];
    assert = assert;
    constructor() {
        this.assert.fns = this.fns;
        this.assert.verbs = this.verbs;
        this.assert.consts = this.consts;
    }
    private ast2deduction(ast: AST): Deduction {
        assert.checkGrammer(ast, "d");
        const [conditions, conclusions] = ast.nodes;
        const varLists: ReplvarTypeTable = {};
        const allReplvars = new Set<string>;
        const matchingReplvars = new Set<string>;
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
    private ast2metaRule(ast: AST): MetaRule {
        let grammarCheck = ast.type === "meta" && ast.name === "⊢M" && ast.nodes?.length === 2;
        if (!grammarCheck) throw TR("未找到元推理符号");
        const [conditions, conclusions] = ast.nodes;
        if (!conclusions.nodes?.length) throw TR("元推理符号后面没有结论");
        return {
            value: ast,
            conclusions: conclusions.nodes,
            conditions: conditions.nodes,
            replaceNames: [], conditionDeductionIdxs: [],
            from: ""
        };
    }
    getdependency(name: string, deductionIdx: string) {
        if (!deductionIdx) return false;
        const res: string[] = [];
        this.getAtomDeductionTokens(deductionIdx, res);
        return name === deductionIdx || res.includes(name);
    }
    removeDeduction(name: string) {
        if (!this.deductions[name]) throw TR("规则名称 ") + name + TR(" 不存在");
        // if (this.deductions[name].from.match(/$/)) throw "无法删除系统规则";
        for (const [n, d] of Object.entries(this.deductions)) {
            if (!d.steps) continue;
            if (name === n) continue;
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

        if (name.startsWith("dc")) {
            this.consts.delete(name.slice(2));
        }

        if (name.startsWith("df")) {
            this.fns.delete(name.slice(2));
        }

        if (name.startsWith("dv")) {
            this.verbs.delete(name.slice(2));
        }

        delete this.deductions[name];
        return true;
    }
    addDeduction(name: string, d: AST, from: string, macro?: DeductionStep[], tempvars?: Set<string>) {
        const deduction = this.ast2deduction(d);
        deduction.from = from;
        deduction.steps = macro;
        deduction.tempvars = tempvars ?? this.findLocalNamesInDeductionStep(macro);
        if (this.deductions[name]) throw TR("规则名称 ") + name + TR(" 已存在");
        this.deductions[name] = deduction;
        return name;
    }
    addMetaRule(name: string, m: AST, conditionDeductionIdxs: number[], replaceNames: string[], from: string) {
        const metaRule = this.ast2metaRule(m);
        metaRule.from = from;
        metaRule.conditionDeductionIdxs = conditionDeductionIdxs;
        metaRule.replaceNames = replaceNames;
        this.metaRules[name] = metaRule;
    }
    addMetaMacro(name: string, inputs: string[], output: RuleTree, from: string) {
        if (this.metaRules[name]) throw TR("元规则 ") + name + TR(" 已存在");
        for (const i of inputs) {
            if (i.startsWith("$$")) throw TR("元规则输入中不能包含以$$开头的变量");
        }
        const replaceInTree = (tree: RuleTree) => {
            if (tree.length === 1) {
                if (inputs.includes(tree[0])) {
                    tree[0] = "$$" + tree[0];
                }
            } else {
                for (let i = 1; i < tree.length; i++) {
                    replaceInTree(tree[i] as RuleTree);
                }
            }
        };
        replaceInTree(output);
        inputs = inputs.map(i => "$$" + i);
        this.metaMacro[name] = { inputs, output, from };
        const ast = parser.parse(inputs.join(",") + " ⊢M $$");
        for (const a of ast.nodes[0].nodes) {
            a.type = "rule";
        }
        ast.nodes[1].nodes[0].type = "rule";
        ast.nodes[1].nodes[0].name = ruleparser.stringify(output);
        this.addMetaRule(name, ast, inputs.map((e, i) => i), [], from);
    }
    private _hasRpFn(m: AST) {
        if (m.type === "fn" && m.name === "#rp") {
            return true;
        }
        if (!m.nodes) return false;
        for (const n of m.nodes) {
            if (this._hasRpFn(n)) return true;
        }
        return false;
    }
    addHypothese(m: AST, expandMode?: boolean) {
        m = astmgr.clone(m);
        assert.checkGrammer(m, "p");
        if (!expandMode && this._hasLocalNames(m)) throw TR("假设中不能出现以#号开头的局部变量");
        try {
            assert.expand(m, false);
        } catch (e) { throw TR("假设中") + e; }
        if (!expandMode && this._hasRpFn(m)) throw TR("假设中不能包含未化简的#rp函数，否则匹配机制将失效");
        this.propositions.push({ value: m, from: null });
        const dst = this.propositions.findIndex(e => e.from);
        if (dst !== -1) {
            this.moveProposition(this.propositions.length - 1, dst);
        }
        return this.propositions.length - 1;
    }
    // find #0 in ast
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
    // find ##0 in ast
    private findLocalNamesInAst(ast: AST, reg: RegExp, res = new Set<string>) {
        if (ast.type === "replvar" && ast.name.match(reg)) {
            res.add(ast.name); return res;
        }
        if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this.findLocalNamesInAst(n, reg, res);
            }
        }
        return res;
    }
    // find ##0 in macro
    findLocalNamesInDeductionStep(steps: DeductionStep[], res = new Set<string>) {
        if (!steps) return res;
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
    private replaceTempVar(ast: AST, tempvarTable: Set<string>) {
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
    private recoverTempVar(ast: AST, tempvarTable: Set<string>) {
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
    addMacro(name: string, from: string) {
        const propositionIdx = this.propositions.length - 1;
        let hypothesisAmount = this.propositions.findIndex(e => e.from);
        if (hypothesisAmount == -1) hypothesisAmount = this.propositions.length;
        if (propositionIdx < hypothesisAmount) throw TR("无有效定理推导步骤，创建宏推导失败");
        const conditions: AST[] = [];
        for (let i = 0; i < hypothesisAmount; i++) {
            conditions.push(this.propositions[i].value);
        }
        const conclusion = this.propositions[propositionIdx].value;
        if (this._hasLocalNames(conclusion)) {
            throw TR("局部变量不能出现在推理宏的结论中");
        }
        const macro: DeductionStep[] = [];
        const subTempvars = new Set<string>;
        for (let i = hypothesisAmount; i <= propositionIdx; i++) {
            for (const v of this.generateDeduction(this.propositions[i].from.deductionIdx).tempvars) {
                subTempvars.add(v);
            }
        }
        for (let i = hypothesisAmount; i <= propositionIdx; i++) {
            const step = this.propositions[i].from;
            macro.push({
                conditionIdxs: step.conditionIdxs.map(
                    cidx => cidx < hypothesisAmount ? cidx : cidx - i
                ),
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
    removePropositions(amount?: number) {
        if (!isFinite(amount)) {
            this.propositions = [];
        } else {
            while (amount--) {
                this.propositions.pop();
            }
        }
    }
    private _getNewIndex(i: number, j: number, k: number): number {
        if (k === i) {
            return j > i ? j - 1 : j;
        }
        if (i < j && k > i && k < j) {
            return k - 1;
        }
        if (i > j && k >= j && k < i) {
            return k + 1;
        }
        return k;
    }
    moveProposition(src: number, dst: number) {
        if (dst === -1) dst = this.propositions.length;
        if (src === dst || dst === src + 1) return;
        // 0 1 2 | 3 4 
        const hyps = this.propositions.findIndex(e => e.from);
        if (!this.propositions[src].from) {
            if (hyps !== -1 && dst > hyps) {
                const sv = this.propositions[src];
                sv.from = { conditionIdxs: [], replaceValues: [], deductionIdx: "" };
                try {
                    this.moveProposition(src, -1);
                    this.propositions.pop();
                } catch (e) {
                    delete sv.from;
                    throw TR("无法移动假设条件：假设须位于其它定理之前");
                }
                throw TR("被移动的假设条件被删除：假设须位于其它定理之前") + " - " + parser.stringify(sv.value);
            }
        } else if (dst < hyps) {
            throw TR("无法移动假设条件：假设须位于其它定理之前");
        }
        for (let i = Math.min(src, dst); i < this.propositions.length; i++) {
            const from = this.propositions[i]?.from;
            if (!from) continue;
            const ni = this._getNewIndex(src, dst, i);
            for (const j of from.conditionIdxs) {
                const nj = this._getNewIndex(src, dst, j);
                console.assert(nj !== ni);
                if (nj > ni) throw TR("非法移动：推出定理") + "p" + i + TR("所依赖的定理") + "p" + j + TR("无法调整至其后方");
            }
        }
        for (let i = Math.min(src, dst); i < this.propositions.length; i++) {
            const from = this.propositions[i]?.from;
            if (!from) continue;
            from.conditionIdxs = from.conditionIdxs.map(e => this._getNewIndex(src, dst, e));
        }
        if (dst > src) dst--;
        const moved = this.propositions.splice(src, 1)[0];
        if (dst === this.propositions.length) this.propositions.push(moved);
        else this.propositions.splice(dst, 0, moved);


    }
    isNameCanBeNewConst(name: string) {
        if (assert.isConst(name)) return `"${name}" ` + TR(`已有定义，无法重复定义`);
        this.consts.add(name);
        for (const [idx, d] of Object.entries(this.deductions)) {
            try {
                assert.checkGrammer(d.value, "d");
                assert.getReplVarsType(d.conclusion, {}, false);
            } catch (e) {
                this.consts.delete(name);
                return TR(`定义符号失败：`) + ` ${idx} : ` + e;
            }
        }
        for (const [idx, p] of this.propositions.entries()) {
            try {
                assert.checkGrammer(p.value, "p");
                assert.getReplVarsType(p.value, {}, false);
            } catch (e) {
                this.consts.delete(name);
                return TR(`定义符号失败：`) + ` p${idx} : ` + e;
            }
        }
        this.consts.delete(name);
        return true;
    }
    isNameCanBeNewFnOrVerb() {
        for (const [idx, d] of Object.entries(this.deductions)) {
            try {
                assert.checkGrammer(d.value, "d");
                assert.getReplVarsType(d.conclusion, {}, false);
            } catch (e) {
                throw TR(`定义符号失败：`) + ` ${idx} : ` + e;
            }
        }
        for (const [idx, p] of this.propositions.entries()) {
            try {
                assert.checkGrammer(p.value, "p");
                assert.getReplVarsType(p.value, {}, false);
            } catch (e) {
                throw TR(`定义符号失败：`) + ` p${idx} : ` + e;
            }
        }
        return true;
    }

    generateDeductionByToken(tree: RuleTree, name = ruleparser.stringify(tree)): Deduction {
        if (this.deductions[name]) return this.deductions[name];
        const unlocked = this.fastmetarules;
        const from = "元规则生成*";
        const cmd = tree[0];
        const fn = {
            "<": this.metaInvDeductTheorem,
            ">": this.metaDeductTheorem,
            "c": this.metaConditionTheorem,
            "e": this.metaExistTheorem,
            "v": unlocked.includes("v") ? this.metaConditionUniversalTheorem : unlocked.includes("q") ? this.metaQuantifyAxiomSchema : null,
            "u": this.metaUniversalTheorem,
        }[tree[0]];
        if (fn) {
            if (!unlocked.includes(cmd) && cmd !== "v") throw "null";
            const subRuleName = ruleparser.stringify(tree[1]);
            this.generateDeductionByToken(tree[1], subRuleName);
            return this.deductions[fn.bind(this)(subRuleName, from)];
        }
        if (tree[0] === ":") {
            if (!unlocked.includes(":")) throw "null";
            const d1name = ruleparser.stringify(tree[1]);
            const d2name = ruleparser.stringify(tree[2]);
            this.generateDeductionByToken(tree[1], d1name);
            this.generateDeductionByToken(tree[2], d2name);
            return this.deductions[this.metaCombineTheorem(d1name, d2name, from)];
        }
        if (tree.length === 1) {
            const dname = tree[0];
            let generated: string = null;
            if (unlocked.includes("#")) {
                generated ??= this.generateNatLiteralDef(dname);
                generated ??= this.generateNatLiteralOp(dname);
            }
            if (generated) return this.deductions[generated];
        }
        throw "null";
    }
    getDeductionTokens(name: string): RuleTree {
        return ruleparser.parse(name);
    }
    getAtomDeductionTokens(name: string, res: string[] = [], token = ruleparser.parse(name)) {
        if (token.length === 1) {
            res.push(token[0]);
        } else {
            for (let i = 1; i < token.length; i++) this.getAtomDeductionTokens("", res, token[i] as RuleTree);
        }
    }
    generateDeduction(name: string): Deduction {
        if (!name) return null;
        try {
            const tokens = ruleparser.parse(name);
            return this.generateDeductionByToken(tokens);
        } catch (e) {
            if (e === "null") return null;
            if (e === ",") throw TR(`使用元规则生成推理规则`) + name + TR(`时：意外出现了“,”`);
            throw TR(`使用元规则生成推理规则`) + name + TR(`时：`) + e;
        }
    }
    generateNatLiteralDef(name: string) {
        const n = name.match(/^d([1-9][0-9]+)$/);
        if (!n || !isFinite(Number(n[1]))) return;
        if (this.deductions[name]) return name;
        const num = Number(n[1]);
        return this.addDeduction(name, parser.parse(`⊢${num} =S(${num - 1})`), "算数符号定义");
    }
    generateNatLiteralOp(name: string, vnum = 0) {
        const vpre = "v".repeat(vnum);
        const vars = [];
        let V = "";
        for (let i = 0; i < vnum; i++) {
            vars.push({ type: "replvar", name: "$" + i });
            V += "V$" + i + ":";
        }
        const n = name.match(/^\.([1-9][0-9]*)([\+\*])([1-9][0-9]*)$/);
        if (!n || !isFinite(Number(n[1])) || !isFinite(Number(n[3]))) return;
        if (this.deductions[vpre + name]) return vpre + name;
        const a = Number(n[1]);
        const b = Number(n[3]);
        const op = n[2];
        const steps = [
            b > 1 ?
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "." + a + op + (b - 1) } :
                { conditionIdxs: [], replaceValues: [...vars, { type: "replvar", name: String(a) }], deductionIdx: vpre + "d" + op + "1" }
            ,
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

    deduct(step: DeductionStep, inlineMode?: DeductInlineMode | ((step: DeductionStep, conclusion: AST) => DeductInlineMode)) {
        const { conditionIdxs, deductionIdx, replaceValues } = step;
        const deduction = this.generateDeduction(deductionIdx);
        const errorMsg = TR(`规则 `) + deductionIdx + TR(` 推理失败:`);
        if (!deduction) throw errorMsg + TR("规则不存在");
        const { conditions, conclusion, replaceNames, steps, replaceTypes } = deduction;

        // firstly, match condition, get matchtable ( partial initially provided by users)

        let replacedVarTypeTable: ReplvarTypeTable = {};
        let matchTable: ReplvarMatchTable = Object.fromEntries(replaceNames.map(
            (replname: string, idx: number) => (
                assert.getReplVarsType(replaceValues[idx], replacedVarTypeTable, replaceTypes[replname]),
                [replname, replaceValues[idx]]
            )
        ));
        let assertions: AST[] = [];
        let assertionsFrom: number[] = [];
        for (const [conditionIdx, condition] of conditions.entries()) {
            const condPropIdx = conditionIdxs[conditionIdx];
            const condProp = this.propositions[condPropIdx];
            if (!condProp) throw errorMsg + TR(`第${conditionIdx + 1}个`) + TR(`条件对应的定理p`) + condPropIdx + TR(`不存在`);
            try {
                assert.match(condProp.value, condition, /^\$/, false, matchTable, replacedVarTypeTable, assertions);
                while (assertionsFrom.length < assertions.length) assertionsFrom.push(conditionIdx);
            } catch (e) {
                // match failed
                throw errorMsg + TR(`第${conditionIdx + 1}个`) + TR(`条件`) + e;
            }
        }

        // then replace replvars in assertions by matchtable, and check them

        for (const [idx, ass] of assertions.entries()) {
            const cas = astmgr.clone(ass);
            astmgr.replaceByMatchTable(cas, matchTable);
            // todo: how to get assert's type
            try { assert.assertUnwrap(cas, replacedVarTypeTable); } catch (e) {
                // assertion in condition failed (first layer must be T)
                throw errorMsg + TR(`第${assertionsFrom[idx] + 1}个`) + TR(`条件中:`) + e;
            }
        }

        // finally replace conclusion

        let replacedConclusion = astmgr.clone(conclusion);
        astmgr.replaceByMatchTable(replacedConclusion, matchTable);
        try {
            assert.checkGrammer(replacedConclusion, "p");
            // grammar in conclusion failed
        } catch (e) { throw TR("结论中出现语法错误：") + e }
        try { assert.expand(replacedConclusion, false); } catch (e) {
            // assertion in conclusion failed (can be T or U, only F to fail)
            throw errorMsg + TR(`结论中：`) + e;
        }

        // if it isn't macro or not inineMode, done

        let netInlineMode = inlineMode;
        if (typeof netInlineMode === "function") netInlineMode = netInlineMode(step, replacedConclusion);
        if (!steps?.length || !netInlineMode) {
            return this.propositions.push({ value: replacedConclusion, from: step }) - 1;
        }

        // if it is macro and inline, expand substeps 

        let startPropositions = this.propositions.length;
        let propsOffset = [];

        // find outter tempvars
        let tempvars = new Set<string>;
        Object.values(matchTable).forEach(v => this.findLocalNamesInAst(v, this.localNameRule, tempvars));

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
                this.recoverTempVar(replaced, tempvars);
                this.replaceTempVar
                astmgr.replaceByMatchTable(replaced, matchTable);
                return replaced;
            });
            let firstPos = this.propositions.length - 1;
            let lastPos: number;
            try {
                lastPos = this.deduct({ deductionIdx: substep.deductionIdx, replaceValues, conditionIdxs: replacedConditionIdxs }, netInlineMode === "deep" ? inlineMode : null);
            } catch (e) {
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
    expandMacroWithProp(propositionIdx: number) {
        const p = this.propositions[propositionIdx];
        if (!p.from) throw TR("该定理为假设，无推理步骤可展开");
        const { deductionIdx, conditionIdxs, replaceValues } = p.from;
        if (!this.deductions[deductionIdx]) this.deductions[deductionIdx] = this.generateDeduction(deductionIdx);
        const from = this.deductions[deductionIdx].from;
        if (!this.deductions[deductionIdx].steps) throw TR(`该定理由来自<`) + TR(deductionIdx[0] === "v" ? TR("一阶逻辑公理模式") : from) + TR(`>的原子推理规则得到，无子步骤`);
        const hyps = conditionIdxs.map(c => this.propositions[c].value);
        this.removePropositions();
        // expandMode set true to skip local var check in addHypothese
        hyps.forEach(h => this.addHypothese(h, true));
        this.deduct({
            deductionIdx, conditionIdxs: hyps.map((v, idx) => idx), replaceValues
        }, "inline");
    }
    inlineMacroInProp(propositionIdx: number) {
        const p = this.propositions[propositionIdx];
        if (!p.from) throw TR("该定理为假设，无推理步骤可展开");
        const { deductionIdx, conditionIdxs, replaceValues } = p.from;
        if (!this.deductions[deductionIdx]) this.deductions[deductionIdx] = this.generateDeduction(deductionIdx);
        if (!this.deductions[deductionIdx].steps) throw TR(`该定理由来自<`) + TR(this.deductions[deductionIdx].from) + TR(`>的原子推理规则得到，无子步骤`);
        const suivant: Proposition[] = [];
        while (true) {
            const p1 = this.propositions.pop();
            if (p1 !== p) suivant.unshift(p1);
            if (p1 === p) { break; }
        }
        const before = this.propositions.length;
        this.deduct({
            deductionIdx, conditionIdxs, replaceValues
        }, "inline");
        const offset = this.propositions.length - before - 1;
        while (true) {
            const p1 = suivant.shift();
            if (!p1) break;
            if (!p1.from) continue;
            this.propositions.push(p1);
            p1.from.conditionIdxs = p1.from.conditionIdxs.map(id => id < propositionIdx ? id : id + offset);
        }
    }
    expandMacroWithDefaultValue(deductionIdx: string, inlineMode: DeductInlineMode = "inline", expandAxiom?: boolean) {
        const d = this.deductions[deductionIdx] || this.generateDeduction(deductionIdx);
        if (!d) throw TR(`推理规则 `) + deductionIdx + TR(` 不存在`);
        if (!expandAxiom && !d.steps) throw TR(`无法展开原子推理规则`);
        this.removePropositions();
        d.conditions.forEach(dcond => this.addHypothese(dcond));
        this.deduct({
            deductionIdx, conditionIdxs: d.conditions.map((v, idx) => idx),
            replaceValues: d.replaceNames.map(str => ({ type: "replvar", name: str }))
        }, inlineMode);
    }
    private _findReplNameInRule(deductionIdx: string) {
        const d = this.deductions[deductionIdx];
        const p = new Set<string>;
        for (const c of d.conditions) astmgr.getVarNames(c, p, /^\$/);
        astmgr.getVarNames(d.conclusion, p, /^\$/);
        return p;
    }
    private _findNewReplName(deductionIdx: string, p = new Set<string>) {
        let name = "$0", i = 0;
        if (deductionIdx) {
            const d = this.deductions[deductionIdx];
            for (const c of d.conditions) astmgr.getVarNames(c, p, /^\$/);
            astmgr.getVarNames(d.conclusion, p, /^\$/);
        }
        while (p.has(name)) {
            name = "$" + (i++);
        }
        return { type: "replvar", name };
    }
    metaQuantifyAxiomSchema(deductionIdx: string, from: string) {
        const d = this.generateDeduction(deductionIdx);
        if (!d) throw TR(`推理规则 `) + deductionIdx + TR(` 不存在`);
        if (d.conditions?.length) throw TR("无法匹配带条件的推理规则");
        if (d.steps?.length) throw TR("无法匹配非公理推理规则");
        if (this.deductions["v" + deductionIdx]) return "v" + deductionIdx;

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

    metaExistTheorem(idx: string, from: string) {
        const d = this.generateDeduction(idx);
        if (d.conditions.length !== 1) throw TR("匹配条件推理规则($$0 ⊢ $$1)失败");
        if (this.deductions["e" + idx]) return "e" + idx;
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
            }); pidx++;
            const vd = this.generateDeduction(("v>" + idx).replace("><", ""));
            this.deduct({
                deductionIdx: ("v>" + idx).replace("><", ""),
                replaceValues: vd.replaceNames.map(e => ({ type: "replvar", name: e })),
                conditionIdxs: []
            }); pidx++;
            this.deduct({
                deductionIdx: ".Emp",
                replaceValues: [],
                conditionIdxs: [1, 0]
            }); pidx++;
            const ret = this.addMacro("e" + idx, from);
            this.propositions = oldP;
            return ret;
        } catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaTransitTheorem(idx: string, from: string, mode: string) {
        const d = this.generateDeduction(idx);
        // |- a<>b  =>  x<>a |- x<>b
        if (d.conditions.length !== 0) throw TR("匹配条件推理规则($$0 ⊢ $$1)失败");
        // todo:
        // if (this.deductions["e" + idx]) return "e" + idx;
        const oldP = this.propositions;
        const sym = d.conclusion.name;
        try {
            this.removePropositions();
            const s = this._findNewReplName(idx);
            let pidx = 0;
            // |- Ea   |- v(a>b)  |- Ea > Eb
            this.addHypothese({ type: "sym", name: sym, nodes: [s, d.conclusion.nodes[0]] }); pidx++;
            this.deduct({
                deductionIdx: idx,
                replaceValues: d.replaceNames.map(e => ({ type: "replvar", name: e })),
                conditionIdxs: []
            }); pidx++;
            this.deduct({
                deductionIdx: sym === ">" ? ".t" : sym === "<>" ? ".<>t" : sym === "=" ? ".=t" : '',
                replaceValues: [],
                conditionIdxs: [0, 1]
            }); pidx++;
            const ret = this.addMacro("e" + idx, from);
            this.propositions = oldP;
            return ret;
        } catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaConditionUniversalTheorem(idx: string, from: string) {
        // mp
        if (this.deductions["v" + idx]) return "v" + idx;
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
        const generate = (condMode: boolean, idx?: number) => {
            idx ??= d.steps.length - 1 + d.conditions.length;
            const step = d.steps[idx - d.conditions.length];
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            if (!condMode) {
                // avoid repeated deductions on the same prop (here reaching hyps are not possible)
                if (isFinite(offsetTable[idx])) return offsetTable[idx];
                // mp, axiom or macros
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: step.replaceValues,
                    conditionIdxs: step.conditionIdxs.map(id => generate(false, id >= 0 ? id : idx + id))
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx])) return offsetCondTable[idx];
            return offsetCondTable[idx] = this.deduct({
                deductionIdx: this.metaConditionUniversalTheorem(sdidx, ""),
                replaceValues: sd.conditions.length ? step.replaceValues : [s, ...step.replaceValues],
                conditionIdxs: step.conditionIdxs.map(id => generate(true, id >= 0 ? id : idx + id))
            });
        }
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
        } catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaUniversalTheorem(idx: string, from: string) {
        if (this.deductions["u" + idx]) return "u" + idx;
        const d = this.generateDeduction(idx);
        if (!d) throw TR("条件中的推理规则不存在");
        if (!d.conditions.length) return this.metaConditionUniversalTheorem(idx, from);
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
        const replvarTable: ReplvarMatchTable = {};
        const generate = (condMode: boolean, idx?: number) => {
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
                if (isFinite(offsetTable[idx])) return offsetTable[idx];
                // mp, axiom or macros
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: stepReplaceValues,
                    conditionIdxs: step.conditionIdxs.map(id => generate(false, id >= 0 ? id : idx + id))
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx])) return offsetCondTable[idx];
            return offsetCondTable[idx] = this.deduct({
                deductionIdx: this.metaConditionUniversalTheorem(sdidx, "元规则生成*"),
                replaceValues: sd.conditions.length ? stepReplaceValues : [s, ...stepReplaceValues],
                conditionIdxs: step.conditionIdxs.map(id => generate(true, id >= 0 ? id : idx + id))
            });
        }
        const oldP = this.propositions;
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => {
                const newHyp = { type: "fn", name: "#nf", nodes: [c, s] };
                this.addHypothese(newHyp);
                try { assert.match(this.propositions[id].value, c, /^\$/, false, replvarTable, {}, []); } catch (e) {
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
        } catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaNewConstant(replaceValues: AST[], from: string) {
        const [constAst, varAst, exprAst] = replaceValues;
        if (constAst.type !== "replvar") throw TR("$$0只能为纯变量名");
        if (constAst.name.match(/[A-Z]/)) throw TR(`自定义符号中不能有大写字母`);
        if (constAst.name.startsWith("$")) throw TR("以$开头的变量名称被系统保留");
        if (constAst.name.startsWith("#")) throw TR("以#开头的变量名称被系统保留");
        const constCheckRes = this.isNameCanBeNewConst(constAst.name);
        if (constCheckRes !== true) throw TR("匹配条件##newconst($$0)时：") + constCheckRes;
        if (this.fns.has(constAst.name)) throw TR("匹配条件##newconst($$0)时：$$0已有定义");
        const deduction = astmgr.clone(this.metaRules["c"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": constAst,
            "$$1": varAst,
            "$$2": exprAst
        }
        astmgr.replaceByMatchTable(deduction, replTable);
        const R = astmgr.clone(exprAst);
        astmgr.replace(R, varAst, constAst);
        if (assert.nf(constAst.name, R) !== -1) throw TR("定义的常量没在结论中出现");
        astmgr.assign(deduction.nodes[1].nodes[0].nodes[1], R);
        let d: string;
        try {
            this.consts.add(constAst.name);
            d = this.addDeduction("dc" + constAst.name, deduction, from);
            if (this.deductions[d].replaceNames.length) throw TR("不能包含$开头的替代项");
        } catch (e) {
            if (d) delete this.deductions[d];
            this.consts.delete(constAst.name);
            throw e;
        }
        return d;
    }
    metaNewFunction(replaceValues: [AST, AST, AST, AST[]], from: string) {
        const [fnAst, varAst, exprAst, paramAsts] = replaceValues;
        if (!paramAsts.length) throw null;
        if (fnAst.type !== "replvar") throw TR("$$0只能为纯变量名");
        if (fnAst.name.match(/[A-Z]/)) throw TR(`自定义符号中不能有大写字母`);
        if (fnAst.name.startsWith("#")) throw TR("以#开头的函数被系统保留");
        if (fnAst.name.startsWith("$")) throw TR("以$开头的函数被系统保留");
        const fnCheckRes = this.fns.has(fnAst.name) || this.verbs.has(fnAst.name);
        if (fnCheckRes) throw TR(`匹配条件##newfn($$0)时：$$0已有定义`);
        const deduction = astmgr.clone(this.metaRules["f"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": fnAst,
            "$$2": varAst,
            "$$3": exprAst
        }
        const wrapVs = (ast: AST) => {
            console.assert(ast.name === "V");
            let first = true;
            for (const p of paramAsts) {
                const n = p.name;
                if (p.type !== "replvar") throw TR("函数的参数必须是变量");
                if (assert.isConst(n)) throw TR("函数的参数不能是常量");
                if (first) {
                    astmgr.assign(ast.nodes[0], p);
                    first = false;
                    continue;
                }
                astmgr.assign(ast, { type: "sym", name: "V", nodes: [p, ast] });
            }
        }
        astmgr.replaceByMatchTable(deduction, replTable);
        const R = astmgr.clone(exprAst);
        if (assert.nf(varAst.name, R) !== -1) throw TR("定义的函数表达式没在结论中出现");
        astmgr.replace(R, varAst, { type: "fn", name: fnAst.name, nodes: paramAsts });
        astmgr.assign(deduction.nodes[1].nodes[0].nodes[1].nodes[1], R);
        wrapVs(deduction.nodes[1].nodes[0].nodes[0]);
        wrapVs(deduction.nodes[1].nodes[0].nodes[1]);
        let d: string;
        try {
            this.fns.add(fnAst.name);
            this.isNameCanBeNewFnOrVerb();
            d = this.addDeduction("df" + fnAst.name, deduction, from);
            if (this.deductions[d].replaceNames.length) throw TR("不能包含$开头的替代项");
        } catch (e) {
            if (d) delete this.deductions[d];
            this.fns.delete(fnAst.name);
            throw e;
        }
        return d;
    }
    metaNewVerb(replaceValues: [AST, AST, AST[]], from: string) {
        const [fnAst, exprAst, paramAsts] = replaceValues;
        if (!paramAsts.length) throw null;
        if (fnAst.type !== "replvar") throw TR("$$0只能为纯变量名");
        if (fnAst.name.match(/[A-Z]/)) throw TR(`自定义符号中不能有大写字母`);
        if (fnAst.name.startsWith("#")) throw TR("以#开头的函数被系统保留");
        if (fnAst.name.startsWith("$")) throw TR("以$开头的函数被系统保留");
        const fnCheckRes = this.fns.has(fnAst.name) || this.verbs.has(fnAst.name);
        if (fnCheckRes) throw TR(`匹配条件##newfn($$0)时：$$0已有定义`);
        const deduction = astmgr.clone(this.metaRules["prd"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": fnAst,
            "$$2": exprAst
        }
        const wrapVs = (ast: AST) => {
            console.assert(ast.name === "V");
            let first = true;
            for (const p of paramAsts) {
                const n = p.name;
                if (p.type !== "replvar") throw TR("函数的参数必须是变量");
                if (assert.isConst(n)) throw TR("函数的参数不能是常量");
                if (first) {
                    astmgr.assign(ast.nodes[0], p);
                    first = false;
                    continue;
                }
                astmgr.assign(ast, { type: "sym", name: "V", nodes: [p, ast] });
            }
        }
        astmgr.replaceByMatchTable(deduction, replTable);
        astmgr.assign(deduction.nodes[1].nodes[0].nodes[1].nodes[0], { type: "fn", name: fnAst.name, nodes: paramAsts });
        wrapVs(deduction.nodes[1].nodes[0]);

        let d: string;
        try {
            this.verbs.add(fnAst.name);
            this.isNameCanBeNewFnOrVerb();
            d = this.addDeduction("dv" + fnAst.name, deduction, from);
            if (this.deductions[d].replaceNames.length) throw TR("不能包含$开头的替代项");
        } catch (e) {
            if (d) delete this.deductions[d];
            this.verbs.delete(fnAst.name);
            throw e;
        }
        return d;
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
    metaConditionTheorem(idx: string, from: string) {
        // mp
        if (this.deductions["c" + idx]) return "c" + idx;
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
            } catch (e) {
                this.propositions = oldP;
                throw e;
            }
        }
        // ...A |- B
        const offsetTable = [];
        const offsetCondTable = [];
        const generate = (condMode: boolean, idx?: number) => {
            idx ??= d.steps.length - 1 + d.conditions.length;
            const step = d.steps[idx - d.conditions.length];
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            if (!condMode) {
                // avoid repeated deductions on the same prop (here reaching hyps are not possible)
                if (isFinite(offsetTable[idx])) return offsetTable[idx];
                // mp, axiom or macros
                offsetTable[idx] = this.deduct({
                    deductionIdx: sdidx, replaceValues: step.replaceValues,
                    conditionIdxs: step.conditionIdxs.map(id => generate(false, id >= 0 ? id : idx + id))
                });
                return offsetTable[idx];
            }
            // avoid repeated deductions on the same prop (here includes hyps)
            if (isFinite(offsetCondTable[idx])) return offsetCondTable[idx];
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
        }
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
        } catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaDeductTheorem(idx: string, from: string) {
        if (idx[0] === "<") { this.generateDeduction(idx.slice(1)); return idx.slice(1); }
        if (this.deductions[">" + idx]) return ">" + idx;
        const d = this.generateDeduction(idx);
        // mp, axiom, |- A : error
        if (!d.conditions.length) {
            throw TR("推理规则不包含假设，无法与条件匹配");
        }
        if (idx === "mp") throw TR("元推理结论 >mp 为 (($0 > $1) ⊢ ($0 > $1))，假设与结论相同");
        // ...A, B |- C
        let offsetTable = [];
        let offsetCondTable = [];
        let s: AST; // condAst
        const generate = (condMode: boolean, idx?: number) => {
            idx ??= d.steps.length - 1 + d.conditions.length;
            const step = d.steps[idx - d.conditions.length];
            const sdidx = step?.deductionIdx;
            const sd = this.generateDeduction(sdidx);
            if (!condMode) {
                // avoid repeated deductions on the same prop
                if (isFinite(offsetTable[idx])) return offsetTable[idx];
                // here if reaching hyp B, roll back
                if (!step) {
                    return -1;
                }
                // mp, axiom or macros, if rely on hyp B, roll back recursively
                const state = [offsetTable.slice(0), this.propositions.slice(0)];
                const condIdxs: number[] = [];
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
            if (isFinite(offsetCondTable[idx])) return offsetCondTable[idx];
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
        }
        const oldP = this.propositions;
        try {
            this.removePropositions();
            d.conditions.forEach((c, id) => {
                if (id !== d.conditions.length - 1) {
                    this.addHypothese(c);
                    offsetTable.push(id);
                } else {
                    s = c;
                }
            });
            generate(true);
            const ret = this.addMacro(">" + idx, from);
            this.propositions = oldP;
            return ret;
        } catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaInvDeductTheorem(idx: string, from: string) {
        // >a => a
        if (idx[0] === ">") { this.generateDeduction(idx.slice(1)); return idx.slice(1); }
        // a => <a
        if (this.deductions["<" + idx]) return "<" + idx;
        const d = this.generateDeduction(idx);
        const oldP = this.propositions;
        const conclusion = d.conclusion;
        if (conclusion.type !== "sym" || conclusion.name !== ">") throw TR("条件推理规则(...$$0 ⊢ ($$1 > $$2))匹配失败");
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
        } catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaCompleteTheorem(ast: AST, name: string, from: string) {
        const proof = new Proof(this);
        const p = this.propositions;
        try {
            this.propositions = [];
            proof.prove(ast);
            this.addMacro(name, from);
            this.propositions = p;
        } catch (e) {
            this.propositions = p;
            throw e;
        }
        return name;
    }
    metaCombineTheorem(idx1: string, idx2: string, from: string) {
        const name = ":" + idx1 + "," + idx2;
        if (this.deductions[name]) return name;
        const d1 = this.generateDeduction(idx1);
        const d2 = this.generateDeduction(idx2);
        if (!d2.conditions.length) throw TR("匹配条件推理规则($$1b, ...$$2 ⊢ $$3)失败");
        const oldP = this.propositions;
        try {
            this.removePropositions();
            d1.conditions.forEach((c, id) => this.addHypothese(c));
            const matchTable: ReplvarMatchTable = {};
            const replacedVarTypeTable: ReplvarTypeTable = assert.getReplVarsType(d1.conclusion, {}, false);
            assert.match(d1.conclusion, d2.conditions[0], /^\$/, false, matchTable, replacedVarTypeTable, []);
            const d2_conds = [];
            for (let i = 1; i < d2.conditions.length; i++) {
                const R = astmgr.clone(d2.conditions[i]);
                astmgr.replaceByMatchTable(R, matchTable);
                d2_conds.push(this.addHypothese(R));
            }
            const p1 = this.deduct({
                deductionIdx: idx1, conditionIdxs: d1.conditions.map((v, id) => id),
                replaceValues: d1.replaceNames.map(str => ({ type: "replvar", name: str }))
            });
            const replNames = this._findReplNameInRule(idx1);
            const p2 = this.deduct({
                deductionIdx: idx2, conditionIdxs: [p1, ...d2_conds],
                replaceValues: d2.replaceNames.map(str => {
                    const n = this._findNewReplName("", replNames);
                    replNames.add(n.name);
                    return n;
                })
            });
            const ret = this.addMacro(name, from);
            this.propositions = oldP;
            return ret;
        } catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
    metaIffTheorem(idx: string, replaceValues: AST[], name: string, from: string, allowIFFT_RP: boolean) {
        const d = this.generateDeduction(idx);
        if (!d) throw TR("推理规则不存在");
        if (d.conditions?.length) throw TR("条件推理规则( ⊢ ($$0 <> $$1))匹配失败");
        const conclusion = d.conclusion;
        if (conclusion.type !== "sym" || conclusion.name !== "<>") throw TR("条件推理规则( ⊢ ($$0 <> $$1))匹配失败");
        const [A, B] = conclusion.nodes;
        const [C, N] = replaceValues;
        if (N.type !== "replvar") throw TR("匹配序号参数必须为非负整数");
        let nth = Number(N.name);
        if (!isFinite(nth) || Math.floor(nth) !== nth || nth < 0) throw TR("匹配序号参数必须为非负整数");
        nth -= 1;
        const oldP = this.propositions;
        const R = astmgr.clone(C);
        assert.matchSubAndReplace(R, A, B, nth, /^\$/, false, 0, assert.getReplVarsType(R, {}, false));
        let A_B: number;
        let replacedNth = 0;
        // generate a <> b or VxVyVz a<>b
        const generate = (a: AST, b: AST, Vs: AST[] = []) => {
            const prefix = "".padEnd(Vs.length, "v");
            if (astmgr.equal(a, b)) {
                // example: (~~a>~~b) <> (~~a > b), also count ~~a one time
                try {
                    const matched: ReplvarMatchTable = {};
                    assert.match(a, A, /^\$/, false, matched, {}, []);
                    replacedNth++;
                } catch (e) { }
                // a == b : a <> a
                return this.deduct({ deductionIdx: prefix + ".<>i", conditionIdxs: [], replaceValues: [...Vs, a] });
            }
            try {
                const matched: ReplvarMatchTable = {};
                assert.match(a, A, /^\$/, false, matched, {}, []);
                replacedNth++;
                if (nth === -1 || nth + 1 === replacedNth) {
                    return this.deduct({
                        deductionIdx: prefix + idx, conditionIdxs: [],
                        replaceValues: [...Vs, ...d.replaceNames.map(str => matched[str])]
                    });
                }
            } catch (e) { }
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
        }
        try {
            this.removePropositions();
            generate(C, R);
            const ret = this.addMacro(name, from);
            this.propositions = oldP;
            return ret;
        } catch (e) {
            this.propositions = oldP;
            throw e;
        }
    }
}