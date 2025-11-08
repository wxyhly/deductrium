import { ASTMgr } from "./astmgr.js";
import { AssertionSystem } from "./assertion.js";
import { Proof } from "./proof.js";
import { ASTParser } from "./astparser.js";
import { TR } from "../lang.js";
import { ConstrainSolver, RuleParser } from "./metarule.js";
const astmgr = new ASTMgr;
const assert = new AssertionSystem;
const parser = new ASTParser;
const ruleparser = new RuleParser();
export class FormalSystem {
    deductions = {};
    metaRules = {};
    metaMacro = {};
    fastmetarules = "";
    disabledMetaRules = [];
    deductionReplNameRule = /^\$/g;
    localNameRule = /^\#/g;
    localReplacedNameRule = /^\#\#/g;
    // replacedLocalNameRule: RegExp = /^&/g;
    // ignoreNfNameRule: RegExp = /^(&|#)/g;
    // fnParamNames = (n: number) => "#" + n;
    consts = new Set();
    fns = new Set();
    verbs = new Set();
    propositions = [];
    assert = assert;
    constructor() {
        this.assert.fns = this.fns;
        this.assert.verbs = this.verbs;
        this.assert.consts = this.consts;
    }
    ast2deduction(ast) {
        assert.checkGrammer(ast, "d");
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
        const res = [];
        this.getAtomDeductionTokens(deductionIdx, res);
        return name === deductionIdx || res.includes(name);
    }
    removeDeduction(name) {
        if (!this.deductions[name])
            throw TR("规则名称 ") + name + TR(" 不存在");
        if (this.getDeductionTokens(name).length > 1)
            return false; // this is composed, ignore it
        const composedDs = [];
        for (const [n, d] of Object.entries(this.deductions)) {
            if (!d.steps)
                continue;
            if (name === n)
                continue;
            if (this.getDeductionTokens(n).length > 1) {
                if (this.getdependency(name, n))
                    composedDs.push(n);
                continue;
            }
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
        for (const d of composedDs) {
            delete this.deductions[d];
        }
        delete this.deductions[name];
        return true;
    }
    renameDeduction(oldname, newname) {
        if (this.getDeductionTokens(oldname).length > 1 || this.getDeductionTokens(newname).length > 1)
            throw TR("无法重命名快速元规则");
        if (oldname.match(/^[mad\.]/)) {
            throw TR("无法重命名系统规则");
        }
        if (!this.deductions[oldname])
            throw TR("规则名称 ") + oldname + TR(" 不存在");
        if (this.deductions[newname])
            throw TR("规则名称 ") + newname + TR(" 已存在");
        const composedDs = [];
        for (const [n, d] of Object.entries(this.deductions)) {
            if (!d.steps)
                continue;
            if (oldname === n)
                continue;
            if (this.getDeductionTokens(n).length > 1) {
                if (this.getdependency(oldname, n)) {
                    composedDs.push(n);
                }
                continue;
            }
            for (const s of d.steps) {
                if (this.getdependency(oldname, s.deductionIdx)) {
                    const tr = this.getDeductionTokens(s.deductionIdx);
                    ruleparser.replaceNameByName(tr, oldname, newname);
                    s.deductionIdx = ruleparser.stringify(tr);
                }
            }
        }
        for (const [n, p] of this.propositions.entries()) {
            const s = p.from;
            if (!s)
                continue;
            if (this.getdependency(oldname, s.deductionIdx)) {
                const tr = this.getDeductionTokens(s.deductionIdx);
                ruleparser.replaceNameByName(tr, oldname, newname);
                s.deductionIdx = ruleparser.stringify(tr);
            }
        }
        for (const d of composedDs) {
            delete this.deductions[d];
        }
        this.deductions[newname] = this.deductions[oldname];
        delete this.deductions[oldname];
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
    addMetaMacro(name, inputs, output, from) {
        if (this.metaRules[name])
            throw TR("元规则 ") + name + TR(" 已存在");
        for (const i of inputs) {
            if (i.startsWith("$$"))
                throw TR("元规则输入中不能包含以$$开头的变量");
        }
        const replaceInTree = (tree) => {
            if (tree.length === 1) {
                if (inputs.includes(tree[0])) {
                    tree[0] = "$$" + tree[0];
                }
            }
            else {
                for (let i = 1; i < tree.length; i++) {
                    replaceInTree(tree[i]);
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
        assert.checkGrammer(m, "p");
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
        this.propositions.push({ value: m, from: null });
        const dst = this.propositions.findIndex(e => e.from);
        if (dst !== -1) {
            this.moveProposition(this.propositions.length - 1, dst);
        }
        return this.propositions.length - 1;
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
            ast.name = ast.name === "#" ? "##" : ast.name.replace(/^#([^#].*)$/, "##$1");
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
            // special case: # -> ## -> ###
            ast.name = ast.name === "###" ? "#" : ast.name.replace(/^##(.+)$/, "#$1");
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
    _getNewIndex(i, j, k) {
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
    moveProposition(src, dst) {
        if (dst === -1)
            dst = this.propositions.length;
        if (src === dst || dst === src + 1)
            return;
        // 0 1 2 | 3 4 
        const hyps = this.propositions.findIndex(e => e.from);
        if (!this.propositions[src].from) {
            if (hyps !== -1 && dst > hyps) {
                const sv = this.propositions[src];
                sv.from = { conditionIdxs: [], replaceValues: [], deductionIdx: "" };
                try {
                    this.moveProposition(src, -1);
                    this.propositions.pop();
                }
                catch (e) {
                    delete sv.from;
                    throw TR("无法移动假设条件：假设须位于其它定理之前");
                }
                throw TR("被移动的假设条件被删除：假设须位于其它定理之前") + " - " + parser.stringify(sv.value);
            }
        }
        else if (dst < hyps) {
            throw TR("无法移动假设条件：假设须位于其它定理之前");
        }
        for (let i = Math.min(src, dst); i < this.propositions.length; i++) {
            const from = this.propositions[i]?.from;
            if (!from)
                continue;
            const ni = this._getNewIndex(src, dst, i);
            for (const j of from.conditionIdxs) {
                const nj = this._getNewIndex(src, dst, j);
                console.assert(nj !== ni);
                if (nj > ni)
                    throw TR("非法移动：推出定理") + "p" + i + TR("所依赖的定理") + "p" + j + TR("无法调整至其后方");
            }
        }
        for (let i = Math.min(src, dst); i < this.propositions.length; i++) {
            const from = this.propositions[i]?.from;
            if (!from)
                continue;
            from.conditionIdxs = from.conditionIdxs.map(e => this._getNewIndex(src, dst, e));
        }
        if (dst > src)
            dst--;
        const moved = this.propositions.splice(src, 1)[0];
        if (dst === this.propositions.length)
            this.propositions.push(moved);
        else
            this.propositions.splice(dst, 0, moved);
    }
    isNameCanBeNewConst(name) {
        if (assert.isConst(name))
            return `"${name}" ` + TR(`已有定义，无法重复定义`);
        this.consts.add(name);
        for (const [idx, d] of Object.entries(this.deductions)) {
            try {
                assert.checkGrammer(d.value, "d");
                assert.getReplVarsType(d.conclusion, {}, false);
            }
            catch (e) {
                this.consts.delete(name);
                return TR(`定义符号失败：`) + ` ${idx} : ` + e;
            }
        }
        for (const [idx, p] of this.propositions.entries()) {
            try {
                assert.checkGrammer(p.value, "p");
                assert.getReplVarsType(p.value, {}, false);
            }
            catch (e) {
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
            }
            catch (e) {
                throw TR(`定义符号失败：`) + ` ${idx} : ` + e;
            }
        }
        for (const [idx, p] of this.propositions.entries()) {
            try {
                assert.checkGrammer(p.value, "p");
                assert.getReplVarsType(p.value, {}, false);
            }
            catch (e) {
                throw TR(`定义符号失败：`) + ` p${idx} : ` + e;
            }
        }
        return true;
    }
    generateDeductionByToken(tree, name = ruleparser.stringify(tree)) {
        if (this.deductions[name])
            return this.deductions[name];
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
            if (!unlocked.includes(cmd) && cmd !== "v")
                throw "null";
            const subRuleName = ruleparser.stringify(tree[1]);
            this.generateDeductionByToken(tree[1], subRuleName);
            return this.deductions[fn.bind(this)(subRuleName, from)];
        }
        if (tree[0] === ":") {
            if (!unlocked.includes(":"))
                throw "null";
            let tempvar;
            const d1names = tree.slice(1).map(t => (tempvar = ruleparser.stringify(t),
                tempvar !== "#" ? this.generateDeductionByToken(t, tempvar) : null,
                tempvar));
            const d2name = d1names.pop();
            return this.deductions[this.metaCombineTheorem(d1names, d2name, from)];
        }
        if (tree.length === 1) {
            const dname = tree[0];
            let generated = null;
            if (unlocked.includes("#")) {
                generated ??= this.generateNatLiteralDef(dname);
                generated ??= this.generateNatLiteralIsNat(dname);
                generated ??= this.generateNatLiteralOp(dname);
            }
            if (unlocked.includes("z")) {
                generated ??= this.generateZLiteralDef(dname);
            }
            if (unlocked.includes("Z")) {
                generated ??= this.generateZLiteralIsZ(dname);
                generated ??= this.generateZLiteralOp(dname);
            }
            if (generated)
                return this.deductions[generated];
        }
        throw "null";
    }
    getDeductionTokens(name) {
        return ruleparser.parse(name);
    }
    getAtomDeductionTokens(name, res = [], token = ruleparser.parse(name)) {
        if (token.length === 1) {
            res.push(token[0]);
        }
        else {
            for (let i = 1; i < token.length; i++)
                this.getAtomDeductionTokens("", res, token[i]);
        }
    }
    generateDeduction(name) {
        if (!name)
            return null;
        try {
            const tokens = ruleparser.parse(name);
            return this.generateDeductionByToken(tokens);
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
        const num = BigInt(n[1]);
        return this.addDeduction(name, parser.parse(`⊢${num} =S(${num - 1n})`), "算数符号定义");
    }
    generateNatLiteralIsNat(name, vnum = 0) {
        const vpre = "v".repeat(vnum);
        const n = name.match(/^\.([1-9][0-9]*)@N$/);
        if (!n || !isFinite(Number(n[1])))
            return;
        if (this.deductions[vpre + name])
            return vpre + name;
        const vars = [];
        let V = "";
        for (let i = 0; i < vnum; i++) {
            vars.push({ type: "replvar", name: "$" + i });
            V += "V$" + i + ":";
        }
        const num = BigInt(n[1]);
        const steps = [
            num === 1n ?
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "apn1" } :
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "." + (num - 1n) + "@N" },
            { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "apn2" },
            { conditionIdxs: [-1], replaceValues: [{ type: "replvar", name: String(num - 1n) }], deductionIdx: vpre + "<a4" },
            { conditionIdxs: [-1, -3], replaceValues: [], deductionIdx: vpre + "mp" },
            { conditionIdxs: [], replaceValues: [], deductionIdx: vpre + "d" + String(num) },
            { conditionIdxs: [-1], replaceValues: [], deductionIdx: vpre + ".=s" },
            { conditionIdxs: [-1, -3], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" }
        ];
        return this.addDeduction(vpre + name, parser.parse(`⊢${V}(${num}@N)`), "元规则生成*", steps, new Set());
    }
    generateNatLiteralOp(name, vnum = 0) {
        const vpre = "v".repeat(vnum);
        const n = name.match(/^\.(0|[1-9][0-9]*)([\+\*])(0|[1-9][0-9]*)$/);
        if (!n || !isFinite(Number(n[1])) || !isFinite(Number(n[3])))
            return;
        if (this.deductions[vpre + name])
            return vpre + name;
        const vars = [];
        let V = "";
        for (let i = 0; i < vnum; i++) {
            vars.push({ type: "replvar", name: "$" + i });
            V += "V$" + i + ":";
        }
        const a = BigInt(n[1]);
        const b = BigInt(n[3]);
        const op = n[2];
        const isNat = (x) => {
            return x === 0n ? "apn1" : "." + x + "@N";
        };
        const steps = b === 0n ? [{ conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + ":" + isNat(a) + ",<d" + op + "1" }] : [
            b > 1n ?
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "." + a + op + (b - 1n) } :
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + ":" + isNat(a) + ",<d" + op + "1" },
            { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + ":" + isNat(a) + ",:" + isNat(b - 1n) + ",<<d" + op + "2" },
            { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "d" + b },
            op === "+" ? { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + "d" + (a + b) } : b === 1n ? { conditionIdxs: [], replaceValues: [], deductionIdx: ":" + isNat(a) + ",<.0+" } :
                { conditionIdxs: [], replaceValues: vars, deductionIdx: vpre + `.${a * (b - 1n)}+${a}` },
            { conditionIdxs: [-4, -3], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" },
            op === "+" ? { conditionIdxs: [-2], replaceValues: [], deductionIdx: vpre + ".=s" } : null,
            { conditionIdxs: [op === "+" ? -4 : -3], replaceValues: [], deductionIdx: vpre + ".=s" },
            { conditionIdxs: [-1, op === "+" ? -3 : -2], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" },
            op === "+" ? { conditionIdxs: [-3, -1], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: vpre + "<<a8" } :
                { conditionIdxs: [-1, op === "+" ? -5 : -4], replaceValues: [], deductionIdx: vpre + ".=t" }
        ].filter(e => e);
        return this.addDeduction(vpre + name, parser.parse(`⊢${V}(${a}${op}${b}=${op === "+" ? a + b : a * b})`), "元规则生成*", steps, new Set());
    }
    generateZLiteralDef(name) {
        const n = name.match(/^dZ([\+\-])?([0-9]|[1-9][0-9]+)$/);
        if (!n)
            return;
        if (this.deductions[name])
            return name;
        const num = (n[1] ?? "+") + n[2];
        let pos = "0", min = "0";
        if (n[1] === "-") {
            min = n[2];
        }
        else {
            pos = n[2];
        }
        return this.addDeduction(name, parser.parse(`⊢${num} = Z((${pos},${min}))`), "算数符号定义");
    }
    generateZLiteralIsZ(name) {
        const n = name.match(/^\.([\+\-])?([0-9]|[1-9][0-9]+)@Z$/);
        if (!n)
            return;
        if (this.deductions[name])
            return name;
        const num = (n[1] ?? "+") + n[2];
        let pos = "apn1", min = "apn1";
        if (n[1] === "-") {
            min = Number(n[2]) !== 0 ? `.${n[2]}@N` : "apn1";
        }
        else {
            pos = Number(n[2]) !== 0 ? `.${n[2]}@N` : "apn1";
        }
        const steps = [
            { conditionIdxs: [], replaceValues: [], deductionIdx: `:${pos}:${min},.@Z` },
            { conditionIdxs: [], replaceValues: [], deductionIdx: `dZ` + num },
            { conditionIdxs: [-1, -2], replaceValues: [{ type: "replvar", name: "0" }], deductionIdx: `:.=s,<<a8` },
        ];
        return this.addDeduction(name, parser.parse(`⊢(${num}@Z)`), "元规则生成*", steps, new Set());
    }
    generateZLiteralOp(name) {
        const n = name.match(/^\.([\+\-])?([0-9]|[1-9][0-9]+)([\+\-\*])([\+\-])?([0-9]|[1-9][0-9]+)$/);
        if (!n)
            return;
        if (this.deductions[name] || this.generateNatLiteralOp(name))
            return name;
        const num1 = (n[1] ?? "+") + n[2];
        let pos1 = "apn1", min1 = "apn1";
        let p11 = "0", p12 = "0";
        if (n[1] === "-") {
            min1 = Number(n[2]) !== 0 ? `.${n[2]}@N` : "apn1";
            p12 = n[2];
        }
        else {
            pos1 = Number(n[2]) !== 0 ? `.${n[2]}@N` : "apn1";
            p11 = n[2];
        }
        const num2 = (n[4] ?? "+") + n[5];
        let pos2 = "apn1", min2 = "apn1";
        let p21 = "0", p22 = "0";
        if (n[4] === "-") {
            min2 = Number(n[5]) !== 0 ? `.${n[5]}@N` : "apn1";
            p22 = n[5];
        }
        else {
            pos2 = Number(n[5]) !== 0 ? `.${n[5]}@N` : "apn1";
            p21 = n[5];
        }
        const num3 = n[3] === "+" ? BigInt(num1) + BigInt(num2) : n[3] === "-" ? BigInt(num1) - BigInt(num2) : BigInt(num1) * BigInt(num2);
        const writeValue = (...v) => v.map(e => ({ type: "replvar", name: e }));
        const _0 = [{ type: "replvar", name: "0" }];
        const a8 = { conditionIdxs: [-1, -2], replaceValues: _0, deductionIdx: `<<a8` };
        const steps = [
            { conditionIdxs: [], replaceValues: [], deductionIdx: `:${pos1}:${min1},.Xi` },
            { conditionIdxs: [], replaceValues: [], deductionIdx: `:${pos2}:${min2},.Xi` },
            { conditionIdxs: [-2, -1], replaceValues: [], deductionIdx: `<<dZ` + n[3] },
            { conditionIdxs: [], replaceValues: writeValue(p11, p12), deductionIdx: `:.Pr1,.=s` }, a8,
            { conditionIdxs: [], replaceValues: writeValue(p21, p22), deductionIdx: `:.Pr1,.=s` }, a8,
            { conditionIdxs: [], replaceValues: writeValue(p11, p12), deductionIdx: `:.Pr2,.=s` }, a8,
            { conditionIdxs: [], replaceValues: writeValue(p21, p22), deductionIdx: `:.Pr2,.=s` }, a8,
            { conditionIdxs: [], replaceValues: [], deductionIdx: `:dZ${num1},.=s` }, a8,
            { conditionIdxs: [], replaceValues: [], deductionIdx: `:dZ${num2},.=s` }, a8,
            { conditionIdxs: [], replaceValues: [], deductionIdx: n[3] === "+" ? `.${p11}+${p21}` : n[3] === "*" ? `.${p11}*${p21}` : `.${p11}+${p22}` }, a8,
            { conditionIdxs: [], replaceValues: [], deductionIdx: n[3] === "+" ? `.${p12}+${p22}` : n[3] === "*" ? `.${p12}*${p22}` : `.${p12}+${p21}` }, a8,
        ];
        let a = n[3] === "+" ? BigInt(p11) + BigInt(p21) : BigInt(p11) + BigInt(p22);
        let b = n[3] === "+" ? BigInt(p12) + BigInt(p22) : BigInt(p12) + BigInt(p21);
        if (n[3] === "*") {
            steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${p11}*${p22}` }, a8);
            steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${p12}*${p21}` }, a8);
            const x11_21 = BigInt(p11) * BigInt(p21);
            const x12_22 = BigInt(p12) * BigInt(p22);
            const x11_22 = BigInt(p11) * BigInt(p22);
            const x21_12 = BigInt(p21) * BigInt(p12);
            steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${x11_21}+${x12_22}` }, a8);
            steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${x11_22}+${x21_12}` }, a8);
            a = x11_21 + x12_22;
            b = x11_22 + x21_12;
        }
        if (a > 0n && b > 0n) {
            if (a >= b) {
                const a_min_b = a - b;
                const a_min_bN = a_min_b === 0n ? "apn1" : `.${a_min_b}@N`;
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `:${a_min_bN}:apn1:.${b}@N,.Zr` });
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${a_min_b}+${b}` }, a8);
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.0+${b}` }, a8);
            }
            else {
                const b_min_a = b - a;
                const b_min_aN = `.${b_min_a}@N`;
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `:apn1:${b_min_aN}:.${a}@N,.Zr` });
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.0+${a}` }, a8);
                steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `.${b_min_a}+${a}` }, a8);
            }
        }
        steps.push({ conditionIdxs: [], replaceValues: [], deductionIdx: `dZ` + num3 });
        if (a > 0n && b > 0n)
            steps.push({ conditionIdxs: [-1, -2], replaceValues: [], deductionIdx: `.=t` });
        steps.push({ conditionIdxs: [n[3] === "*" ? -2 : (18 - steps.length), -1], replaceValues: [], deductionIdx: `:#:.=s,.=t` });
        return this.addDeduction(name, parser.parse(`⊢(${num1}${n[3]}${num2}=${num3 >= 0n ? "+" + num3 : num3})`), "元规则生成*", steps, new Set());
    }
    deduct(step, inlineMode, partialTest) {
        const { conditionIdxs, deductionIdx, replaceValues } = step;
        const deduction = this.generateDeduction(deductionIdx);
        const errorMsg = TR(`规则 `) + deductionIdx + TR(` 推理失败:`);
        if (!deduction)
            throw errorMsg + TR("规则不存在");
        const { conditions, conclusion, replaceNames, steps, replaceTypes } = deduction;
        // firstly, match condition, get matchtable ( partial initially provided by users)
        let replacedVarTypeTable = {};
        let matchTable = partialTest ? {} : Object.fromEntries(replaceNames.map((replname, idx) => (assert.getReplVarsType(replaceValues[idx], replacedVarTypeTable, replaceTypes[replname]),
            [replname, replaceValues[idx]])));
        // assertions in pattern
        let assertions = [];
        let assertionsFrom = [];
        // assertions in matched conditions
        let astAssertions = {};
        for (const [conditionIdx, condition] of conditions.entries()) {
            const condPropIdx = conditionIdxs[conditionIdx];
            if (partialTest && !isFinite(condPropIdx))
                return;
            const condProp = this.propositions[condPropIdx];
            if (!condProp)
                throw errorMsg + TR(`第${conditionIdx + 1}个`) + TR(`条件对应的定理p`) + condPropIdx + TR(`不存在`);
            try {
                // 
                assert.match(condProp.value, condition, /^\$/, false, matchTable, replacedVarTypeTable, null, assertions);
                while (assertionsFrom.length < assertions.length)
                    assertionsFrom.push(conditionIdx);
            }
            catch (e) {
                // match failed
                throw errorMsg + TR(`第${conditionIdx + 1}个`) + TR(`条件`) + e;
            }
        }
        if (partialTest)
            return; // just test, no props to add
        // assertions in condition can spread, i.e. fn(a,nf(a))  => fn(nf(a),nf(a))
        // we spread it over matchTable and pattern assertions
        for (const astAss of Object.values(astAssertions)) {
            for (const ass of assertions) {
                astmgr.replace(ass, astAss.nodes[0], astAss);
            }
            for (const [n, v] of Object.entries(matchTable)) {
                astmgr.replace(v, astAss.nodes[0], astAss);
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
            assert.checkGrammer(replacedConclusion, "p");
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
    _findReplNameInRule(deductionIdx) {
        const d = this.deductions[deductionIdx];
        const p = new Set;
        for (const c of d.conditions)
            astmgr.getVarNames(c, p, /^\$/);
        astmgr.getVarNames(d.conclusion, p, /^\$/);
        return p;
    }
    _findNewReplName(deductionIdx, p = new Set) {
        let name = "$0", i = 0;
        if (deductionIdx) {
            const d = this.deductions[deductionIdx];
            for (const c of d.conditions)
                astmgr.getVarNames(c, p, /^\$/);
            astmgr.getVarNames(d.conclusion, p, /^\$/);
        }
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
    metaExistTheorem(idx, from) {
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
        if (!d.conditions.length) {
            this.metaConditionUniversalTheorem(idx, from);
            this.deductions["u" + idx] = this.deductions["v" + idx];
            return "u" + idx;
        }
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
                    assert.match(this.propositions[id].value, c, /^\$/, false, replvarTable, {}, null, []);
                }
                catch (e) {
                    throw TR(`向`) + TR(`第${id + 1}个`) + TR(`条件添加不自由断言时出现不一致：`) + e;
                }
            });
            d.conditions.forEach((c, id) => {
                // const p0 = this.deduct({ deductionIdx: "a6", replaceValues: [this.propositions[id].value, s], conditionIdxs: [] });
                const p1 = this.deduct({ deductionIdx: "<a6", conditionIdxs: [id], replaceValues: [s] });
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
    metaNewConstant(replaceValues, from) {
        const [constAst, varAst, exprAst] = replaceValues;
        if (constAst.type !== "replvar")
            throw TR("$$0只能为纯变量名");
        if (constAst.name.match(/[A-Z]/))
            throw TR(`自定义符号中不能有大写字母`);
        if (constAst.name.startsWith("$"))
            throw TR("以$开头的变量名称被系统保留");
        if (constAst.name.startsWith("#"))
            throw TR("以#开头的变量名称被系统保留");
        const constCheckRes = this.isNameCanBeNewConst(constAst.name);
        if (constCheckRes !== true)
            throw TR("匹配条件##newconst($$0)时：") + constCheckRes;
        if (this.fns.has(constAst.name))
            throw TR("匹配条件##newconst($$0)时：$$0已有定义");
        const deduction = astmgr.clone(this.metaRules["c"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": constAst,
            "$$1": varAst,
            "$$2": exprAst
        };
        astmgr.replaceByMatchTable(deduction, replTable);
        const R = astmgr.clone(exprAst);
        astmgr.replace(R, varAst, constAst);
        if (assert.nf(constAst.name, R) !== -1)
            throw TR("定义的常量没在结论中出现");
        astmgr.assign(deduction.nodes[1].nodes[0].nodes[1], R);
        let d;
        try {
            this.consts.add(constAst.name);
            d = this.addDeduction("dc" + constAst.name, deduction, from);
            if (this.deductions[d].replaceNames.length)
                throw TR("不能包含$开头的替代项");
        }
        catch (e) {
            if (d)
                delete this.deductions[d];
            this.consts.delete(constAst.name);
            throw e;
        }
        return d;
    }
    metaNewFunction(replaceValues, from) {
        const [fnAst, varAst, exprAst, paramAsts] = replaceValues;
        if (!paramAsts.length)
            throw null;
        if (fnAst.type !== "replvar")
            throw TR("$$0只能为纯变量名");
        if (fnAst.name.match(/[A-Z]/))
            throw TR(`自定义符号中不能有大写字母`);
        if (fnAst.name.startsWith("#"))
            throw TR("以#开头的函数被系统保留");
        if (fnAst.name.startsWith("$"))
            throw TR("以$开头的函数被系统保留");
        const fnCheckRes = this.fns.has(fnAst.name) || this.verbs.has(fnAst.name);
        if (fnCheckRes)
            throw TR(`匹配条件##newfn($$0)时：$$0已有定义`);
        const deduction = astmgr.clone(this.metaRules["f"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": fnAst,
            "$$2": varAst,
            "$$3": exprAst
        };
        const wrapVs = (ast) => {
            console.assert(ast.name === "V");
            let first = true;
            for (const p of paramAsts) {
                const n = p.name;
                if (p.type !== "replvar")
                    throw TR("函数的参数必须是变量");
                if (assert.isConst(n))
                    throw TR("函数的参数不能是常量");
                if (first) {
                    astmgr.assign(ast.nodes[0], p);
                    first = false;
                    continue;
                }
                astmgr.assign(ast, { type: "sym", name: "V", nodes: [p, ast] });
            }
        };
        astmgr.replaceByMatchTable(deduction, replTable);
        const R = astmgr.clone(exprAst);
        if (assert.nf(varAst.name, R) !== -1)
            throw TR("定义的函数表达式没在结论中出现");
        astmgr.replace(R, varAst, { type: "fn", name: fnAst.name, nodes: paramAsts });
        astmgr.assign(deduction.nodes[1].nodes[0].nodes[1].nodes[1], R);
        wrapVs(deduction.nodes[1].nodes[0].nodes[0]);
        wrapVs(deduction.nodes[1].nodes[0].nodes[1]);
        let d;
        try {
            this.fns.add(fnAst.name);
            this.isNameCanBeNewFnOrVerb();
            d = this.addDeduction("df" + fnAst.name, deduction, from);
            if (this.deductions[d].replaceNames.length)
                throw TR("不能包含$开头的替代项");
        }
        catch (e) {
            if (d)
                delete this.deductions[d];
            this.fns.delete(fnAst.name);
            throw e;
        }
        return d;
    }
    metaNewVerb(replaceValues, from) {
        const [fnAst, exprAst, paramAsts] = replaceValues;
        if (!paramAsts.length)
            throw null;
        if (fnAst.type !== "replvar")
            throw TR("$$0只能为纯变量名");
        if (fnAst.name.match(/[A-Z]/))
            throw TR(`自定义符号中不能有大写字母`);
        if (fnAst.name.startsWith("#"))
            throw TR("以#开头的函数被系统保留");
        if (fnAst.name.startsWith("$"))
            throw TR("以$开头的函数被系统保留");
        const fnCheckRes = this.fns.has(fnAst.name) || this.verbs.has(fnAst.name);
        if (fnCheckRes)
            throw TR(`匹配条件##newfn($$0)时：$$0已有定义`);
        const deduction = astmgr.clone(this.metaRules["prd"].value.nodes[1].nodes[0].nodes[0]);
        const replTable = {
            "$$0": fnAst,
            "$$2": exprAst
        };
        const wrapVs = (ast) => {
            console.assert(ast.name === "V");
            let first = true;
            for (const p of paramAsts) {
                const n = p.name;
                if (p.type !== "replvar")
                    throw TR("函数的参数必须是变量");
                if (assert.isConst(n))
                    throw TR("函数的参数不能是常量");
                if (first) {
                    astmgr.assign(ast.nodes[0], p);
                    first = false;
                    continue;
                }
                astmgr.assign(ast, { type: "sym", name: "V", nodes: [p, ast] });
            }
        };
        astmgr.replaceByMatchTable(deduction, replTable);
        astmgr.assign(deduction.nodes[1].nodes[0].nodes[1].nodes[0], { type: "fn", name: fnAst.name, nodes: paramAsts });
        wrapVs(deduction.nodes[1].nodes[0]);
        let d;
        try {
            this.verbs.add(fnAst.name);
            this.isNameCanBeNewFnOrVerb();
            d = this.addDeduction("dv" + fnAst.name, deduction, from);
            if (this.deductions[d].replaceNames.length)
                throw TR("不能包含$开头的替代项");
        }
        catch (e) {
            if (d)
                delete this.deductions[d];
            this.verbs.delete(fnAst.name);
            throw e;
        }
        return d;
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
        const fastrule = this.fastmetarules;
        // axiom, |- A
        if (!d.conditions.length) {
            const oldP = this.propositions;
            try {
                this.expandMacroWithDefaultValue(idx, null, true);
                this.fastmetarules += "<";
                this.deduct({
                    deductionIdx: "<a1", conditionIdxs: [0],
                    replaceValues: [s]
                });
                const ret = this.addMacro("c" + idx, from);
                this.propositions = oldP;
                this.fastmetarules = fastrule;
                return ret;
            }
            catch (e) {
                this.propositions = oldP;
                this.fastmetarules = fastrule;
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
                return offsetCondTable[idx] = this.deduct({
                    deductionIdx: "<a1", conditionIdxs: [p0],
                    replaceValues: [s]
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
            this.fastmetarules = fastrule;
            return ret;
        }
        catch (e) {
            this.propositions = oldP;
            this.fastmetarules = fastrule;
            throw e;
        }
    }
    metaDeductTheorem(idx, from) {
        if (idx[0] === "<") {
            this.generateDeduction(idx.slice(1));
            return idx.slice(1);
        }
        if (this.deductions[">" + idx])
            return ">" + idx;
        const d = this.generateDeduction(idx);
        const fastrule = this.fastmetarules;
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
                return offsetCondTable[idx] = this.deduct({
                    deductionIdx: "<a1", conditionIdxs: [p0],
                    replaceValues: [s]
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
            this.fastmetarules += "<";
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
            this.fastmetarules = fastrule;
            return ret;
        }
        catch (e) {
            this.fastmetarules = fastrule;
            this.propositions = oldP;
            throw e;
        }
    }
    metaInvDeductTheorem(idx, from) {
        // >a => a
        if (idx[0] === ">") {
            this.generateDeduction(idx.slice(1));
            return idx.slice(1);
        }
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
    metaCombineTheorem(idx1s, idx2, from) {
        const name = ":" + idx1s.join(":") + "," + idx2;
        if (this.deductions[name])
            return name;
        const d2 = this.generateDeduction(idx2);
        if (d2.conditions.length < idx1s.length)
            throw TR("匹配条件推理规则($$1b, ...$$2 ⊢ $$3)失败");
        while (d2.conditions.length > idx1s.length)
            idx1s.push("#");
        const d1s = idx1s.map(e => e === "#" ? null : this.generateDeduction(e));
        const oldP = this.propositions;
        const cloneAndRename = (ast, postfix) => {
            const R = astmgr.clone(ast);
            const rename = (a) => {
                if (a.type === "replvar" && a.name.startsWith("$")) {
                    a.name = a.name + postfix;
                }
                if (a.nodes?.length) {
                    for (const n of a.nodes) {
                        rename(n);
                    }
                }
            };
            return rename(R), R;
        };
        // rename replvars in d1s and d2
        const d1conds = d1s.map((d, i) => {
            if (!d)
                return null;
            return d.conditions.map(c => cloneAndRename(c, String(i + 1)));
        });
        const d1concs = d1s.map((d, i) => {
            if (!d)
                return null;
            return cloneAndRename(d.conclusion, "" + String(i + 1));
        });
        const d2cond = d2.conditions.map(e => cloneAndRename(e, "0"));
        const d1replaceNames = d1s.map((d, i) => d ? d.replaceNames.map(dr => ({ type: "replvar", name: dr + String(i + 1) })) : []);
        const d2replaceNames = d2.replaceNames.map(dr => ({ type: "replvar", name: dr + "0" }));
        // generate and solve constrains
        const constrains = [];
        for (let i = 0; i < d1s.length; i++) {
            if (!d1concs[i])
                continue;
            constrains.push([d1concs[i], d2cond[i], false]);
        }
        const solver = new ConstrainSolver();
        const assertions = [];
        const mt = solver.solveConstrain(constrains, assertions);
        // solver.dbg(mt, constrains, assertions);
        const nfTable = solver.addAssertions(mt, assertions);
        // use match table to replace all iteratively (include itself, nftable and dconds/dconcs)
        const finished = new Set;
        for (const key in mt) {
            const v = mt[key];
            const k = { type: "replvar", name: key };
            finished.add(key);
            const RP = (ast) => {
                astmgr.replace(ast, k, v);
            };
            for (const key2 in mt) {
                if (finished.has(key2))
                    continue;
                RP(mt[key2]);
            }
            for (const key2 in nfTable) {
                RP(nfTable[key2][0]);
            }
            d1conds.forEach(conds => {
                if (!conds)
                    return;
                conds.forEach(c => RP(c));
            });
            d2cond.forEach(c => RP(c));
            d1replaceNames.forEach(c => c.forEach(sc => RP(sc)));
            d2replaceNames.forEach(c => RP(c));
        }
        // add nf fn from match table
        for (const key2 in nfTable) {
            const k = { type: "replvar", name: key2 };
            const RP = (ast) => {
                astmgr.replace(ast, k, nfTable[key2][0]);
            };
            d1conds.forEach(conds => {
                if (!conds)
                    return;
                conds.forEach(c => RP(c));
            });
            d2cond.forEach(c => RP(c));
            d1replaceNames.forEach(c => c.forEach(sc => RP(sc)));
            d2replaceNames.forEach(c => RP(c));
        }
        try {
            this.removePropositions();
            const hyps = d1conds.map((c, idx) => c ? c.map(c => this.addHypothese(c)) : [this.addHypothese(d2cond[idx])]);
            const pcs = [];
            for (let i = 0; i < d1conds.length; i++) {
                if (idx1s[i] === "#")
                    pcs.push(hyps[i][0]);
                else
                    pcs.push(this.deduct({
                        deductionIdx: idx1s[i], conditionIdxs: hyps[i],
                        replaceValues: d1replaceNames[i]
                    }));
            }
            this.deduct({
                deductionIdx: idx2, conditionIdxs: pcs,
                replaceValues: d2replaceNames
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
                    assert.match(a, A, /^\$/, false, matched, {}, null, []);
                    replacedNth++;
                }
                catch (e) { }
                // a == b : a <> a
                return this.deduct({ deductionIdx: prefix + ".<>i", conditionIdxs: [], replaceValues: [...Vs, a] });
            }
            try {
                const matched = {};
                assert.match(a, A, /^\$/, false, matched, {}, null, []);
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
}
//# sourceMappingURL=formalsystem.js.map