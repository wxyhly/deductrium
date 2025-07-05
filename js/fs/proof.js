import { TR } from "../lang.js";
import { AssertionSystem } from "./assertion.js";
import { ASTMgr } from "./astmgr.js";
const astmgr = new ASTMgr;
const assert = new AssertionSystem;
export class Proof {
    fs;
    constructor(fs) {
        this.fs = fs;
    }
    prove(ast) {
        const varTable = assert.getReplVarsType(ast, {}, false);
        if (Object.values(varTable).includes(true))
            throw TR("无法对非命题逻辑符号进行真值指派");
        const vars = Object.keys(varTable);
        const hypEnums = 1 << vars.length;
        const proofEnumsTable = [];
        for (let i = 0; i < hypEnums; i++) {
            const [t, p] = this.enumProve(ast, vars, i);
            if (!t)
                throw TR("条件重言式测试失败：真值指派") + vars.map((v, idx) => (v + TR(`为`) + (((1 << idx) & i) ? TR("真") : TR("假")))).join(TR("、")) + TR("时命题为假");
            proofEnumsTable.push(p);
        }
        for (let idx = 0; idx < vars.length; idx++) {
            for (let i = 0; i < hypEnums >> (idx + 1); i++) {
                const prefix = "".padEnd(vars.length - idx - 1, "c");
                const p1 = proofEnumsTable[i];
                const p2 = proofEnumsTable[i + (hypEnums >> (idx + 1))];
                const p3 = this.fs.deduct({
                    deductionIdx: prefix + ".m2",
                    conditionIdxs: [p2, p1], replaceValues: [],
                });
                proofEnumsTable[i] = p3;
            }
        }
    }
    enumProve(ast, vars, hyps) {
        const varsLen = vars.length;
        const prefix = "".padEnd(varsLen, "c");
        if (ast.type === "replvar") {
            return this.cca1(vars, vars.indexOf(ast.name), hyps);
        }
        if (ast.type === "sym") {
            if (ast.name === "~") {
                const [ta, pa] = this.enumProve(ast.nodes[0], vars, hyps);
                if (!ta)
                    return [true, pa];
                return [false, this.fs.deduct({ deductionIdx: prefix + "<.ni", conditionIdxs: [pa], replaceValues: [] })];
            }
            if (ast.name === ">") {
                const prevLen = this.fs.propositions.length;
                const [tb, pb] = this.enumProve(ast.nodes[1], vars, hyps);
                // . > T : T
                if (tb) {
                    return [true, this.fs.deduct({ deductionIdx: prefix + "<a1", conditionIdxs: [pb], replaceValues: [ast.nodes[0]] })];
                }
                const [ta, pa] = this.enumProve(ast.nodes[0], vars, hyps);
                // T > F : F
                if (ta) {
                    return [false, this.fs.deduct({ deductionIdx: prefix + ".>TF", conditionIdxs: [pa, pb], replaceValues: [] })];
                }
                // F > U : T
                return [true, this.fs.deduct({ deductionIdx: prefix + ".>FU", conditionIdxs: [pa], replaceValues: [ast.nodes[1]] })];
            }
            if (ast.name === "<>") {
                const [ta, pa] = this.enumProve(ast.nodes[0], vars, hyps);
                const [tb, pb] = this.enumProve(ast.nodes[1], vars, hyps);
                const dname = (ta ? "T" : "F") + (tb ? "T" : "F");
                return [ta === tb, this.fs.deduct({ deductionIdx: prefix + ".<>" + dname, conditionIdxs: [pa, pb], replaceValues: [] })];
            }
            if (ast.name === "|") {
                const [ta, pa] = this.enumProve(ast.nodes[0], vars, hyps);
                const [tb, pb] = this.enumProve(ast.nodes[1], vars, hyps);
                const dname = ta ? "1" : tb ? "2" : "n";
                const conditionIdxs = ta ? [pa] : tb ? [pb] : [pa, pb];
                const replaceValues = ta ? [ast.nodes[1]] : tb ? [ast.nodes[0]] : [];
                return [ta || tb, this.fs.deduct({ deductionIdx: prefix + ".|" + dname, conditionIdxs, replaceValues })];
            }
            if (ast.name === "&") {
                const [ta, pa] = this.enumProve(ast.nodes[0], vars, hyps);
                const [tb, pb] = this.enumProve(ast.nodes[1], vars, hyps);
                const dname = !ta ? "n1" : !tb ? "n2" : "";
                const conditionIdxs = !ta ? [pa] : !tb ? [pb] : [pa, pb];
                const replaceValues = !ta ? [ast.nodes[1]] : !tb ? [ast.nodes[0]] : [];
                return [ta && tb, this.fs.deduct({ deductionIdx: prefix + ".&" + dname, conditionIdxs, replaceValues })];
            }
            throw TR("无法对非命题逻辑符号进行真值指派");
        }
    }
    cca1(vars, id, hyps) {
        const truth = !!((hyps >> id) & 1);
        const len = vars.length;
        const prefix = "".padEnd(id, "c");
        const replaceValues = vars.map((v, idx) => (hyps >> idx) & 1 ? { type: "replvar", name: v } : {
            type: "sym", name: "~", nodes: [{ type: "replvar", name: v }]
        });
        const gen = (l) => {
            if (l < 3)
                throw "cannot reached";
            const name = ".a1_" + l;
            if (this.fs.deductions[name])
                return name;
            const p = this.fs.propositions;
            this.fs.propositions = [];
            try {
                this.fs.addHypothese({ type: "replvar", name: "$0" });
                for (let i = 1; i < l; i++) {
                    this.fs.deduct({
                        deductionIdx: "<a1", conditionIdxs: [i - 1],
                        replaceValues: [{ type: "replvar", name: "$" + i }]
                    });
                }
                this.fs.addMacro(name, "元规则生成*");
                this.fs.propositions = p;
                return name;
            }
            catch (e) {
                this.fs.propositions = p;
                throw e;
            }
        };
        // a>b> c>c
        if (id === len - 1) {
            return [truth, this.fs.deduct({ deductionIdx: prefix + ".i", conditionIdxs: [], replaceValues })];
        }
        // a> b>c>b
        if (id === len - 2) {
            return [truth, this.fs.deduct({ deductionIdx: prefix + "a1", conditionIdxs: [], replaceValues })];
        }
        return [truth, this.fs.deduct({
                deductionIdx: prefix + ">" + gen(len - id), conditionIdxs: [], replaceValues
            })];
    }
}
//# sourceMappingURL=proof.js.map