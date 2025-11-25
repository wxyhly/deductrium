import { ASTParser } from "./astparser.js";
import { initFormalSystem } from "./initial.js";
const astparser = new ASTParser;
export class SavesParser {
    creative = false;
    constructor(creative) {
        this.creative = creative;
    }
    serializeDeductionStep(s) {
        return [
            s.deductionIdx, s.conditionIdxs,
            s.replaceValues.map(v => astparser.stringifyTight(v))
        ];
    }
    serializeProposition(p) {
        const value = astparser.stringifyTight(p.value);
        const step = p.from ? this.serializeDeductionStep(p.from) : null;
        return [value, step];
    }
    deserializeDeductionStep(v) {
        return { conditionIdxs: v[1], deductionIdx: v[0], replaceValues: v[2].map(v => astparser.parse(v)) };
    }
    deserializeProposition(v) {
        return {
            value: astparser.parse(v[0]),
            from: v[1] ? this.deserializeDeductionStep(v[1]) : null
        };
    }
    serializeDeduction(deduction) {
        const value = astparser.stringifyTight(deduction.value);
        const steps = deduction.steps?.map(s => this.serializeDeductionStep(s));
        // if fs has tempvars record, then serialize it
        return deduction.tempvars?.size ? [value, deduction.from, steps, Array.from(deduction.tempvars)] : [value, deduction.from, steps];
    }
    deserializeDeduction(name, fs, sd) {
        // deserialized data is reliable, no need to regen tempvars
        fs.addDeduction(name, astparser.parse(sd[0]), sd[1], sd[2]?.map(e => ({
            deductionIdx: e[0], conditionIdxs: e[1], replaceValues: e[2].map(v => astparser.parse(v))
        })), sd[3] ? new Set(sd[3]) : new Set());
    }
    serialize(gui) {
        const fs = gui.formalSystem;
        const dlist = gui.deductions;
        const userD = {};
        for (const [n, d] of Object.entries(fs.deductions)) {
            // save a..x
            if (!d.from.endsWith("*") && !n.endsWith("x"))
                continue;
            if (n.startsWith("c") || n.startsWith("<") || n.startsWith(">") || n.startsWith("v") || n.startsWith("u") || n.startsWith("e") || n.startsWith(".")) {
                continue;
            }
            userD[n] = this.serializeDeduction(d);
        }
        const props = gui.getProps();
        return JSON.stringify([
            Array.from(fs.consts), Array.from(fs.fns), Array.from(fs.verbs), [[ /* todo metamacro */], ...gui.metarules], userD, dlist, props.map(s => this.serializeProposition(s))
        ]);
    }
    deserializeArr(fs, arr) {
        // 
        if (arr.length < 7)
            arr.splice(2, 0, [], []);
        const [arrC, arrFn, arrVb, arrM, dictD, arrD, arrP] = arr;
        for (const v of arrC) {
            fs.consts.add(v);
        }
        for (const v of arrFn) {
            fs.fns.add(v);
        }
        for (const v of arrVb) {
            fs.verbs.add(v);
        }
        for (const [k, v] of Object.entries(dictD)) {
            if (v.length)
                this.deserializeDeduction(k, fs, v);
        }
        if (arrP)
            for (const v of arrP) {
                fs.propositions.push(this.deserializeProposition(v));
            }
        return { fs, arrD, arrM };
    }
    deserializeMetaMacro(gui, arr) {
        // todo
        gui.formalSystem.metaMacro = {};
    }
    deserialize(gui, str) {
        const skipRendering = gui.skipRendering;
        gui.skipRendering = true;
        const fsArrD = initFormalSystem(this.creative);
        const fsdata = this.deserializeArr(fsArrD.fs, JSON.parse(str));
        const savedMetarules = gui.formalSystem.fastmetarules;
        gui.formalSystem = fsdata.fs;
        gui.formalSystem.fastmetarules = savedMetarules;
        gui.deductions = fsdata.arrD;
        // 25-11-25: bug fix player's progress
        if (gui.deductions.includes("apn3") && !gui.deductions.includes("apn4") && !gui.deductions.includes("apn5")) {
            gui.deductions.push("apn4", "apn5");
        }
        if (fsdata.arrM[0]) {
            gui.metarules = fsdata.arrM.slice(1);
            this.deserializeMetaMacro(gui, fsdata.arrM[0]);
        }
        gui.skipRendering = skipRendering;
        gui.updatePropositionList(true);
        gui.updateDeductionList();
        gui.updateMetaRuleList(true);
    }
}
//# sourceMappingURL=savesparser.js.map