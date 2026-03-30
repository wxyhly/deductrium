import { ASTParser } from "./astparser.js";
import { Deduction, DeductionStep, FormalSystem, Proposition } from "./formalsystem.js";
import { FSGui } from "./gui.js";
import { initFormalSystem } from "./initial.js";
type SerilizedDeductionStep = [string, number[], string[]];
type SerilizedDeduction = [string, string, SerilizedDeductionStep[]] | [string, string, SerilizedDeductionStep[], string[]];
type SerilizedProposition = [string, SerilizedDeductionStep];


const astparser = new ASTParser;
export class SavesParser {
    creative = false;
    constructor(creative?: boolean) {
        this.creative = creative;
    }
    serializeDeductionStep(s: DeductionStep) {
        return [
            s.deductionIdx, s.conditionIdxs,
            s.replaceValues.map(v => astparser.stringifyTight(v))
        ] as SerilizedDeductionStep;
    }
    serializeProposition(p: Proposition): SerilizedProposition {
        const value = astparser.stringifyTight(p.value);
        const step = p.from ? this.serializeDeductionStep(p.from) : null;
        return [value, step];
    }
    deserializeDeductionStep(v: SerilizedDeductionStep): DeductionStep {
        return { conditionIdxs: v[1], deductionIdx: v[0], replaceValues: v[2].map(v => astparser.parse(v)) };
    }
    deserializeProposition(v: SerilizedProposition): Proposition {
        return {
            value: astparser.parse(v[0]),
            from: v[1] ? this.deserializeDeductionStep(v[1]) : null
        };
    }
    serializeDeduction(deduction: Deduction): SerilizedDeduction {
        const value = astparser.stringifyTight(deduction.value);
        const steps = deduction.steps?.map(s => this.serializeDeductionStep(s));
        // if fs has tempvars record, then serialize it
        return deduction.tempvars?.size ? [value, deduction.from, steps, Array.from(deduction.tempvars)] : [value, deduction.from, steps];
    }

    // 26-3-30: bug fix: rule "<.a1_n" not exist, use ":c{rec},.cs" instead

    private fixbug260330_(num: number) {
        return num === 3 ? ":ca1,.cs" : (":c" + this.fixbug260330_(num - 1) + ",.cs");
    }
    private fixbug260330(s: string) {
        const num = Number(s.match(/>\.a1\_([1-9][0-9]*)$/)[1]);
        return s.replace(/>\.a1\_([1-9][0-9]*)$/, this.fixbug260330_(num));
    }
    deserializeDeduction(name: string, fs: FormalSystem, sd: SerilizedDeduction) {
        // deserialized data is reliable, no need to regen tempvars
        fs.addDeduction(name, astparser.parse(sd[0]), sd[1], sd[2]?.map(e => ({
            deductionIdx: e[0].includes(">.a1_") ? this.fixbug260330(e[0]) : e[0], conditionIdxs: e[1], replaceValues: e[2].map(v => astparser.parse(v))
        })), sd[3] ? new Set(sd[3]) : new Set());
    }
    serialize(gui: FSGui) {
        const fs = gui.formalSystem;
        const dlist = gui.deductions;
        const userD = {};
        for (const [n, d] of Object.entries(fs.deductions)) {
            // save a..x
            if (!d.from.endsWith("*") && !n.endsWith("x")) continue;
            if (n.startsWith("c") || n.startsWith("<") || n.startsWith(">") || n.startsWith("v") || n.startsWith("u") || n.startsWith("e") || n.startsWith(".")) {
                continue;
            }
            userD[n] = this.serializeDeduction(d);
        }
        const props = gui.getProps();
        return JSON.stringify([
            Array.from(fs.consts), Array.from(fs.fns), Array.from(fs.verbs), [[/* todo metamacro */], ...gui.metarules], userD, dlist, props.map(s => this.serializeProposition(s))
        ]);
    }
    deserializeArr(fs: FormalSystem, arr: any[]) {
        // 
        if (arr.length < 7) arr.splice(2, 0, [], []);
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
            if ((v as any[]).length) this.deserializeDeduction(k, fs, v as SerilizedDeduction);
        }
        if (arrP)
            for (const v of arrP) {
                fs.propositions.push(this.deserializeProposition(v));
            }
        return { fs, arrD, arrM };
    }
    deserializeMetaMacro(gui: FSGui, arr: any) {
        // todo
        gui.formalSystem.metaMacro = {};
    }
    deserialize(gui: FSGui, str: string) {
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