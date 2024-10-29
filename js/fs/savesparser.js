import { ASTParser } from "./astparser.js";
import { initFormalSystem } from "./initial.js";
const dict = {
    ',"aE0","aPair","aPow","aUnion","areg","arepl","asep","ainf",': "a#`",
    '"0","1","2","3","4","5","6","7","8","9","10"': "b#`",
    '"{}","Union","Pow","S"': "c#`",
    ',"apn1","apn2","apn3","d1","d2","d3","d4","d5","d6","d7","d8","d9",': "d#`",
    '","a': 'a`',
    '","d': 'd`',
};
const replaceArr1 = Object.entries(dict);
const replaceArr2 = replaceArr1.slice(0).reverse();
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
        return [value, deduction.from, steps];
    }
    deserializeDeduction(name, fs, sd) {
        fs.addDeduction(name, astparser.parse(sd[0]), sd[1], sd[2]?.map(e => ({
            deductionIdx: e[0], conditionIdxs: e[1], replaceValues: e[2].map(v => astparser.parse(v))
        })));
    }
    serialize(gui) {
        const fs = gui.formalSystem;
        const dlist = gui.deductions;
        const userD = {};
        for (const [n, d] of Object.entries(fs.deductions)) {
            if (!d.from.endsWith("*"))
                continue;
            if (n.startsWith("c") || n.startsWith("<") || n.startsWith(">") || n.startsWith("v") || n.startsWith("u")) {
                continue;
            }
            userD[n] = this.serializeDeduction(d);
        }
        const props = gui.getProps();
        return this.serializeStr(JSON.stringify([
            Array.from(fs.fns), Array.from(fs.consts), userD, dlist, props.map(s => this.serializeProposition(s))
        ]));
    }
    deserializeArr(fs, arr) {
        const [arrC, arrFn, dictD, arrD, arrP] = arr;
        for (const [k, v] of Object.entries(dictD)) {
            this.deserializeDeduction(k, fs, v);
        }
        for (const v of arrC) {
            fs.consts.add(v);
        }
        for (const v of arrFn) {
            fs.fns.add(v);
        }
        if (arrP)
            for (const v of arrP) {
                fs.propositions.push(this.deserializeProposition(v));
            }
        return { fs, arrD };
    }
    deserialize(gui, str) {
        const fsArrD = initFormalSystem(this.creative);
        const fsdata = this.deserializeArr(fsArrD.fs, JSON.parse(this.deserializeStr(str)));
        const savedMetarules = gui.formalSystem.fastmetarules;
        gui.formalSystem = fsdata.fs;
        gui.formalSystem.fastmetarules = savedMetarules;
        gui.deductions = fsdata.arrD;
        gui.updatePropositionList(true);
        gui.updateDeductionList();
    }
    serializeStr(json) {
        for (const [a, b] of replaceArr1) {
            json = json.replaceAll(a, b);
        }
        return json;
    }
    deserializeStr(str) {
        for (const [a, b] of replaceArr2) {
            str = str.replaceAll(b, a);
        }
        return str;
    }
}
//# sourceMappingURL=savesparser.js.map