import { ASTParser } from "./astparser.js";
import { Deduction, FormalSystem } from "./formalsystem.js";
import { initFormalSystem } from "./initial.js";
type SerilizedDeductionStep = [string, number[], string[]];
type SerilizedDeduction = [string, string, SerilizedDeductionStep[]];

const dict = {
    ',"aE0","aPair","aPow","aUnion","areg","arepl","asep","ainf",': "a#`",
    '],["0","1","2","3","4","5","6","7","8","9"': "b#`",
    '[["Union","Pow","Pair","S"': "c#`",
    ',"d0","d1","d2","d3","d4","d5","d6","d7","d8","d9",': "d#`",
    '","a': 'a`',
    '","d': 'd`',
};
const replaceArr1 = Object.entries(dict);
const replaceArr2 = replaceArr1.slice(0).reverse();
const astparser = new ASTParser;
export class SavesParser {
    serializeDeduction(deduction: Deduction): SerilizedDeduction {
        const value = astparser.stringifyTight(deduction.value);
        const steps = deduction.steps?.map(s => [
            s.deductionIdx, s.conditionIdxs,
            s.replaceValues.map(v => astparser.stringifyTight(v))
        ] as SerilizedDeductionStep);
        return [value, deduction.from, steps];
    }
    deserializeDeduction(name: string, fs: FormalSystem, sd: SerilizedDeduction) {
        fs.addDeduction(name, astparser.parse(sd[0]), sd[1], sd[2]?.map(e => ({
            deductionIdx: e[0], conditionIdxs: e[1], replaceValues: e[2].map(v => astparser.parse(v))
        })));
    }
    serialize(dlist: string[], fs: FormalSystem) {
        const userD = {};
        for (const [n, d] of Object.entries(fs.deductions)) {
            if (!d.from.endsWith("*")) continue;
            if (n.startsWith("c") || n.startsWith("<") || n.startsWith(">") || n.startsWith("v") || n.startsWith("u")) {
                continue;
            }
            userD[n] = this.serializeDeduction(d);
        }
        return this.serializeStr(JSON.stringify([
            Array.from(fs.fns), Array.from(fs.consts), userD, dlist
        ]));
    }
    deserializeArr(fs: FormalSystem, arr: any[]) {
        const [arrC, arrFn, dictD, arrD] = arr;
        for (const [k, v] of Object.entries(dictD)) {
            this.deserializeDeduction(k, fs, v as SerilizedDeduction);
        }
        for (const v of arrC) {
            fs.consts.add(v);
        }
        for (const v of arrFn) {
            fs.fns.add(v);
        }
        return { fs, arrD };
    }
    deserialize(str: string) {
        const fsArrD = initFormalSystem();
        return this.deserializeArr(fsArrD.fs, JSON.parse(this.deserializeStr(str)));
    }

    serializeStr(json: string) {
        for (const [a, b] of replaceArr1) {
            json = json.replaceAll(a, b);
        }
        return json;
    }
    deserializeStr(str: string) {
        for (const [a, b] of replaceArr2) {
            str = str.replaceAll(b, a);
        }
        return str;
    }
}