import { ASTParser } from "./astparser.js";
import { SavesParser } from "./savesparser.js";
export class FSCmd {
    cmdBuffer = [];
    astparser = new ASTParser;
    escClear = true;
    gui;
    lastDeduction = null;
    savesParser = new SavesParser;
    constructor(gui) {
        this.gui = gui;
        const actionInput = this.gui.actionInput;
        document.addEventListener("keydown", e => {
            if (e.key === "Escape") {
                this.clearCmdBuffer();
                return false;
            }
        });
        actionInput.addEventListener("keydown", e => {
            e.stopPropagation();
            this.actionInputKeydown(e);
        });
        this.clearCmdBuffer();
        actionInput.addEventListener("blur", ev => {
            this._selStart = actionInput.selectionStart;
            this._selEnd = actionInput.selectionEnd;
        });
    }
    actionInputKeydown(e) {
        const actionInput = this.gui.actionInput;
        if (e.key === "Escape") {
            this.clearCmdBuffer();
            return false;
        }
        if (e.key !== "Enter")
            return false;
        const cmd = actionInput.value;
        if (!cmd.trim())
            return;
        this.cmdBuffer.push(cmd);
        actionInput.value = "";
        this.execCmdBuffer();
    }
    clearCmdBuffer() {
        if (this.escClear) {
            this.cmdBuffer = [];
            this.gui.actionInput.value = "";
            this.gui.hintText.innerText = "请输入命令";
            if (!this.gui.isMobile)
                this.gui.actionInput.focus();
            this.gui.divCmdBtns.querySelectorAll("button").forEach(e => {
                e.disabled = false;
            });
        }
        else {
            this.onEsc();
        }
    }
    execCmdBuffer() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        if (!this.gui.isMobile)
            this.gui.actionInput.focus();
        if (!cmdBuffer.length)
            return;
        this.gui.divCmdBtns.querySelectorAll("button").forEach(e => {
            e.disabled = true;
        });
        try {
            switch (cmdBuffer[0]) {
                case "_copy":
                    hintText.innerText = "可复制定理内容，按Esc取消";
                    return;
                case "d": return this.execDeduct();
                case "save": return this.execSave();
                case "load": return this.execLoad();
                case "help": return this.execHelp();
                case "clear": return this.execClear();
                case "pop": return this.execPop();
                case "meta": return this.execMetaDeduct();
            }
            if (this.gui.unlockedMacro)
                switch (cmdBuffer[0]) {
                    case "macro":
                    case "m": return this.execMacro();
                    case "del": return this.execDel();
                    case "inln": return this.execInline();
                    case "entr": return this.execExpand();
                    case "hyp": if (this.gui.unlockedHyp)
                        return this.execHyp();
                }
            if (cmdBuffer[0].includes(" ")) {
                const queue = cmdBuffer[0].split(" ").filter(e => e);
                this.cmdBuffer = [];
                for (const c of queue) {
                    this.cmdBuffer.push(c);
                    this.execCmdBuffer();
                }
            }
            else {
                if (cmdBuffer.length === 1) {
                    try {
                        if (this.gui.getDeduction(cmdBuffer[0])) {
                            cmdBuffer.unshift("d");
                            this.execCmdBuffer();
                            return;
                        }
                    }
                    catch (e) {
                        // do nothing but wait for unknown cmd
                    }
                    if (this.gui.metarules.includes(cmdBuffer[0].slice(1))) {
                        cmdBuffer[0] = cmdBuffer[0].slice(1);
                        cmdBuffer.unshift("meta");
                        this.execCmdBuffer();
                        return;
                    }
                }
                this.clearCmdBuffer();
                hintText.innerText = `无效命令`;
            }
        }
        catch (e) {
            this.clearCmdBuffer();
            hintText.innerText = `意外的错误：${e}`;
        }
    }
    execExpand() {
        const hintText = this.gui.hintText;
        // ["expand", "(d|p).", {props}, "p.", {props}, "p.", {props},....]
        if (this.cmdBuffer.length < 2) {
            hintText.innerText = `请输入或点击要展开的推理规则或定理\n按Esc取消`;
            this.escClear = true;
            return;
        }
        if (this.cmdBuffer.length % 2 == 0) {
            const item = this.cmdBuffer[this.cmdBuffer.length - 1];
            if (this.gui.formalSystem.deductions[item]) {
                if (!this.escClear) {
                    this.cmdBuffer.pop();
                    this.execCmdBuffer();
                    hintText.innerText += `\n要展开推理规则，请先按Esc返回`;
                    return;
                }
                this.cmdBuffer.push(this.gui.formalSystem.propositions);
                try {
                    this.gui.formalSystem.expandMacroWithDefaultValue(item);
                    this.execCmdBuffer();
                }
                catch (e) {
                    this.cmdBuffer.pop();
                    this.cmdBuffer.pop();
                    this.execCmdBuffer();
                    hintText.innerText += "\n" + e;
                }
            }
            else if (item.startsWith("p")) {
                const p = item.slice(1);
                this.cmdBuffer.push(this.gui.formalSystem.propositions);
                try {
                    this.gui.formalSystem.expandMacroWithProp(Number(p));
                    this.execCmdBuffer();
                }
                catch (e) {
                    this.cmdBuffer.pop();
                    this.cmdBuffer.pop();
                    this.execCmdBuffer();
                    hintText.innerText += "\n" + e;
                }
            }
            else {
                // else if clicked metarule, pop to roll back
                this.cmdBuffer.pop();
                this.execCmdBuffer();
                hintText.innerText += "\n无法展开元规则";
                return;
            }
        }
        else {
            this.gui.updatePropositionList(true);
            this.escClear = false;
            hintText.innerHTML = `目前位于${this.cmdBuffer.map((v, idx, arr) => {
                if (idx % 2 === 0)
                    return null;
                if (v.match(/^p[0-9]+$/)) {
                    return v + ` (${this.gui.stringifyDeductionStep(arr[idx + 1][Number(v.slice(1))].from)})`;
                }
                return `( ${v} )`;
            }).filter(v => v).join(" > ")}共${(this.cmdBuffer.length - 1) / 2}层推理宏内，按Esc返回上一层定理表\n或继续输入/点击要展开的定理`.replaceAll("<", "&lt;").replaceAll(">", "&gt;");
        }
    }
    execInline() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        const formalSystem = this.gui.formalSystem;
        const curLength = cmdBuffer.length;
        if (curLength === 1) {
            hintText.innerText = "请输入或点选使用推理宏得到的定理";
            return;
        }
        if (cmdBuffer[1].startsWith("p"))
            cmdBuffer[1] = cmdBuffer[1].slice(1);
        try {
            if (!formalSystem.propositions[cmdBuffer[1]])
                throw "该定理不存在";
            formalSystem.inlineMacroInProp(Number(cmdBuffer[1]));
            this.gui.updatePropositionList(true);
            this.clearCmdBuffer();
        }
        catch (e) {
            this.clearCmdBuffer();
            hintText.innerText = "展开定理出错：" + e;
        }
    }
    execHelp() {
        const hintText = this.gui.hintText;
        this.clearCmdBuffer();
        document.getElementById("github").click();
    }
    execMetaDeduct() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        const formalSystem = this.gui.formalSystem;
        const curLength = cmdBuffer.length;
        if (curLength === 1) {
            hintText.innerText = "请输入或点选元规则，按Esc取消";
            return;
        }
        if (!this.gui.metarules.includes(cmdBuffer[1])) {
            this.clearCmdBuffer();
            hintText.innerText = "该元规则不存在，元推理取消";
            return;
        }
        const mr = this.gui.formalSystem.metaRules[cmdBuffer[1]];
        // a metarule is chosen, we verify vars and conditions
        const replVarsLength = mr.replaceNames.length;
        const condLength = mr.conditionDeductionIdxs.length;
        const vars = mr.replaceNames;
        const writtenConditions = new Array(condLength); // conditions already inputted by user, used for hint
        let j = 0;
        for (let i = 2; i < 2 + condLength && i < curLength; i++, j++) {
            const idx = cmdBuffer[i];
            if (!formalSystem.generateDeduction(idx)) {
                this.clearCmdBuffer();
                hintText.innerText = "元推理已取消：条件推理规则不存在";
                return;
            }
            writtenConditions[j] = idx;
        }
        writtenConditions.fill("?", j);
        let preInfo = `正在进行元推理 ${cmdBuffer[1]} ${writtenConditions.join(", ")} : \n`;
        for (let i = 2 + condLength; i < 2 + condLength + replVarsLength && i < curLength; i++) {
            preInfo += vars[i - 2 - condLength] + `: ${cmdBuffer[i]}\n`;
        }
        if (curLength < condLength + 2) {
            //wait for conditionIdx input
            hintText.innerText = preInfo + "请输入条件" + this.astparser.stringify(mr.conditions[mr.conditionDeductionIdxs[cmdBuffer.length - 2]]) + "的推理规则名或点推理规则";
            return;
        }
        if (curLength < replVarsLength + condLength + 2) {
            // wait for replvar input
            hintText.innerText = preInfo + "请输入替代" + vars[cmdBuffer.length - 2 - condLength] + "的内容";
            if (!this.gui.actionInput.value) {
                this.gui.actionInput.value = vars[cmdBuffer.length - 2 - condLength];
                this.gui.actionInput.setSelectionRange(0, this.gui.actionInput.value.length);
            }
            return;
        }
        // all params are there, finish it
        try {
            let newName;
            let afterName = null;
            switch (cmdBuffer[1]) {
                case "q":
                    newName = formalSystem.metaQuantifyAxiomSchema(cmdBuffer[2], "元规则生成*");
                    afterName = cmdBuffer[2];
                    break;
                case "c":
                    newName = formalSystem.metaNewConstant([cmdBuffer[2], cmdBuffer[3], cmdBuffer[4]].map(v => this.astparser.parse(v)), "元规则生成*");
                    break;
                case "f":
                    newName = formalSystem.metaNewFunction([cmdBuffer[2], cmdBuffer[3], cmdBuffer[4], cmdBuffer[5]].map(v => this.astparser.parse(v)), "元规则生成*");
                    break;
                case "cdt":
                    newName = formalSystem.metaConditionTheorem(cmdBuffer[2], "元规则生成*");
                    afterName = cmdBuffer[2];
                    break;
                case "dt":
                    newName = formalSystem.metaDeductTheorem(cmdBuffer[2], "元规则生成*");
                    afterName = cmdBuffer[2];
                    break;
                case "idt":
                    newName = formalSystem.metaInvDeductTheorem(cmdBuffer[2], "元规则生成*");
                    afterName = cmdBuffer[2];
                    break;
                case "cvt":
                    newName = formalSystem.metaConditionUniversalTheorem(cmdBuffer[2], "元规则生成*");
                    afterName = cmdBuffer[2];
                    break;
                case "vt":
                    newName = formalSystem.metaUniversalTheorem(cmdBuffer[2], "元规则生成*");
                    afterName = cmdBuffer[2];
                    break;
                case "ifft":
                    // ["m","ifft",sx,ast,nth,  pos, null, name]
                    if (!this.getInputNewDeductionPos(5))
                        return;
                    newName = formalSystem.metaIffTheorem(cmdBuffer[2], [cmdBuffer[3], cmdBuffer[4]].map(v => this.astparser.parse(v)), cmdBuffer[7], "元规则生成*");
                    afterName = cmdBuffer[5];
                    break;
                case "cpt":
                    // ["m","cpt",ss0,  pos, null, name]
                    if (!this.getInputNewDeductionPos(3))
                        return;
                    newName = formalSystem.metaCompleteTheorem(this.astparser.parse(cmdBuffer[2]), cmdBuffer[5], "元规则生成*");
                    afterName = cmdBuffer[3];
                    break;
                default:
                    throw "很抱歉，该规则暂未被作者实现";
            }
            this.gui.addToDeductions(newName, afterName);
            this.clearCmdBuffer();
        }
        catch (e) {
            this.clearCmdBuffer();
            hintText.innerText = preInfo + "错误：" + e;
        }
    }
    execDeduct() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        const formalSystem = this.gui.formalSystem;
        if (cmdBuffer.length === 1) {
            hintText.innerText = "请输入或点选推理规则，按Esc取消";
            return;
        }
        // a deduction is chosen, we verify vars and conditions
        const deduction = this.gui.getDeduction(cmdBuffer[1]);
        if (!deduction) {
            this.clearCmdBuffer();
            hintText.innerText = `推理已取消：\n未找到推理规则 ${cmdBuffer[1]}`;
        }
        const vars = deduction.replaceNames;
        const conditions = deduction.conditions;
        // cmdBuffer : [
        //    "d", d_idx: string, ...conditionIdxs: number[]
        //    ...replVars:ast[], 
        // ]
        const replVarsLength = vars.length;
        const condLength = conditions.length;
        const curLength = cmdBuffer.length;
        const writtenConditions = new Array(condLength); // conditions already inputted by user, used for hint
        let j = 0;
        for (let i = 2; i < 2 + condLength && i < curLength; i++, j++) {
            let idx = Number(cmdBuffer[i]);
            idx = idx < 0 ? formalSystem.propositions.length + idx : idx;
            if (!formalSystem.propositions[idx]) {
                this.clearCmdBuffer();
                hintText.innerText = "推理已取消：条件定理不存在";
                return;
            }
            cmdBuffer[i] = idx;
            writtenConditions[j] = cmdBuffer[i];
        }
        writtenConditions.fill("?", j);
        let preInfo = `正在进行推理 ${cmdBuffer[1] === "." ? this.lastDeduction : cmdBuffer[1]} ${writtenConditions.join(", ")} :  ${this.astparser.stringify(deduction.value)}\n`;
        for (let i = 2 + condLength; i < 2 + condLength + replVarsLength && i < curLength; i++) {
            preInfo += vars[i - 2 - condLength] + `: ${cmdBuffer[i]}\n`;
        }
        if (curLength < condLength + 2) {
            //wait for conditionIdx input
            hintText.innerText = preInfo + "请输入条件" + this.astparser.stringify(deduction.conditions[cmdBuffer.length - 2]) + "的定理编号，或点选定理";
        }
        else if (curLength < replVarsLength + condLength + 2) {
            // wait for replvar input
            hintText.innerText = preInfo + "请输入替代" + vars[cmdBuffer.length - 2 - condLength] + "的内容";
            if (!this.gui.actionInput.value) {
                this.gui.actionInput.value = vars[cmdBuffer.length - 2 - condLength];
                this.gui.actionInput.setSelectionRange(0, this.gui.actionInput.value.length);
            }
        }
        else {
            // all params are there, finish it
            try {
                formalSystem.deduct({
                    deductionIdx: cmdBuffer[1],
                    replaceValues: cmdBuffer.slice(2 + condLength).map((it) => this.astparser.parse(it)),
                    conditionIdxs: cmdBuffer.slice(2, 2 + condLength).map(n => Number(n))
                });
                this.clearCmdBuffer();
                this.gui.updatePropositionList();
                this.lastDeduction = cmdBuffer[1];
            }
            catch (e) {
                this.clearCmdBuffer();
                hintText.innerText = "推理已取消\n" + e;
            }
            return;
        }
    }
    execMacro() {
        const formalSystem = this.gui.formalSystem;
        if (!this.getInputNewDeductionPos(1))
            return; // ["m"].length == 1
        try {
            // ["m", pos, null, name]
            formalSystem.addMacro(this.cmdBuffer[3], "录制*");
            this.gui.addToDeductions(this.cmdBuffer[3], this.cmdBuffer[1]);
            this.execClear();
        }
        catch (e) {
            this.clearCmdBuffer();
            this.gui.hintText.innerText = e;
        }
    }
    execPop() {
        this.gui.formalSystem.removePropositions(1);
        this.gui.updatePropositionList(true);
        this.clearCmdBuffer();
    }
    execDel() {
        if (this.cmdBuffer.length === 1) {
            this.gui.hintText.innerText = "请输入要删除的推理规则名称";
            return;
        }
        try {
            const pos = this.gui.deductions.indexOf(this.cmdBuffer[1]);
            if (pos === -1)
                throw "列表中无此规则";
            this.gui.formalSystem.removeDeduction(this.cmdBuffer[1]);
            this.gui.deductions.splice(pos, 1);
            this.gui.updateDeductionList();
            this.clearCmdBuffer();
        }
        catch (e) {
            this.clearCmdBuffer();
            this.gui.hintText.innerText = "删除推理规则失败：" + e;
        }
    }
    execSave() {
        if (this.cmdBuffer.length > 1)
            return;
        const fs = this.gui.formalSystem;
        this.gui.hintText.innerText = "正在保存";
        const data = this.savesParser.serialize(this.gui.deductions, fs);
        if (!navigator.clipboard) {
            this.gui.actionInput.value = data;
            this.gui.actionInput.select();
            if (document.execCommand("copy")) {
                this.clearCmdBuffer();
                this.gui.hintText.innerText = "进度成功保存至剪贴板";
            }
            else {
                this.gui.hintText.innerText = "无法访问剪贴板，请手动复制以下内容：";
            }
        }
        else {
            navigator.clipboard.writeText(data).then(() => {
                this.clearCmdBuffer();
                this.gui.hintText.innerText = "进度成功保存至剪贴板";
            });
        }
    }
    execLoad() {
        if (this.cmdBuffer.length > 1) {
            let ds;
            try {
                const { fs, arrD } = this.savesParser.deserialize(this.cmdBuffer[1]);
                this.gui.formalSystem = fs;
                this.gui.deductions = arrD;
            }
            catch (e) {
                this.clearCmdBuffer();
                this.gui.hintText.innerText = "进度导入失败";
                return;
            }
            this.gui.updatePropositionList(true);
            this.gui.updateDeductionList();
            this.execClear();
        }
        else {
            this.gui.hintText.innerText = "请在此粘贴进度";
        }
    }
    execClear() {
        this.gui.formalSystem.removePropositions();
        this.gui.updatePropositionList(true);
        this.clearCmdBuffer();
    }
    execHyp() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        const formalSystem = this.gui.formalSystem;
        if (cmdBuffer[cmdBuffer.length - 1] === "$") {
            this.clearCmdBuffer();
            return;
        }
        if (cmdBuffer.length > 1) {
            try {
                formalSystem.addHypothese(this.astparser.parse(cmdBuffer.pop()));
                this.gui.updatePropositionList();
            }
            catch (e) {
                this.clearCmdBuffer();
                hintText.innerText = `解析错误：` + e;
                return;
            }
        }
        hintText.innerText = `请输入假设命题p${formalSystem.propositions.length}，或按“Esc”结束`;
    }
    onClickSubAst(idx, inserted) {
        const cmdBuffer = this.cmdBuffer;
        // click prop just for copy
        if (idx.startsWith("p") && !cmdBuffer.length || cmdBuffer[0] === "_copy") {
            cmdBuffer.push("_copy");
            this.execCmdBuffer();
            this.replaceActionInputFromClick(inserted);
            return;
        }
        if (!cmdBuffer.length || (cmdBuffer.length === 1 && (cmdBuffer[0] === "d" || cmdBuffer[0] === "meta"))) {
            // click item to start a cmd
            cmdBuffer.push(idx);
            this.execCmdBuffer();
            return;
        }
        // deduction started, but wait for click props or replvars
        if (cmdBuffer[0] === "d" && cmdBuffer.length >= 2) {
            const deduction = this.gui.formalSystem.deductions[cmdBuffer[1]];
            const vars = deduction.replaceNames.length;
            const conditions = deduction.conditions.length;
            if (conditions + 2 > cmdBuffer.length) {
                //wait for conditionIdx input
                if (!idx.match(/^p[0-9]+$/)) {
                    this.gui.hintText.innerText += "\n请点选定理！";
                    return;
                }
                cmdBuffer.push(Number(idx.slice(1)));
                this.execCmdBuffer();
            }
            else {
                // wait for replvar input
                this.replaceActionInputFromClick(inserted);
            }
        }
        else if (cmdBuffer[0] === "hyp") {
            // wait for hypothese input, user can click both d&p terms
            this.replaceActionInputFromClick(inserted);
        }
        else if (cmdBuffer[0] === "meta" && cmdBuffer.length >= 2) {
            const mr = this.gui.formalSystem.metaRules[cmdBuffer[1]];
            const conditions = mr.conditionDeductionIdxs.length;
            if (conditions + 2 > cmdBuffer.length) {
                //wait for conditionIdx input
                if (!this.gui.formalSystem.deductions[idx]) {
                    this.gui.hintText.innerText += "\n请点选推理规则！";
                    return;
                }
                cmdBuffer.push(idx);
                this.execCmdBuffer();
            }
            else {
                // wait for replvar input
                this.replaceActionInputFromClick(inserted);
            }
        }
        else if (cmdBuffer[0] === "entr" || cmdBuffer[0] === "inln") {
            // wait for both d&p terms
            cmdBuffer.push(idx);
            this.execCmdBuffer();
        }
    }
    _selStart = 0;
    _selEnd = 0;
    replaceActionInputFromClick(inserted) {
        const actionInput = this.gui.actionInput;
        if (!this.gui.isMobile)
            actionInput.focus();
        const val = actionInput.value;
        const start = this._selStart;
        const end = this._selEnd;
        actionInput.value = val.substring(0, start) + inserted + val.substring(end);
        actionInput.selectionStart = this._selStart = start;
        actionInput.selectionEnd = this._selEnd = start + inserted.length;
        // alert(start + "|" + end + " => " + actionInput.selectionStart + "|" + actionInput.selectionEnd)
    }
    getInputNewDeductionPos(prevLength) {
        const cmdLen = this.cmdBuffer.length - prevLength + 1;
        // ["m", pos, null, name]
        if (cmdLen === 1 || cmdLen === 3) {
            // ["m"] || ["m", pos, null]
            let i = 0;
            while (this.gui.formalSystem.deductions["s" + (++i)])
                ;
            this.gui.actionInput.value = "s" + i;
            this.gui.actionInput.selectionStart = 1;
            this.gui.actionInput.selectionEnd = this.gui.actionInput.value.length;
            this.gui.hintText.innerText = cmdLen === 1 ? "请输入在哪个规则后方插入新规则。若直接输入新规则名称，则默认插入至规则表最后" : "请输入新规则名称";
            // ["m", pos] || ["m", name] || ["m", pos, null, name]
            return false;
        }
        if (cmdLen === 2) {
            const pos = this.gui.deductions.includes(this.cmdBuffer[prevLength]);
            if (pos) {
                // ["m", pos]
                this.cmdBuffer.push(null);
                // ["m", pos, null]
                return this.getInputNewDeductionPos(prevLength);
            }
            else {
                // ["m", name]
                this.cmdBuffer.splice(prevLength, 0, null, null);
                // ["m", pos=null, null, name]
                return this.getInputNewDeductionPos(prevLength);
            }
        }
        // ["m", pos, null, name]
        const n = this.cmdBuffer[prevLength + 2];
        if (n.match(/^<>uvdcamp\.]/)) {
            this.cmdBuffer.pop();
            const res = this.getInputNewDeductionPos(prevLength);
            this.gui.hintText.innerText = "以.<>uvdcamp开头的推理规则名称由系统保留，请重新命名";
            return res;
        }
        if (this.gui.formalSystem.deductions[n]) {
            this.cmdBuffer.pop();
            const res = this.getInputNewDeductionPos(prevLength);
            this.gui.hintText.innerText = `推理规则名称${n}已存在或被系统保留，请重新命名`;
            return res;
        }
        return true;
    }
    onEsc() {
        const hintText = this.gui.hintText;
        if (this.cmdBuffer[0] === "entr") {
            // ["expand", "(d|p).", {props}, "p.", {props}, "p.", {props},....]
            this.gui.formalSystem.propositions = this.cmdBuffer.pop();
            this.cmdBuffer.pop();
            this.execCmdBuffer();
            if (this.escClear) {
                this.gui.updatePropositionList(true);
            }
        }
        else
            throw "cannot reached";
    }
}
//# sourceMappingURL=cmd.js.map