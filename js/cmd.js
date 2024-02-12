import { ASTParser } from "./astparser.js";
import { SavesParser } from "./savesparser.js";
export class FSCmd {
    cmdBuffer = [];
    astparser = new ASTParser;
    escClear = true;
    gui;
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
                case "macro":
                case "m": return this.execMacro();
                case "expand": return this.execExpand();
                case "save": return this.execSave();
                case "load": return this.execLoad();
                case "help": return this.execHelp();
                case "hyp": return this.execHyp();
                case "d": return this.execDeduct();
                case "meta": return this.execMetaDeduct();
                case "pop": return this.execPop();
                case "popd": return this.execPopD();
                case "clear": return this.execClear();
                default:
                    if (cmdBuffer.length === 1 && cmdBuffer[0].startsWith("d")) {
                        cmdBuffer.push(cmdBuffer[0].substring(1));
                        cmdBuffer[0] = "d";
                        this.execCmdBuffer();
                    }
                    else {
                        this.clearCmdBuffer();
                        hintText.innerText = `无效命令`;
                    }
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
            if (this.cmdBuffer[this.cmdBuffer.length - 1].startsWith("d")) {
                if (!this.escClear) {
                    this.cmdBuffer.pop();
                    this.execCmdBuffer();
                    hintText.innerText += `\n要展开推理规则，请先按Esc返回`;
                    return;
                }
                const d = this.cmdBuffer[this.cmdBuffer.length - 1].slice(1);
                this.cmdBuffer.push(this.gui.formalSystem.propositions);
                try {
                    this.gui.formalSystem.expandMacroWithDefaultValue(Number(d));
                    this.execCmdBuffer();
                }
                catch (e) {
                    this.cmdBuffer.pop();
                    this.cmdBuffer.pop();
                    this.execCmdBuffer();
                    hintText.innerText += "\n" + e;
                }
            }
            else if (this.cmdBuffer[this.cmdBuffer.length - 1].startsWith("p")) {
                const p = this.cmdBuffer[this.cmdBuffer.length - 1].slice(1);
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
                return;
            }
        }
        else {
            this.gui.updatePropositionList(true);
            this.escClear = false;
            hintText.innerText = `目前位于第${(this.cmdBuffer.length - 1) / 2}层推理宏内，按Esc返回上一层定理表\n或继续输入/点击要展开的定理`;
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
        if (cmdBuffer.length === 1) {
            hintText.innerText = "请输入或点选元规则，按Esc取消";
            return;
        }
        // a metarule is chosen, we verify vars and conditions
        let preInfo = `正在执行元规则m${cmdBuffer[1]}:\n`;
        switch (cmdBuffer[1]) {
            case "q":
                if (cmdBuffer.length === 2) {
                    hintText.innerText = preInfo + "请输入匹配条件( ⊢ $$0)的公理规则，按Esc取消";
                    return;
                }
                if (cmdBuffer.length === 3) {
                    hintText.innerText = preInfo + "请输入替代$$1的内容，按Esc取消";
                    return;
                }
                try {
                    formalSystem.deductions[formalSystem.metaQuantifyAxiomSchema(Number(cmdBuffer[2]), this.astparser.parse(cmdBuffer[3]))].from = `*mq d${cmdBuffer[2]}`;
                    this.gui.updateDeductionList();
                    this.clearCmdBuffer();
                }
                catch (e) {
                    this.clearCmdBuffer();
                    hintText.innerText = preInfo + "错误：" + e;
                }
                break;
            case "c":
                if (cmdBuffer.length < 5) {
                    hintText.innerText = `请输入替代${['$$0', '$$1', '$$2'][cmdBuffer.length - 2]}的内容，按Esc取消`;
                    return;
                }
                try {
                    formalSystem.metaNewConstant(cmdBuffer.slice(2).map(ast => this.astparser.parse(ast)));
                    this.gui.updateDeductionList();
                    this.gui.updatePropositionList(true); //update const color
                    this.clearCmdBuffer();
                }
                catch (e) {
                    this.clearCmdBuffer();
                    hintText.innerText = "元规则执行错误：" + e;
                }
                break;
            case "f":
                if (cmdBuffer.length < 6) {
                    hintText.innerText = `请输入替代${['$$0', '$$1', '$$2', '$$3'][cmdBuffer.length - 2]}的内容，按Esc取消`;
                    return;
                }
                try {
                    formalSystem.metaNewFunction(cmdBuffer.slice(2).map(ast => this.astparser.parse(ast)));
                    this.gui.updateDeductionList();
                    this.gui.updatePropositionList(true); // update fn color
                    this.clearCmdBuffer();
                }
                catch (e) {
                    this.clearCmdBuffer();
                    hintText.innerText = "元规则执行错误：" + e;
                }
                break;
            case "dt":
                if (cmdBuffer.length === 2) {
                    hintText.innerText = "请输入或点选条件推理规则，按Esc取消";
                    return;
                }
                try {
                    formalSystem.metaDeductTheorem(Number(cmdBuffer[2]));
                    this.gui.updateDeductionList();
                    this.clearCmdBuffer();
                }
                catch (e) {
                    this.clearCmdBuffer();
                    hintText.innerText = "元规则执行错误：" + e;
                }
                break;
            case "qt":
                if (cmdBuffer.length === 2) {
                    hintText.innerText = "请输入或点选条件推理规则，按Esc取消";
                    return;
                }
                if (cmdBuffer.length === 3) {
                    hintText.innerText = "请输入替代$$0的变量名，按Esc取消";
                    return;
                }
                try {
                    formalSystem.metaUniversalTheorem(Number(cmdBuffer[2]), this.astparser.parse(cmdBuffer[3]));
                    this.gui.updateDeductionList();
                    this.clearCmdBuffer();
                }
                catch (e) {
                    this.clearCmdBuffer();
                    hintText.innerText = "元规则执行错误：" + e;
                }
                break;
            default: hintText.innerText = "该元规则不存在或作者暂未实现";
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
        const deduction = formalSystem.deductions[cmdBuffer[1]];
        const vars = deduction.replaceNames;
        const conditions = deduction.conditions;
        // cmdBuffer : [
        //    "d", d_idx: number, 
        //    ...replVars:ast[], ...conditionIdxs: number[]
        // ]
        const replVarsLength = vars.length;
        const conditionIdxsLength = conditions.length;
        const writtenConditions = new Array(conditionIdxsLength); // conditions already inputted by user, used for hint
        let j = 0;
        for (let i = 2 + replVarsLength; i < 2 + replVarsLength + conditionIdxsLength && i < cmdBuffer.length; i++, j++) {
            const idx = cmdBuffer[i];
            if (!formalSystem.propositions[idx]) {
                this.clearCmdBuffer();
                hintText.innerText = "推理已取消：条件定理不存在";
                return;
            }
            writtenConditions[j] = idx;
        }
        writtenConditions.fill("?", j);
        let preInfo = `正在进行推理${writtenConditions.join(", ")} d${cmdBuffer[1]}:\n`;
        for (let i = 2; i < 2 + replVarsLength && i < cmdBuffer.length; i++) {
            preInfo += vars[i - 2] + `: ${cmdBuffer[i]}\n`;
        }
        if (replVarsLength + 2 > cmdBuffer.length) {
            // wait for replvar input
            hintText.innerText = preInfo + "请输入替代" + vars[cmdBuffer.length - 2] + "的内容";
        }
        else if (replVarsLength + conditionIdxsLength + 2 > cmdBuffer.length) {
            //wait for conditionIdx input
            hintText.innerText = preInfo + "请输入条件" + this.gui.stringify(deduction.conditions[cmdBuffer.length - replVarsLength - 2]) + "的定理编号，或点选定理";
        }
        else {
            // all params are there, finish it
            try {
                formalSystem.deduct({
                    deductionIdx: Number(cmdBuffer[1]),
                    replaceValues: cmdBuffer.slice(2, 2 + replVarsLength).map((it) => this.astparser.parse(it)),
                    conditionIdxs: cmdBuffer.slice(2 + replVarsLength).map(n => Number(n))
                });
                this.clearCmdBuffer();
                this.gui.updatePropositionList();
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
        try {
            formalSystem.addMacro(formalSystem.propositions.length - 1, "录制");
            this.gui.updateDeductionList();
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
    execPopD() {
        const ds = this.gui.formalSystem.deductions;
        if (!ds[ds.length - 1].from.includes("[S]")) {
            if (this.gui.formalSystem.propositions.length) {
                this.clearCmdBuffer();
                this.gui.hintText.innerText = "无法删除规则：需先清空定理列表";
                return;
            }
            this.gui.formalSystem.removeLastDeduction();
            this.gui.updateDeductionList(true);
            this.execClear();
        }
        else {
            this.clearCmdBuffer();
            this.gui.hintText.innerText = "无法删除系统推理规则";
        }
    }
    execSave() {
        if (this.cmdBuffer.length > 1)
            return;
        const fs = this.gui.formalSystem;
        this.gui.hintText.innerText = "正在保存";
        const data = this.savesParser.serialize(fs);
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
                this.gui.formalSystem = this.savesParser.deserialize(this.cmdBuffer[1]);
            }
            catch (e) {
                this.clearCmdBuffer();
                this.gui.hintText.innerText = "进度导入失败";
                return;
            }
            this.gui.updatePropositionList(true);
            this.gui.updateDeductionList(true);
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
        if (formalSystem.propositions.findIndex(e => e.from) !== -1) {
            this.clearCmdBuffer();
            hintText.innerText = `无法添加假设条件：假设须添加在其它定理之前`;
            return;
        }
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
        if (!cmdBuffer.length) {
            if (idx[0] === "d") {
                // click to start a deduction
                cmdBuffer.push("d", Number(idx.slice(1)));
                this.execCmdBuffer();
            }
            if (idx[0] === "m") {
                // click to start a meta rule
                cmdBuffer.push("meta", idx.slice(1));
                this.execCmdBuffer();
            }
            return;
        }
        // deduction started, but wait for click props or replvars
        if (cmdBuffer[0] === "d" && cmdBuffer.length >= 2) {
            const deduction = this.gui.formalSystem.deductions[cmdBuffer[1]];
            const vars = deduction.replaceNames;
            const conditions = deduction.conditions;
            const replVarsLength = vars.length;
            const conditionIdxsLength = conditions.length;
            if (replVarsLength + 2 > cmdBuffer.length) {
                // wait for replvar input, user can click both d&p terms
                this.replaceActionInputFromClick(inserted);
            }
            else if (idx[0] === "p" && replVarsLength + conditionIdxsLength + 4 > cmdBuffer.length) {
                //wait for conditionIdx input
                cmdBuffer.push(Number(idx.slice(1)));
                this.execCmdBuffer();
            }
        }
        else if (cmdBuffer[0] === "hyp") {
            // wait for hypothese input, user can click both d&p terms
            this.replaceActionInputFromClick(inserted);
        }
        else if (cmdBuffer[0] === "meta") {
            switch (cmdBuffer[1]) {
                case "qt":
                    if (cmdBuffer.length === 2) {
                        if (idx[0] === "d") {
                            cmdBuffer.push(Number(idx.slice(1)));
                            this.execCmdBuffer();
                        }
                    }
                    else {
                        this.replaceActionInputFromClick(inserted);
                    }
                    break;
                case "q":
                    if (cmdBuffer.length === 2) {
                        if (idx[0] === "d") {
                            cmdBuffer.push(Number(idx.slice(1)));
                            this.execCmdBuffer();
                        }
                    }
                    else {
                        this.replaceActionInputFromClick(inserted);
                    }
                    break;
                case "dt":
                    // wait for deduct idx input, user can click d terms
                    cmdBuffer.push(Number(idx.slice(1)));
                    this.execCmdBuffer();
            }
        }
        else if (cmdBuffer[0] === "expand") {
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
    onEsc() {
        const hintText = this.gui.hintText;
        if (this.cmdBuffer[0] === "expand") {
            // ["expand", "(d|p).", {props}, "p.", {props}, "p.", {props},....]
            this.gui.formalSystem.setPropositions(this.cmdBuffer.pop());
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