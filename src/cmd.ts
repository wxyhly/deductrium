import { ASTParser } from "./astparser.js";
import { Deduction } from "./formalsystem.js";
import { FSGui } from "./gui.js";
import { SavesParser } from "./savesparser.js";

export class FSCmd {
    cmdBuffer: any[] = [];
    astparser = new ASTParser;
    gui: FSGui;
    savesParser = new SavesParser;
    constructor(gui: FSGui) {
        this.gui = gui;
        const actionInput = this.gui.actionInput;
        document.addEventListener("keydown", e => {
            if (e.key === "Escape") {
                this.clearCmdBuffer();
                return false;
            }
        });
        actionInput.addEventListener("keydown", e => this.actionInputKeydown(e));
        this.clearCmdBuffer();
    }
    actionInputKeydown(e: { key: string }) {
        const actionInput = this.gui.actionInput;
        if (e.key === "Escape") {
            this.clearCmdBuffer();
            return false;
        }
        if (e.key !== "Enter") return false;
        const cmd = actionInput.value;
        if (!cmd.trim()) return;
        this.cmdBuffer.push(cmd);
        actionInput.value = "";
        this.execCmdBuffer();
    }

    clearCmdBuffer() {
        this.cmdBuffer = [];
        this.gui.actionInput.value = "";
        this.gui.hintText.innerText = "请输入命令";
        if (!this.gui.isMobile) this.gui.actionInput.focus();
    }
    execCmdBuffer() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        if (!this.gui.isMobile) this.gui.actionInput.focus();
        if (!cmdBuffer.length) return;
        try {
            switch (cmdBuffer[0]) {
                case "macro": case "m": return this.execMacro();
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
                    } else {
                        this.clearCmdBuffer();
                        hintText.innerText = `无效命令`;
                    }
            }

        } catch (e) {
            this.clearCmdBuffer();
            hintText.innerText = `意外的错误：${e}`;
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
        switch (Number(cmdBuffer[1])) {
            case 0:
                if (cmdBuffer.length === 2) {
                    hintText.innerText = "请输入或点选条件推理规则，按Esc取消";
                    return;
                }
                try {
                    formalSystem.deductions[formalSystem.metaDeduct0(Number(cmdBuffer[2]))].from = `*m0 d${cmdBuffer[2]}`;
                    this.gui.updateDeductionList();
                    this.clearCmdBuffer();
                } catch (e) {
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
        const writtenConditions = new Array<string>(conditionIdxsLength); // conditions already inputted by user, used for hint
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
        } else if (replVarsLength + conditionIdxsLength + 2 > cmdBuffer.length) {
            //wait for conditionIdx input
            hintText.innerText = preInfo + "请输入条件" + this.gui.stringify(deduction.conditions[cmdBuffer.length - replVarsLength - 2]) + "的定理编号，或点选定理";
        } else {
            // all params are there, finish it
            const preProps = formalSystem.propositions.length;
            try {
                formalSystem.deduct({
                    deductionIdx: cmdBuffer[1],
                    replaceValues: cmdBuffer.slice(2, 2 + replVarsLength).map(
                        (it: string) => this.astparser.parse(it)
                    ),
                    conditionIdxs: cmdBuffer.slice(2 + replVarsLength)
                });
                this.clearCmdBuffer();
                this.gui.updatePropositionList();
            } catch (e) {
                this.clearCmdBuffer();
                hintText.innerText = "推理已取消\n" + e;
            }
            return;
        }
    }
    execMacro() {
        const formalSystem = this.gui.formalSystem;
        try {
            formalSystem.deductions[formalSystem.addMacro(formalSystem.propositions.length - 1)].from = "*录制宏";
            this.gui.updateDeductionList();
            this.execClear();
        } catch (e) {
            this.clearCmdBuffer();
            this.gui.hintText.innerText = e;
        }
    }
    execPop() {
        const ps = this.gui.formalSystem.propositions;
        this.gui.formalSystem.removePropositions(1);
        for (let i = ps.length - 1; i >= 0; i--) {
            if (ps[i].from[0]?.isSubstep) this.gui.formalSystem.removePropositions(1);
            else break;
        }
        this.gui.updatePropositionList(true);
        this.clearCmdBuffer();
    }
    execPopD() {
        const ds = this.gui.formalSystem.deductions;
        if (ds[ds.length - 1].from.startsWith("*")) {
            this.gui.formalSystem.deductions.pop();
            this.gui.updateDeductionList(true);
            this.execClear();
        } else {
            this.clearCmdBuffer();
            this.gui.hintText.innerText = "无法删除系统推理规则";
        }
    }
    execSave() {
        if (this.cmdBuffer.length > 1) return;
        const ds = this.gui.formalSystem.deductions;
        this.gui.hintText.innerText = "正在保存";
        const data = this.savesParser.serialize(JSON.stringify(ds));
        if (!navigator.clipboard) {
            this.gui.actionInput.value = data;
            this.gui.actionInput.select();
            if (document.execCommand("copy")) {
                this.clearCmdBuffer();
                this.gui.hintText.innerText = "进度成功保存至剪贴板";
            } else {
                this.gui.hintText.innerText = "无法访问剪贴板，请手动复制以下内容：";
            }
        } else {
            navigator.clipboard.writeText(data).then(() => {
                this.clearCmdBuffer();
                this.gui.hintText.innerText = "进度成功保存至剪贴板";
            });
        }
    }
    execLoad() {
        if (this.cmdBuffer.length > 1) {
            let ds: Deduction[];
            try {
                ds = JSON.parse(this.savesParser.deserialize(this.cmdBuffer[1]));
            } catch (e) {
                this.clearCmdBuffer();
                this.gui.hintText.innerText = "进度导入失败";
                return;
            }
            this.gui.formalSystem.deductions = ds;
            this.gui.updateDeductionList(true);
            this.execClear();
        } else {
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
        if (formalSystem.propositions.length !== formalSystem.hypothesisAmount) {
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
            } catch (e) {
                this.clearCmdBuffer();
                hintText.innerText = `解析错误：` + e;
                return;
            }
        }
        hintText.innerText = `请输入假设命题p${formalSystem.propositions.length}，或按“Esc”结束`;
    }
    onClickSubAst(idx: string, inserted: string) {
        const cmdBuffer = this.cmdBuffer;
        if (!cmdBuffer.length) {
            if (idx[0] === "d") {
                // click to start a deduction
                cmdBuffer.push("d", idx.slice(1));
                this.execCmdBuffer();
            }
            if (idx[0] === "m") {
                // click to start a meta rule
                cmdBuffer.push("meta", idx.slice(1));
                this.execCmdBuffer();
            }
            return;
        }
        // cmd has been started, but wait for click props
        if (cmdBuffer[0] === "d" && cmdBuffer.length >= 2) {
            const deduction = this.gui.formalSystem.deductions[cmdBuffer[1]];
            const vars = deduction.replaceNames;
            const conditions = deduction.conditions;
            const replVarsLength = vars.length;
            const conditionIdxsLength = conditions.length;
            if (replVarsLength + 2 > cmdBuffer.length) {
                // wait for replvar input, user can click both d&p terms
                this.replaceActionInputFromClick(inserted);
            } else if (idx[0] === "p" && replVarsLength + conditionIdxsLength + 4 > cmdBuffer.length) {
                //wait for conditionIdx input
                cmdBuffer.push(idx.slice(1));
                this.execCmdBuffer();
            }
        } else if (cmdBuffer[0] === "hyp") {
            // wait for hypothese input, user can click both d&p terms
            this.replaceActionInputFromClick(inserted);
        } else if (cmdBuffer[0] === "meta") {
            switch (cmdBuffer[1]) {
                case "0":
                    // wait for deduct idx input, user can click d terms
                    cmdBuffer.push(idx.slice(1));
                    this.execCmdBuffer();
            }
        }
    }
    replaceActionInputFromClick(inserted: string) {
        const actionInput = this.gui.actionInput;
        if (!this.gui.isMobile) actionInput.focus();
        const val = actionInput.value;
        const start = actionInput.selectionStart;
        const end = actionInput.selectionEnd;
        if (start === end) {
            actionInput.value = val.substring(0, start) + inserted + val.substring(actionInput.selectionEnd);
            actionInput.selectionStart = start;
            actionInput.selectionEnd = start + inserted.length;
        } else {
            actionInput.value = val.replace(new RegExp(val.substring(start, end), "g"), inserted);
            actionInput.selectionStart = actionInput.value.length;
            actionInput.selectionEnd = actionInput.value.length;
        }
    }

}