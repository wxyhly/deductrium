import { TR } from "../lang.js";
import { AST } from "./astmgr.js";
import { ASTParser } from "./astparser.js";
import { Deduction } from "./formalsystem.js";
import { FSGui } from "./gui.js";
import { SavesParser } from "./savesparser.js";

export class FSCmd {
    cmdBuffer: any[] = [];
    astparser = new ASTParser;
    escClear = true;
    pListMasked = false;
    autoCompleteIdx = -1;
    gui: FSGui;
    lastDeduction: string = null;
    savesParser = new SavesParser;
    // onsave: () => string;
    // onload: (s: string) => void;
    // onreset: () => void;
    constructor(gui: FSGui) {
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
        })
        actionInput.addEventListener("input", () => {
            this.actionInputChange();
        });

        document.addEventListener("click", e => {
            if (!(e.target as HTMLElement).closest("#action-input")) {
                document.getElementById("autocomplete-list").style.display = "none";
            }
        });
    }
    actionInputKeydown(e: { key: string }) {
        const actionInput = this.gui.actionInput;

        // autoComplete:

        let currentIndex = this.autoCompleteIdx;
        const list = document.getElementById("autocomplete-list") as HTMLUListElement;
        if (e.key === "Escape") {
            this.showhints([]);
            this.clearCmdBuffer();
            return false;
        }
        const items = list.querySelectorAll("li");
        if (list.style.display !== "none" && items.length) {
            if (e.key === "ArrowDown") {
                currentIndex = (currentIndex + 1) % items.length;
            } else if (e.key === "ArrowUp") {
                currentIndex = (currentIndex - 1 + items.length) % items.length;
            } else if (e.key === "Enter" || e.key === "Tab") {
                if (currentIndex >= 0) {
                    actionInput.value = items[currentIndex].getAttribute("data-value") || "";
                }
            }
        }
        items.forEach((item, i) => {
            item.classList.toggle("active", i === currentIndex);
            if (i === currentIndex) {
                item.scrollIntoView({ block: "nearest" });
            }
        });
        this.autoCompleteIdx = currentIndex;

        // other logics

        if (e.key !== "Enter") return false;

        if (this.cmdBuffer[this.cmdBuffer.length - 1] === "## error") {
            this.escClear = true;
            const lastCmd = actionInput.value;
            this.clearCmdBuffer();
            actionInput.value = lastCmd;
        }
        this.showhints([]);
        let cmd = actionInput.value;
        if (cmd.includes("`")) cmd = cmd.replaceAll("`", "'");
        if (!cmd.trim()) return;
        this.cmdBuffer.push(cmd);
        actionInput.value = "";
        this.execCmdBuffer();
    }
    // hint: [displayHTML, insertText]
    showhints(hints: [[HTMLElement, HTMLElement], string][]) {
        const list = document.getElementById("autocomplete-list") as HTMLUListElement;
        const input = this.gui.actionInput;
        this.autoCompleteIdx = -1;
        list.innerHTML = "";
        if (!hints.length) {
            list.style.display = "none";
            return;
        }
        list.style.display = "block";
        hints.forEach(([html, cmd]) => {
            const li = document.createElement("li");
            for (const h of html) li.appendChild(h);
            li.setAttribute("data-value", cmd);
            li.onclick = () => {
                input.value = cmd;
                list.style.display = "none";
                input.focus();
                if (cmd.startsWith("d ")) {
                    this.actionInputKeydown({ key: "Enter" });
                }
            };
            list.appendChild(li);
        });

    }
    actionInputChange() {
        const value = this.gui.actionInput.value;
        let list = [];

        if (this.cmdBuffer.length === 0 || (
            this.cmdBuffer.length === 1 && this.cmdBuffer[0] === "d"
        ) || (this.cmdBuffer.length === 2 && (this.cmdBuffer[0] === "meta" && this.cmdBuffer[1] === "ifft"))) {

            const prefix = this.gui.formalSystem.fastmetarules.replace(":", "");
            let subValue = value;
            let pre = "";
            if (this.cmdBuffer[0] !== "meta") {
                while (prefix.includes(subValue[0])) {
                    pre += subValue[0];
                    subValue = subValue.slice(1);
                }
            }
            if (subValue) {
                list = this.gui.deductions.filter(e => {
                    if (this.cmdBuffer[0] === "meta" && this.cmdBuffer[1] === "ifft") {
                        const d = this.gui.formalSystem.deductions[e];
                        if (d.conditions.length) return false;
                        if (d.conclusion.name !== "<>") return false;
                        if (d.conclusion.type !== "sym") return false;
                    }
                    return e.toLowerCase().startsWith(subValue.toLowerCase())
                }).map(e => pre + e);
                if (!list.includes(value)) list.unshift(value);
                const time = new Date().getTime();
                list = list.map(
                    e => {
                        let d: Deduction;
                        try {
                            // wait for 150ms, then stop generate more autocomplete items 
                            if (new Date().getTime() - time > 150) return [];
                            d = this.gui.getDeduction(e);
                            if (!d) throw null;
                        } catch (e) {
                            return [];
                        }
                        const cmd = document.createElement("span");
                        cmd.className = "cmd";
                        cmd.appendChild(document.createTextNode("[D]"));
                        cmd.appendChild(this.gui.tree2HTML(this.gui.formalSystem.getDeductionTokens(e)));
                        const hint = document.createElement("span");
                        hint.className = 'hint';
                        hint.innerText = d ? this.astparser.stringifyTight(d.value) : "";
                        return [[cmd, hint], "d " + e]
                    }
                ).filter(e => e.length);
            }
            // cmd, only for empty cmdbuffer
            if (value && this.cmdBuffer.length === 0) {
                const unlockedCmd = ["pop", "clear"];
                if (!document.getElementById("hyp-btn").classList.contains("hide")) unlockedCmd.push("hyp");
                if (!document.getElementById("macro-btns").classList.contains("hide")) unlockedCmd.push("entr", "del", "inln");
                if (!document.getElementById("dir-btn").classList.contains("hide")) unlockedCmd.push("mkdir");
                if (!document.getElementById("rename-btn").classList.contains("hide")) unlockedCmd.push("rename");
                list.push(...unlockedCmd.filter(e => e.startsWith(value)).map(
                    e => {
                        const cmd = document.createElement("span");
                        cmd.className = "cmd";
                        cmd.appendChild(document.createTextNode("[C] " + e));
                        const hint = document.createElement("span");
                        hint.className = 'hint';
                        hint.innerText = TR("命令：") + e;
                        return [[cmd, hint], e];
                    }
                ));
            }
        }
        this.showhints(list);

    }
    clearCmdBuffer() {
        if (this.pListMasked) { this.gui.clearPListMasked(); this.pListMasked = false; }
        if (this.escClear) {
            this.cmdBuffer = [];
            this.gui.actionInput.value = "";
            this.gui.hintText.innerText = TR("请输入命令");
            if (!this.gui.isMobile) this.gui.actionInput.focus();
            this.gui.cmdBtns.forEach(e => {
                e.disabled = false;
            });
        } else {
            this.onEsc();
        }
    }
    execCmdBuffer() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        if (!this.gui.isMobile) this.gui.actionInput.focus();
        if (!cmdBuffer.length) return;
        this.gui.cmdBtns.forEach(e => {
            e.disabled = true;
        });
        try {
            switch (cmdBuffer[0]) {
                case "copy": {
                    hintText.innerText = TR("可复制定理内容，按Esc取消");
                    if (cmdBuffer.length > 1) {
                        cmdBuffer.shift();
                        this.execCmdBuffer();
                    }
                    return;
                }
                case "d": return this.execDeduct();
                // case "help": return this.execHelp();
                case "clear": return this.execClear();
                case "pop": return this.execPop();
                case "meta": return this.execMetaDeduct();
            }
            if (this.gui.unlockedMacro) switch (cmdBuffer[0]) {
                case "metamacro": case "meta-macro": case "meta-m": case "mm": return this.execMetaMacro();
                case "macro": case "m": return this.execMacro();
                case "del": return this.execDel();
                case "inln": return this.execInline();
                case "entr": return this.execExpand();
                case "hyp": if (this.gui.unlockedHyp) return this.execHyp(); break;
                case "rename": if (this.gui.unlockedRename) return this.execRename(); break;
                case "mkdir": if (this.gui.unlockedFolder) return this.execNewFolder(); break;
                case "op-dir": if (this.gui.unlockedFolder) return this.execOpFolder(); break;
            }

            if (cmdBuffer[0].includes(" ")) {
                const queue = (cmdBuffer[0] as string).replaceAll(/\s([@=\+\-\*XUI><&\|\\]|<>)\s/g, "$1").replaceAll(/([,\(\:])\s+/g, "$1").split(" ").filter(e => e);
                this.cmdBuffer = [];
                for (const c of queue) {
                    this.cmdBuffer.push(c);
                    this.execCmdBuffer();
                }
            } else {
                if (cmdBuffer.length === 1) {
                    try {
                        if (this.gui.getDeduction(cmdBuffer[0])) {
                            cmdBuffer.unshift("d");
                            this.execCmdBuffer();
                            return;
                        }
                    } catch (e) {
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
                hintText.innerText = TR(`无效命令`);
            }

        } catch (e) {
            this.clearCmdBuffer();
            hintText.innerText = TR(`意外的错误：`) + e;
        }
    }
    execExpand() {
        const hintText = this.gui.hintText;
        // ["expand", "(d|p).", {props}, "p.", {props}, "p.", {props},....]
        if (this.cmdBuffer.length < 2) {
            hintText.innerText = TR(`请输入或点击要展开的推理规则或定理\n按Esc取消`);
            this.escClear = true;
            return;
        }
        if (this.cmdBuffer.length % 2 == 0) {
            const item = this.cmdBuffer[this.cmdBuffer.length - 1];
            if (this.gui.getDeduction(item)) {
                if (!this.escClear) {
                    this.cmdBuffer.pop();
                    this.execCmdBuffer();
                    hintText.innerText += TR(`\n要展开推理规则，请先按Esc返回`);
                    return;
                }
                this.cmdBuffer.push(this.gui.formalSystem.propositions);
                const fs = this.gui.formalSystem;
                const fmr = fs.fastmetarules;
                const fsd = Object.assign({}, fs.deductions);
                const prop = fs.propositions.slice(0);
                try {
                    fs.fastmetarules = "cvuqe><:#zZQRR";
                    fs.expandMacroWithDefaultValue(item);
                    fs.fastmetarules = fmr;
                    fs.deductions = fsd;
                    this.execCmdBuffer();
                } catch (e) {
                    fs.fastmetarules = fmr;
                    fs.deductions = fsd;
                    fs.propositions = prop;
                    this.cmdBuffer.pop();
                    this.cmdBuffer.pop();
                    this.execCmdBuffer();
                    hintText.innerText += "\n" + e;
                }
            } else if (item.startsWith("p")) {
                const p = item.slice(1);
                this.cmdBuffer.push(this.gui.formalSystem.propositions);
                const fs = this.gui.formalSystem;
                const fmr = fs.fastmetarules;
                const fsd = Object.assign({}, fs.deductions);
                const prop = fs.propositions.slice(0);
                try {
                    fs.fastmetarules = "cvuqe><:#zZQR";
                    fs.expandMacroWithProp(Number(p));
                    fs.fastmetarules = fmr;
                    fs.deductions = fsd;
                    this.execCmdBuffer();
                } catch (e) {
                    fs.fastmetarules = fmr;
                    fs.deductions = fsd;
                    fs.propositions = prop;
                    this.cmdBuffer.pop();
                    this.cmdBuffer.pop();
                    this.execCmdBuffer();
                    hintText.innerText += "\n" + e;
                }
            } else {
                // else if clicked metarule, pop to roll back
                this.cmdBuffer.pop();
                this.execCmdBuffer();
                hintText.innerText += TR("\n无法展开不存在的规则"); return;
            }
        } else {
            this.gui.updatePropositionList(true);
            this.escClear = false;
            hintText.innerHTML = `${TR("目前位于")}${this.cmdBuffer.map((v, idx, arr) => {
                if (idx % 2 === 0) return null;
                if (v.match(/^p[0-9]+$/)) {
                    return v + ` (${this.gui.stringifyDeductionStep(null,
                        arr[idx + 1][Number(v.slice(1))].from
                    )})`;
                }
                return `( ${v} )`;
            }).filter(v => v).join(" > ")}${TR(" 共")}${(this.cmdBuffer.length - 1) / 2}${TR("层推理宏内，按Esc返回上一层定理表，或继续输入/点击要展开的定理")}`.replaceAll("<", "&lt;").replaceAll(">", "&gt;");
        }


    }
    execInline() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        const formalSystem = this.gui.formalSystem;
        const curLength = cmdBuffer.length;
        if (curLength === 1) {
            hintText.innerText = TR("请输入或点选使用推理宏得到的定理");
            return;
        }
        if (cmdBuffer[1].startsWith("p")) cmdBuffer[1] = cmdBuffer[1].slice(1);
        try {
            let inlineRule = false;
            if (!formalSystem.propositions[cmdBuffer[1]]) {
                const d = this.gui.getDeduction(cmdBuffer[1]);
                if (!d) {
                    throw TR("该定理或规则不存在。");
                }
                if (!d.from) {
                    throw TR("无法展开原子推理规则");
                }
                if (formalSystem.propositions.length) {
                    throw TR("要展开规则，请确保定理列表为空。");
                }
                inlineRule = true;
            }
            const fmr = formalSystem.fastmetarules;
            const fsd = Object.assign({}, formalSystem.deductions);
            formalSystem.fastmetarules = "cvuqe><:#zZQR";
            if (inlineRule) {
                formalSystem.expandMacroWithDefaultValue(cmdBuffer[1]);
            } else {
                formalSystem.inlineMacroInProp(Number(cmdBuffer[1]));
            }
            formalSystem.fastmetarules = fmr;
            formalSystem.deductions = fsd;
            this.gui.updatePropositionList(true);
            this.clearCmdBuffer();
        } catch (e) {
            this.clearCmdBuffer();
            hintText.innerText = TR("展开定理出错：") + e;
        }
    }
    execMetaDeduct() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        const formalSystem = this.gui.formalSystem;
        const curLength = cmdBuffer.length;
        if (curLength === 1) {
            hintText.innerText = TR("请输入或点选元规则，按Esc取消");
            return;
        }
        if (!this.gui.metarules.includes(cmdBuffer[1])) {
            this.clearCmdBuffer();
            hintText.innerText = TR("该元规则不存在，元推理取消");
            return;
        }
        const mr = this.gui.formalSystem.metaRules[cmdBuffer[1]];

        // a metarule is chosen, we verify vars and conditions

        const replVarsLength = mr.replaceNames.length;
        const condLength = mr.conditionDeductionIdxs.length;
        const vars = mr.replaceNames;
        const writtenConditions = new Array<string>(condLength); // conditions already inputted by user, used for hint
        let j = 0;
        for (let i = 2; i < 2 + condLength && i < curLength; i++, j++) {
            const idx = cmdBuffer[i];
            if (!formalSystem.generateDeduction(idx)) {
                this.clearCmdBuffer();
                hintText.innerText = TR("元推理已取消：条件推理规则不存在");
                return;
            }
            writtenConditions[j] = idx;
        }
        writtenConditions.fill("?", j);
        let preInfo = `${TR("正在进行元推理")} ${cmdBuffer[1]} ${writtenConditions.join(", ")} : \n`;
        for (let i = 2 + condLength; i < 2 + condLength + replVarsLength && i < curLength; i++) {
            preInfo += TR(vars[i - 2 - condLength]) + `: ${cmdBuffer[i]}\n`;
        }
        if (curLength < condLength + 2) {
            //wait for conditionIdx input
            hintText.innerText = preInfo + TR("请输入条件") + this.astparser.stringify(mr.conditions[mr.conditionDeductionIdxs[cmdBuffer.length - 2]]) + TR("的推理规则名或点推理规则");
            return;
        }
        if (curLength < replVarsLength + condLength + 2) {
            // wait for replvar input
            hintText.innerText = preInfo + TR("请输入替代") + TR(vars[cmdBuffer.length - 2 - condLength]) + TR("的内容");
            if (!this.gui.actionInput.value) {
                this.gui.actionInput.value = TR(vars[cmdBuffer.length - 2 - condLength]);
                // this.gui.actionInput.setSelectionRange(0, this.gui.actionInput.value.length);
                this.gui.actionInput.selectionStart = this._selStart = 0;
                this.gui.actionInput.selectionEnd = this._selEnd = this.gui.actionInput.value.length;
            }
            return;
        }
        // all params are there, finish it
        try {
            let newName: string;
            let afterName: string = null;
            switch (cmdBuffer[1]) {
                case "q":
                    newName = formalSystem.metaQuantifyAxiomSchema(cmdBuffer[2], "元规则生成*");
                    afterName = cmdBuffer[2];
                    break;
                case "c":
                    newName = formalSystem.metaNewConstant([cmdBuffer[2], cmdBuffer[3], cmdBuffer[4]].map(
                        v => this.astparser.parse(v)
                    ), "元规则生成*");
                    this.gui.updatePropositionList(true);
                    break;
                case "f":
                    {
                        let params = (cmdBuffer[3] as string).split(",").map(v => this.astparser.parse(v));
                        let others = [cmdBuffer[2], cmdBuffer[4], cmdBuffer[5]].map(
                            v => this.astparser.parse(v)
                        );
                        newName = formalSystem.metaNewFunction([...others, params] as [AST, AST, AST, AST[]], "元规则生成*");
                        this.gui.updatePropositionList(true);
                    }
                    break;
                case "prd":
                    {
                        let params = (cmdBuffer[3] as string).split(",").map(v => this.astparser.parse(v));
                        let others = [cmdBuffer[2], cmdBuffer[4]].map(
                            v => this.astparser.parse(v)
                        );
                        newName = formalSystem.metaNewVerb([...others, params] as [AST, AST, AST[]], "元规则生成*");
                        this.gui.updatePropositionList(true);
                    }
                    break;
                case "cdt":
                    newName = formalSystem.metaConditionTheorem(cmdBuffer[2], "元规则生成*");
                    afterName = cmdBuffer[2];
                    break;
                case "dt":
                    newName = formalSystem.metaDeductTheorem(cmdBuffer[2], "元规则生成*");
                    afterName = cmdBuffer[2];
                    break;
                case "et":
                    newName = formalSystem.metaExistTheorem(cmdBuffer[2], "元规则生成*");
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
                    if (!this.getInputNewDeductionPos(5)) return;
                    newName = formalSystem.metaIffTheorem(cmdBuffer[2], [cmdBuffer[3], cmdBuffer[4]].map(
                        v => this.astparser.parse(v)
                    ), cmdBuffer[7], "元规则生成*", this.gui.enableMIFFT_RP);
                    afterName = cmdBuffer[5];
                    break;
                case "cpt":
                    // ["m","cpt",ss0,  pos, null, name]
                    if (!this.getInputNewDeductionPos(3)) return;
                    newName = formalSystem.metaCompleteTheorem(this.astparser.parse(cmdBuffer[2]), cmdBuffer[5], "元规则生成*");
                    afterName = cmdBuffer[3];
                    break;
                case "cmt":
                    if (!this.getInputNewDeductionPos(4)) return;
                    // ["m","cpt",cond0,cond1,  pos, null, name]
                    newName = formalSystem.metaCombineTheorem(cmdBuffer[2], cmdBuffer[3], "元规则生成*");
                    afterName = cmdBuffer[4];
                    break;
                default:
                    throw TR("很抱歉，该规则暂未被作者实现");
            }
            // if (!formalSystem.deductions[newName].from.endsWith("*")) formalSystem.deductions[newName].from += "*";
            this.gui.addToDeductions(newName, afterName);
            this.clearCmdBuffer();
        } catch (e) {
            this.clearCmdBuffer();
            hintText.innerText = preInfo + TR("错误：") + e;
        }
    }
    execDeduct() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        const formalSystem = this.gui.formalSystem;
        if (this.pListMasked) { this.gui.clearPListMasked(); this.pListMasked = false; }
        if (cmdBuffer.length === 1) {
            hintText.innerText = TR("请输入或点选推理规则，按Esc取消");
            this.escClear = true;
            return;
        }
        // a deduction is chosen, we verify vars and conditions
        let deduction: Deduction;
        if (cmdBuffer[1].startsWith("d ")) cmdBuffer[1] = cmdBuffer[1].slice(2);
        try {
            deduction = cmdBuffer[1] === "." ? this.gui.getDeduction(this.lastDeduction) : this.gui.getDeduction(cmdBuffer[1]);
        } catch (e) { }
        if (!deduction) {
            this.escClear = true;
            this.clearCmdBuffer();
            hintText.innerText = TR(`推理已取消：\n未找到推理规则`) + ` ${cmdBuffer[1]}`;
            return;
        }
        const vars = deduction.replaceNames;
        const conditions = deduction.conditions;

        // cmdBuffer : [
        //    "d", d_idx: string, ...conditionIdxs: number[]
        //    ...replVars:ast[], ["## error"]?
        // ]
        const replVarsLength = vars.length;
        const condLength = conditions.length;
        const curLength = cmdBuffer.length;
        const writtenConditions = new Array<string>(condLength); // conditions already inputted by user, used for hint
        let j = 0;
        for (let i = 2; i < 2 + condLength && i < curLength; i++, j++) {
            let idx = Number(cmdBuffer[i]);
            idx = idx < 0 ? formalSystem.propositions.length + idx : idx;
            if (!formalSystem.propositions[idx]) {
                cmdBuffer.push("## error");
                hintText.innerText = TR("推理已取消：条件定理不存在");
                return;
            }
            cmdBuffer[i] = idx;
            writtenConditions[j] = cmdBuffer[i];
        }
        writtenConditions.fill("?", j);
        this.gui.hintText.innerHTML = "";
        this.gui.addSpan(this.gui.hintText, TR(`正在进行推理`) + "&nbsp; ", true);
        this.gui.hintText.appendChild(this.gui.tree2HTML(
            formalSystem.getDeductionTokens(cmdBuffer[1] === "." ? this.lastDeduction : cmdBuffer[1])
        ));
        this.gui.addSpan(this.gui.hintText, `&nbsp; ${writtenConditions.map(e => e !== "?" ? `<span class="rule-cond">${e}</span>` : e).join(", ")} : `, true);
        this.gui.hintText.appendChild(this.gui.ast2HTML("d", deduction.value, false));
        let infoWrap = document.createElement("span");
        this.gui.hintText.appendChild(document.createElement("br"));
        for (let i = 2 + condLength; i < 2 + condLength + replVarsLength && i < curLength; i++) {
            let astHtml: HTMLSpanElement, err = "";
            let varName = vars[i - 2 - condLength];
            try {
                astHtml = this.gui.ast2HTML("d", this.astparser.parse(cmdBuffer[i]), deduction.replaceTypes[varName]);
            } catch (e) {
                err = "<span class='error-color'>[!]</span>";
            }
            const varnode = this.gui.addSpan(this.gui.hintText, varName);
            varnode.className = "replvar";
            if (deduction.replaceTypes[varName] && this.gui.italicItem)
                varnode.classList.add("item");
            this.gui.addSpan(this.gui.hintText, " : " + err, true);
            if (astHtml) {
                this.gui.hintText.appendChild(astHtml);
            } else {
                this.gui.addSpan(this.gui.hintText, cmdBuffer[i]);
            }
            this.gui.hintText.appendChild(document.createElement("br"));

        }
        this.gui.hintText.appendChild(infoWrap);
        if (curLength < condLength + 2) {
            if (curLength > 1) this.escClear = false;
            //wait for conditionIdx input
            const waitCond = deduction.conditions[cmdBuffer.length - 2];
            infoWrap.innerHTML = TR("请输入条件") + this.astparser.stringify(waitCond) + TR("的定理编号，或点选定理");
            for (let i = 0; i < this.gui.formalSystem.propositions.length; i++) {
                try {
                    this.gui.formalSystem.deduct({
                        deductionIdx: cmdBuffer[1] === "." ? this.lastDeduction : cmdBuffer[1],
                        replaceValues: vars.map(e => ({ type: "replvar", name: e })),
                        conditionIdxs: [...cmdBuffer.slice(2).map(n => Number(n)), i]
                    }, undefined, true);
                } catch (e) {
                    for (let si = 0; si < 8; si++) {
                        const el = document.querySelector(`#prop-list div:nth-child(${(i + 1) * 8 - 7 + si})`);
                        if (el) el.classList.add("p-match-failed");
                        this.pListMasked = true;
                    }
                }
            }

        } else if (curLength < replVarsLength + condLength + 2) {
            if (curLength > 1) this.escClear = false;
            // wait for replvar input
            infoWrap.innerHTML = TR("请输入替代") + vars[cmdBuffer.length - 2 - condLength] + TR("的内容");
            if (!this.gui.actionInput.value) {
                this.gui.actionInput.value = vars[cmdBuffer.length - 2 - condLength];
                // this.gui.actionInput.setSelectionRange(0, this.gui.actionInput.value.length);

                this.gui.actionInput.selectionStart = this._selStart = 0;
                this.gui.actionInput.selectionEnd = this._selEnd = this.gui.actionInput.value.length;
            }
        } else {
            // all params are there, finish it
            try {
                const replvals = cmdBuffer.slice(2 + condLength) as string[];
                const sharpsharpIdx = replvals.findIndex(r => r.includes("##")) + 1;
                if (sharpsharpIdx) {
                    throw vars[sharpsharpIdx - 1] + TR(" 中包含了系统保留的符号“##”");
                }
                formalSystem.deduct({
                    deductionIdx: cmdBuffer[1] === "." ? this.lastDeduction : cmdBuffer[1],
                    replaceValues: replvals.map(
                        (it: string) => this.astparser.parse(it)
                    ),
                    conditionIdxs: cmdBuffer.slice(2, 2 + condLength).map(n => Number(n))
                });
                this.escClear = true;
                this.clearCmdBuffer();
                this.gui.updatePropositionList();
                if (cmdBuffer[1] !== ".") this.lastDeduction = cmdBuffer[1];
            } catch (e) {
                cmdBuffer.push("## error");
                hintText.innerText = TR("推理已取消\n") + e;
            }
            return;
        }
    }
    execMacro() {
        const formalSystem = this.gui.formalSystem;
        if (!this.getInputNewDeductionPos(1)) return; // ["m"].length == 1
        try {
            // ["m", pos, null, name]
            formalSystem.addMacro(this.cmdBuffer[3], "录制*");
            this.gui.addToDeductions(this.cmdBuffer[3], this.cmdBuffer[1]);
            this.execClear();
        } catch (e) {
            this.clearCmdBuffer();
            this.gui.hintText.innerText = e;
        }
    }
    execMetaMacro() {
        this.gui.hintText.innerText = TR(["", "请输入新的元宏名称", "请输入参数，多个参数用','分隔", "请输入生成的推理规则"][this.cmdBuffer.length]);
        if (this.cmdBuffer.length === 1) return;
        if (this.cmdBuffer.length === 2) {
            if (!this.cmdBuffer[1].match(/^[a-zA-Z0-9_]*$/)) {
                this.cmdBuffer.pop();
                this.gui.hintText.innerText = TR("元宏名称只能包含字母、数字和下划线，请重新输入");
                return;
            }
            return;
        }
        if (this.cmdBuffer.length === 3) return;
        const tree = this.gui.formalSystem.getDeductionTokens(this.cmdBuffer[3]);
        this.gui.formalSystem.addMetaMacro(this.cmdBuffer[1], this.cmdBuffer[2].split(",").map(v => v.trim()).filter(v => v), tree, "元宏录制*");
        this.gui.metarules.push(this.cmdBuffer[1]);
        this.gui.updateMetaRuleList(true);
        this.clearCmdBuffer();
        this.gui.hintText.innerText = TR("元宏录制成功");
    }
    addWrongDeduction(n: string) {
        const s = {
            "apn5x": "⊢#rp($0,$1,0)>(Vx:(x@N>(#rp($0,$1,x)>#rp($0,$1,S(x))))>Vx:(x@N>#rp($0,$1,x)))",
            "asepx": "⊢VxEyVz(z@y<>(z@x&$0))",
        }[n];
        if (!s) throw null;
        if (this.gui.formalSystem.deductions[n]) return;
        const ast = this.astparser.parse(s);
        this.gui.formalSystem.addDeduction(n, ast, "错误的公理");
        if (!this.gui.deductions.includes("n")) {
            this.gui.deductions.push(n);
            this.gui.updateDeductionList();
        }
    }
    execPop() {
        this.gui.formalSystem.removePropositions(1);
        this.gui.updatePropositionList(true);
        this.clearCmdBuffer();
    }
    execDel() {
        if (this.cmdBuffer.length === 1) {
            this.gui.hintText.innerText = TR("请输入要删除的推理规则名称");
            return;
        }
        try {
            const pos = this.gui.deductions.indexOf(this.cmdBuffer[1]);
            if (pos === -1) throw TR("列表中无此规则");
            if (false === this.gui.formalSystem.removeDeduction(this.cmdBuffer[1])) {
                this.gui.deductions[pos] = "< wait to remove >";
            }
            this.gui.deductions = this.gui.deductions.filter(d => this.gui.formalSystem.deductions[d]);
            this.gui.updateDeductionList();
            this.gui.updatePropositionList(true);
            this.clearCmdBuffer();
        } catch (e) {
            this.clearCmdBuffer();
            this.gui.hintText.innerText = TR("删除推理规则失败：") + e;
        }
    }
    execNewFolder() {
        if (this.cmdBuffer.length === 1) {
            this.gui.hintText.innerText = TR("请输入新文件夹名称");
            return;
        }
        const name = this.cmdBuffer[1];
        if (name.includes("::")) {
            this.cmdBuffer.pop();
            this.gui.hintText.innerText = TR("非法文件夹名称");
            return;
        }
        // < f > name, count, uuid, open/close
        this.gui.deductions.push(`< f >${name}::0::${(Math.floor(Math.random() * 2176782336)).toString(36)}::-`);
        this.gui.updateDeductionList();
        this.clearCmdBuffer();
    }
    // execMetaInln() {
    //     // metaInln c/v/e val
    //     const v = this.astparser.parse(this.cmdBuffer[2]);
    //     const token = this.cmdBuffer[1];
    //     const _ = { type: "replvar", name: " " };
    //     const ast: AST = token === "c" ? { type: "sym", name: ">", nodes: [v, _] } :
    //         token === "v" ? { type: "sym", name: "V", nodes: [v, _] } : { type: "sym", name: "E", nodes: [v, _] };
    //     this.gui.formalSystem.propositions.push({
    //         value: ast,
    //         from: {
    //             deductionIdx: "[ " + token + " ]",
    //             conditionIdxs: [], replaceValues: [v]
    //         }
    //     });
    // }
    execOpFolder() {
        if (this.cmdBuffer[1] === "rename") {
            if (this.cmdBuffer.length === 3) {
                this.gui.hintText.innerText = TR("请输入新文件夹名称");
                return;
            }
            if (this.cmdBuffer.length === 4) {
                const name = this.cmdBuffer[3];
                if (name.includes("::")) {
                    this.cmdBuffer.pop();
                    this.gui.hintText.innerText = TR("非法文件夹名称");
                    return;
                }
                const idx = this.gui.deductions.findIndex(e => e.startsWith("< f >") && e.split("::")[2] === this.cmdBuffer[2]);
                if (idx === -1) { this.gui.hintText.innerText = TR("找不到指定文件夹"); return; }
                const items = this.gui.deductions[idx].split("::");
                items[0] = "< f >" + name;
                this.gui.deductions[idx] = items.join("::");
                this.gui.updateDeductionList();
                this.clearCmdBuffer();
            }
        }
    }
    execRename() {
        if (this.cmdBuffer.length === 1) {
            this.gui.hintText.innerText = TR("请输入要重命名的规则名称");
            return;
        }
        if (this.cmdBuffer.length === 2) {
            this.gui.hintText.innerText = TR("请输入新名称");
            return;
        }
        if (this.cmdBuffer[1] === this.cmdBuffer[2]) { this.clearCmdBuffer(); return; }
        const badName = this.testBadNewName(this.cmdBuffer[2]);
        if (badName) {
            this.cmdBuffer.pop();
            this.gui.hintText.innerText = badName; return;
        }
        try {
            const pos = this.gui.deductions.indexOf(this.cmdBuffer[1]);
            this.gui.formalSystem.renameDeduction(this.cmdBuffer[1], this.cmdBuffer[2]);
            if (pos !== -1) {
                this.gui.deductions[pos] = this.cmdBuffer[2];
            }
            this.gui.updateDeductionList();
            this.gui.updatePropositionList(true);
            this.clearCmdBuffer();
        } catch (e) {
            this.clearCmdBuffer();
            this.gui.hintText.innerText = TR("重命名推理规则失败：") + e;
            return;
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
        let hypCount = formalSystem.propositions.findIndex(e => e.from);
        if (cmdBuffer.length > 1) {
            try {
                let ast = cmdBuffer.pop() as string;
                if (ast.startsWith("d ")) {
                    this.clearCmdBuffer();
                    this.cmdBuffer.push(ast);
                    this.execCmdBuffer();
                    return;
                }
                if (ast.startsWith("hyp ")) {
                    ast = ast.slice(4);
                }

                if (ast === "pop") {
                    const lastHyp = hypCount === -1 ? formalSystem.propositions.length : hypCount;
                    if (lastHyp - 1 >= 0) {
                        let removed = false;
                        try {
                            this.gui.formalSystem.moveProposition(lastHyp - 1, -1);
                        } catch (e) {
                            removed = true;
                        }
                        if (!removed) this.gui.formalSystem.removePropositions(1);
                    } else {
                        formalSystem.addHypothese(this.astparser.parse(ast));
                    }
                } else {
                    formalSystem.addHypothese(this.astparser.parse(ast));
                }
                this.gui.updatePropositionList(hypCount !== -1);
                hypCount = formalSystem.propositions.findIndex(e => e.from);
            } catch (e) {
                this.clearCmdBuffer();
                hintText.innerText = TR(`解析错误：`) + e;
                this.cmdBuffer.push("hyp");
                return;
            }
        }
        hintText.innerText = TR(`请输入假设命题p`) + (hypCount === -1 ? formalSystem.propositions.length : hypCount) + TR(`，或按“Esc”结束`);
    }
    onClickSubAst(idx: string, inserted: string) {
        if (idx === "-") return;
        const cmdBuffer = this.cmdBuffer;
        // click prop just for copy
        if (idx.startsWith("p") && !cmdBuffer.length || cmdBuffer[0] === "copy") {
            cmdBuffer.push("copy");
            this.execCmdBuffer();
            this.replaceActionInputFromClick(inserted);
            return;
        }
        if (!cmdBuffer.length || (cmdBuffer.length === 1 && (cmdBuffer[0] === "d" || cmdBuffer[0] === "meta"))) {
            // click item to start a cmd
            if (cmdBuffer[0] === "d" && cmdBuffer.length === 1) {
                if (!this.gui.formalSystem.deductions[idx]) {
                    this.gui.addSpan(this.gui.hintText, "<br>" + TR("\n请点选推理规则！"), true);
                    return;
                }
            }
            if (idx[0] !== "m" && idx[0] !== "p") {
                cmdBuffer.push("d");
                cmdBuffer.push(idx);
            } else {
                cmdBuffer.push(idx);
            }
            this.execCmdBuffer();
            return;
        }
        // deduction started, but wait for click props or replvars
        if (cmdBuffer[0] === "d" && cmdBuffer.length >= 2) {
            const deduction = this.gui.formalSystem.deductions[cmdBuffer[1] === "." ? this.lastDeduction : cmdBuffer[1]];
            const vars = deduction.replaceNames.length;
            const conditions = deduction.conditions.length;
            if (conditions + 2 > cmdBuffer.length) {
                //wait for conditionIdx input
                if (!idx.match(/^p[0-9]+$/)) {
                    this.gui.addSpan(this.gui.hintText, "<br>" + TR("\n请点选定理！"), true);

                    return;
                }
                cmdBuffer.push(Number(idx.slice(1)));
                this.execCmdBuffer();
            } else {
                // wait for replvar input
                this.replaceActionInputFromClick(inserted);
            }
        } else if (cmdBuffer[0] === "hyp") {
            // wait for hypothese input, user can click both d&p terms
            this.replaceActionInputFromClick(inserted);
        } else if (cmdBuffer[0] === "meta" && cmdBuffer.length >= 2) {
            const mr = this.gui.formalSystem.metaRules[cmdBuffer[1]];
            const conditions = mr.conditionDeductionIdxs.length;
            if (conditions + 2 > cmdBuffer.length) {
                //wait for conditionIdx input
                if (!this.gui.formalSystem.deductions[idx]) {
                    this.gui.addSpan(this.gui.hintText, "<br>" + TR("\n请点选推理规则！"), true);
                    return;
                }
                cmdBuffer.push(idx);
                this.execCmdBuffer();
            } else {
                // wait for replvar input
                this.replaceActionInputFromClick(inserted);
            }
        } else if (cmdBuffer[0] === "entr" || cmdBuffer[0] === "inln") {
            // wait for both d&p terms
            cmdBuffer.push(idx);
            this.execCmdBuffer();
        }
    }
    private _selStart = 0; private _selEnd = 0;
    replaceActionInputFromClick(inserted: string) {
        const actionInput = this.gui.actionInput;
        if (!this.gui.isMobile) actionInput.focus();
        const val = actionInput.value;
        const start = this._selStart;
        const end = this._selEnd;
        actionInput.value = val.substring(0, start) + inserted + val.substring(end);
        actionInput.selectionStart = this._selStart = start;
        actionInput.selectionEnd = this._selEnd = start + inserted.length;

        // alert(start + "|" + end + " => " + actionInput.selectionStart + "|" + actionInput.selectionEnd)
    }
    getInputNewDeductionPos(prevLength: number): boolean {
        const cmdLen = this.cmdBuffer.length - prevLength + 1;
        // ["m", pos, null, name]
        if (cmdLen === 1 || cmdLen === 3) {
            // ["m"] || ["m", pos, null]
            let i = 0;
            while (this.gui.formalSystem.deductions["s" + (++i)]);
            this.gui.actionInput.value = "s" + i;
            this.gui.actionInput.selectionStart = 1;
            this.gui.actionInput.selectionEnd = this.gui.actionInput.value.length;
            this.gui.hintText.innerText = cmdLen === 1 ? TR("请输入在哪个规则后方插入新规则。若直接输入新规则名称，则默认插入至规则表最后") : TR("请输入新规则名称");
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
            } else {
                // ["m", name]
                this.cmdBuffer.splice(prevLength, 0, null, null);
                // ["m", pos=null, null, name]
                return this.getInputNewDeductionPos(prevLength);
            }
        }
        // ["m", pos, null, name]
        const n = this.cmdBuffer[prevLength + 2];
        const badInfo = this.testBadNewName(n);
        if (badInfo) {
            this.cmdBuffer.pop();
            const res = this.getInputNewDeductionPos(prevLength);
            this.gui.hintText.innerText = badInfo;
            return res;
        }
        return true;
    }
    testBadNewName(name: string): string {
        if (name.match(/^[0-9<>acdempuv#\.]/)) {
            return TR("以.<>acdempuv#或数字开头的推理规则名称由系统保留，请重新命名");
        }
        if (name.match(/^\$\$/)) {
            return TR("以$$开头的推理规则名称由系统保留，请重新命名");
        }
        if (name.includes(",") || name.includes(":") || name.includes(" ")) {
            return TR("推理规则名称中禁止出现空格或由系统保留的“:”或“,”符号，请重新命名");
        }
        if (this.gui.formalSystem.deductions[name]) {
            return TR(`推理规则名称`) + name + TR(`已存在或被系统保留，请重新命名`);
        }
        return null;
    }
    onEsc() {
        if (this.cmdBuffer[0] === "entr") {
            // ["expand", "(d|p).", {props}, "p.", {props}, "p.", {props},....]
            this.gui.formalSystem.propositions = this.cmdBuffer.pop();
            this.cmdBuffer.pop();
            this.execCmdBuffer();
            if (this.escClear) {
                this.gui.updatePropositionList(true);
            }
        } else if (this.cmdBuffer[0] === "d") {
            if (this.pListMasked) { this.gui.clearPListMasked(); this.pListMasked = false; }
            if (this.cmdBuffer[this.cmdBuffer.length - 1] === "## error") this.cmdBuffer.pop();
            this.gui.actionInput.value = this.cmdBuffer.pop();
            if (this.cmdBuffer.length === 2) this.escClear = false;
            this.execCmdBuffer();
        } else throw "cannot reached";
    }
}