import { TR } from "../lang.js";
import { ASTParser } from "./astparser.js";
import { SavesParser } from "./savesparser.js";
export class FSCmd {
    cmdBuffer = [];
    astparser = new ASTParser;
    escClear = true;
    autoCompleteIdx = -1;
    gui;
    lastDeduction = null;
    savesParser = new SavesParser;
    // onsave: () => string;
    // onload: (s: string) => void;
    // onreset: () => void;
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
        actionInput.addEventListener("input", () => {
            this.actionInputChange();
        });
        document.addEventListener("click", e => {
            if (!e.target.closest("#action-input")) {
                document.getElementById("autocomplete-list").style.display = "none";
            }
        });
    }
    actionInputKeydown(e) {
        const actionInput = this.gui.actionInput;
        // autoComplete:
        let currentIndex = this.autoCompleteIdx;
        const list = document.getElementById("autocomplete-list");
        if (e.key === "Escape") {
            this.showhints([]);
            this.clearCmdBuffer();
            return false;
        }
        const items = list.querySelectorAll("li");
        if (list.style.display !== "none" && items.length) {
            if (e.key === "ArrowDown") {
                currentIndex = (currentIndex + 1) % items.length;
            }
            else if (e.key === "ArrowUp") {
                currentIndex = (currentIndex - 1 + items.length) % items.length;
            }
            else if (e.key === "Enter" || e.key === "Tab") {
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
        if (e.key !== "Enter")
            return false;
        if (this.cmdBuffer[this.cmdBuffer.length - 1] === "## error") {
            this.escClear = true;
            this.clearCmdBuffer();
            return false;
        }
        this.showhints([]);
        let cmd = actionInput.value;
        if (cmd.includes("`"))
            cmd = cmd.replaceAll("`", "");
        if (!cmd.trim())
            return;
        this.cmdBuffer.push(cmd);
        actionInput.value = "";
        this.execCmdBuffer();
    }
    // hint: [displayHTML, insertText]
    showhints(hints) {
        const list = document.getElementById("autocomplete-list");
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
            li.innerHTML = html;
            li.setAttribute("data-value", cmd);
            li.onclick = () => {
                input.value = cmd;
                list.style.display = "none";
                input.focus();
                if (html.includes("<span class='cmd'>[D]")) {
                    this.actionInputKeydown({ key: "Enter" });
                }
            };
            list.appendChild(li);
        });
    }
    actionInputChange() {
        const value = this.gui.actionInput.value;
        let list = [];
        if (this.cmdBuffer.length === 0 || (this.cmdBuffer.length === 1 && this.cmdBuffer[0] === "d") || (this.cmdBuffer.length === 2 && (this.cmdBuffer[0] === "meta" && this.cmdBuffer[1] === "ifft"))) {
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
                        if (d.conditions.length)
                            return false;
                        if (d.conclusion.name !== "<>")
                            return false;
                        if (d.conclusion.type !== "sym")
                            return false;
                    }
                    return e.toLowerCase().startsWith(subValue.toLowerCase());
                }).map(e => {
                    let d;
                    try {
                        d = this.gui.formalSystem.generateDeduction(pre + e);
                    }
                    catch (e) {
                        return [];
                    }
                    return ["<span class='cmd'>[D] " + `<span style="color: red">${pre.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")}</span>` + e.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;") + "</span> <span class='hint'> " + (d ?
                            this.astparser.stringifyTight(d.value).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;") : "") + "</span>", "d " + pre + e];
                }).filter(e => e.length);
            }
            // cmd, only for empty cmdbuffer
            if (value && this.cmdBuffer.length === 0) {
                const unlockedCmd = ["pop", "clear"];
                if (!document.getElementById("hyp-btn").classList.contains("hide"))
                    unlockedCmd.push("hyp");
                if (!document.getElementById("macro-btns").classList.contains("hide"))
                    unlockedCmd.push("entr", "del", "inln");
                list.push(...unlockedCmd.filter(e => e.startsWith(value)).map(e => ["<span class='cmd'>[C] " + e + "</span> <span class='hint'> " + TR("命令：") + e + "</span>", e]));
            }
        }
        this.showhints(list);
    }
    clearCmdBuffer() {
        if (this.escClear) {
            this.cmdBuffer = [];
            this.gui.actionInput.value = "";
            this.gui.hintText.innerText = TR("请输入命令");
            if (!this.gui.isMobile)
                this.gui.actionInput.focus();
            this.gui.cmdBtns.forEach(e => {
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
        this.gui.cmdBtns.forEach(e => {
            e.disabled = true;
        });
        try {
            switch (cmdBuffer[0]) {
                case "copy": {
                    if (cmdBuffer.length === 2) { // copy cmd
                        const reg = new RegExp(TR("命令：") + "(.+)$");
                        const res = hintText.innerText.match(reg);
                        if (res) {
                            hintText.innerText = TR("可复制生成定理的命令，按Esc取消");
                            this.gui.actionInput.value = res[1];
                            return;
                        }
                    }
                    hintText.innerText = TR("可复制定理内容，按Esc取消");
                    return;
                }
                case "d": return this.execDeduct();
                // case "help": return this.execHelp();
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
                hintText.innerText = TR(`无效命令`);
            }
        }
        catch (e) {
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
            if (this.gui.formalSystem.deductions[item]) {
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
                    fs.fastmetarules = "cvuqe><:#";
                    fs.expandMacroWithDefaultValue(item);
                    fs.fastmetarules = fmr;
                    fs.deductions = fsd;
                    this.execCmdBuffer();
                }
                catch (e) {
                    fs.fastmetarules = fmr;
                    fs.deductions = fsd;
                    fs.propositions = prop;
                    this.cmdBuffer.pop();
                    this.cmdBuffer.pop();
                    this.execCmdBuffer();
                    hintText.innerText += "\n" + e;
                }
            }
            else if (item.startsWith("p")) {
                const p = item.slice(1);
                this.cmdBuffer.push(this.gui.formalSystem.propositions);
                const fs = this.gui.formalSystem;
                const fmr = fs.fastmetarules;
                const fsd = Object.assign({}, fs.deductions);
                const prop = fs.propositions.slice(0);
                try {
                    fs.fastmetarules = "cvuqe><:#";
                    fs.expandMacroWithProp(Number(p));
                    fs.fastmetarules = fmr;
                    fs.deductions = fsd;
                    this.execCmdBuffer();
                }
                catch (e) {
                    fs.fastmetarules = fmr;
                    fs.deductions = fsd;
                    fs.propositions = prop;
                    this.cmdBuffer.pop();
                    this.cmdBuffer.pop();
                    this.execCmdBuffer();
                    hintText.innerText += "\n" + e + "\n";
                    const p_ = fs.propositions[Number(p)];
                    const from = p_.from;
                    hintText.innerText += TR("命令：") + (from ?
                        ["d", from.deductionIdx, ...from.conditionIdxs,
                            ...from.replaceValues.map(v => this.astparser.stringifyTight(v))
                        ].join(" ")
                        : ("hyp " + this.astparser.stringifyTight(p_.value)));
                }
            }
            else {
                // else if clicked metarule, pop to roll back
                this.cmdBuffer.pop();
                this.execCmdBuffer();
                hintText.innerText += TR("\n无法展开元规则");
                return;
            }
        }
        else {
            this.gui.updatePropositionList(true);
            this.escClear = false;
            const pData = this.cmdBuffer[this.cmdBuffer.length - 2];
            let pcmd = "";
            if (pData && pData.match(/^p[0-9]+$/)) {
                const p = this.cmdBuffer[this.cmdBuffer.length - 1][Number(pData.slice(1))];
                const from = p.from;
                pcmd = TR("上层命令：") + (from ?
                    ["d", from.deductionIdx.replaceAll("<", "&lt;").replaceAll(">", "&gt;"), ...from.conditionIdxs,
                        ...from.replaceValues.map(v => this.astparser.stringifyTight(v))
                    ].join(" ")
                    : ("hyp " + this.astparser.stringifyTight(p.value).replaceAll("<", "&lt;").replaceAll(">", "&gt;"))) + "<br>";
            }
            hintText.innerHTML = pcmd + `${TR("目前位于")}${this.cmdBuffer.map((v, idx, arr) => {
                if (idx % 2 === 0)
                    return null;
                if (v.match(/^p[0-9]+$/)) {
                    return v + ` (${this.gui.stringifyDeductionStep(arr[idx + 1][Number(v.slice(1))].from)})`;
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
        if (cmdBuffer[1].startsWith("p"))
            cmdBuffer[1] = cmdBuffer[1].slice(1);
        try {
            if (!formalSystem.propositions[cmdBuffer[1]])
                throw TR("该定理不存在");
            const fmr = formalSystem.fastmetarules;
            const fsd = Object.assign({}, formalSystem.deductions);
            formalSystem.fastmetarules = "cvuqe><:#";
            formalSystem.inlineMacroInProp(Number(cmdBuffer[1]));
            formalSystem.fastmetarules = fmr;
            formalSystem.deductions = fsd;
            this.gui.updatePropositionList(true);
            this.clearCmdBuffer();
        }
        catch (e) {
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
        const writtenConditions = new Array(condLength); // conditions already inputted by user, used for hint
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
                    if (!this.getInputNewDeductionPos(5))
                        return;
                    newName = formalSystem.metaIffTheorem(cmdBuffer[2], [cmdBuffer[3], cmdBuffer[4]].map(v => this.astparser.parse(v)), cmdBuffer[7], "元规则生成*", this.gui.enableMIFFT_RP);
                    afterName = cmdBuffer[5];
                    break;
                case "cpt":
                    // ["m","cpt",ss0,  pos, null, name]
                    if (!this.getInputNewDeductionPos(3))
                        return;
                    newName = formalSystem.metaCompleteTheorem(this.astparser.parse(cmdBuffer[2]), cmdBuffer[5], "元规则生成*");
                    afterName = cmdBuffer[3];
                    break;
                case "cmt":
                    if (!this.getInputNewDeductionPos(4))
                        return;
                    // ["m","cpt",cond0,cond1,  pos, null, name]
                    newName = formalSystem.metaCombineTheorem(cmdBuffer[2], cmdBuffer[3], "元规则生成*");
                    afterName = cmdBuffer[4];
                    break;
                case "nt":
                    if (!this.getInputNewDeductionPos(4))
                        return;
                    // ["m","cpt",oldvars+body,  newvars,pos, null, name]
                    newName = formalSystem.metaChangeNameTheorem(this.astparser.parse(cmdBuffer[2]), cmdBuffer[3].split(/[\s,]/g).filter(e => e), cmdBuffer[6], "元规则生成*");
                    afterName = cmdBuffer[4];
                    break;
                default:
                    throw TR("很抱歉，该规则暂未被作者实现");
            }
            // if (!formalSystem.deductions[newName].from.endsWith("*")) formalSystem.deductions[newName].from += "*";
            this.gui.addToDeductions(newName, afterName);
            this.clearCmdBuffer();
        }
        catch (e) {
            this.clearCmdBuffer();
            hintText.innerText = preInfo + TR("错误：") + e;
        }
    }
    execDeduct() {
        const cmdBuffer = this.cmdBuffer;
        const hintText = this.gui.hintText;
        const formalSystem = this.gui.formalSystem;
        if (cmdBuffer.length === 1) {
            hintText.innerText = TR("请输入或点选推理规则，按Esc取消");
            this.escClear = true;
            return;
        }
        // a deduction is chosen, we verify vars and conditions
        let deduction;
        try {
            deduction = cmdBuffer[1] === "." ? this.gui.getDeduction(this.lastDeduction) : this.gui.getDeduction(cmdBuffer[1]);
        }
        catch (e) { }
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
        const writtenConditions = new Array(condLength); // conditions already inputted by user, used for hint
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
        let preInfo = TR(`正在进行推理`) + ` ${cmdBuffer[1] === "." ? this.lastDeduction : cmdBuffer[1]} ${writtenConditions.join(", ")} :  ${this.astparser.stringify(deduction.value)}\n`;
        for (let i = 2 + condLength; i < 2 + condLength + replVarsLength && i < curLength; i++) {
            preInfo += vars[i - 2 - condLength] + `: ${cmdBuffer[i]}\n`;
        }
        if (curLength < condLength + 2) {
            if (curLength > 2)
                this.escClear = false;
            //wait for conditionIdx input
            hintText.innerText = preInfo + TR("请输入条件") + this.astparser.stringify(deduction.conditions[cmdBuffer.length - 2]) + TR("的定理编号，或点选定理");
        }
        else if (curLength < replVarsLength + condLength + 2) {
            if (curLength > 2)
                this.escClear = false;
            // wait for replvar input
            hintText.innerText = preInfo + TR("请输入替代") + vars[cmdBuffer.length - 2 - condLength] + TR("的内容");
            if (!this.gui.actionInput.value) {
                this.gui.actionInput.value = vars[cmdBuffer.length - 2 - condLength];
                // this.gui.actionInput.setSelectionRange(0, this.gui.actionInput.value.length);
                this.gui.actionInput.selectionStart = this._selStart = 0;
                this.gui.actionInput.selectionEnd = this._selEnd = this.gui.actionInput.value.length;
            }
        }
        else {
            // all params are there, finish it
            try {
                const replvals = cmdBuffer.slice(2 + condLength);
                const sharpsharpIdx = replvals.findIndex(r => r.includes("##")) + 1;
                if (sharpsharpIdx) {
                    throw vars[sharpsharpIdx - 1] + TR(" 中包含了系统保留的符号“##”");
                }
                formalSystem.deduct({
                    deductionIdx: cmdBuffer[1] === "." ? this.lastDeduction : cmdBuffer[1],
                    replaceValues: replvals.map((it) => this.astparser.parse(it)),
                    conditionIdxs: cmdBuffer.slice(2, 2 + condLength).map(n => Number(n))
                });
                this.escClear = true;
                this.clearCmdBuffer();
                this.gui.updatePropositionList();
                if (cmdBuffer[1] !== ".")
                    this.lastDeduction = cmdBuffer[1];
            }
            catch (e) {
                cmdBuffer.push("## error");
                hintText.innerText = TR("推理已取消\n") + e;
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
            this.gui.hintText.innerText = TR("请输入要删除的推理规则名称");
            return;
        }
        try {
            const pos = this.gui.deductions.indexOf(this.cmdBuffer[1]);
            if (pos === -1)
                throw TR("列表中无此规则");
            this.gui.formalSystem.removeDeduction(this.cmdBuffer[1]);
            this.gui.deductions.splice(pos, 1);
            this.gui.updateDeductionList();
            this.clearCmdBuffer();
        }
        catch (e) {
            this.clearCmdBuffer();
            this.gui.hintText.innerText = TR("删除推理规则失败：") + e;
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
                hintText.innerText = TR(`解析错误：`) + e;
                this.cmdBuffer.push("hyp");
                return;
            }
        }
        hintText.innerText = TR(`请输入假设命题p`) + formalSystem.propositions.length + TR(`，或按“Esc”结束`);
    }
    onClickSubAst(idx, inserted) {
        const cmdBuffer = this.cmdBuffer;
        // click prop just for copy
        if (idx.startsWith("p") && !cmdBuffer.length || cmdBuffer[0] === "copy") {
            cmdBuffer.push("copy");
            this.execCmdBuffer();
            const p = this.gui.formalSystem.propositions[Number(idx.slice(1))];
            const from = p.from;
            this.gui.hintText.innerText += "\n" + TR("命令：") + (from ?
                ["d", from.deductionIdx, ...from.conditionIdxs,
                    ...from.replaceValues.map(v => this.astparser.stringifyTight(v))
                ].join(" ")
                : ("hyp " + this.astparser.stringifyTight(p.value)));
            this.replaceActionInputFromClick(inserted);
            return;
        }
        if (!cmdBuffer.length || (cmdBuffer.length === 1 && (cmdBuffer[0] === "d" || cmdBuffer[0] === "meta"))) {
            // click item to start a cmd
            if (cmdBuffer[0] === "d" && cmdBuffer.length === 1) {
                if (!this.gui.formalSystem.deductions[idx]) {
                    this.gui.hintText.innerText += TR("\n请点选推理规则！");
                    return;
                }
            }
            if (idx[0] !== "m" && idx[0] !== "p") {
                cmdBuffer.push("d");
                cmdBuffer.push(idx);
            }
            else {
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
                    this.gui.hintText.innerText += TR("\n请点选定理！");
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
                    this.gui.hintText.innerText += TR("\n请点选推理规则！");
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
        if (n.match(/^[<>acdempuv\.]/)) {
            this.cmdBuffer.pop();
            const res = this.getInputNewDeductionPos(prevLength);
            this.gui.hintText.innerText = TR("以.<>acdempuv开头的推理规则名称由系统保留，请重新命名");
            return res;
        }
        if (n.includes(",") || n.includes(":") || n.includes(" ")) {
            this.cmdBuffer.pop();
            const res = this.getInputNewDeductionPos(prevLength);
            this.gui.hintText.innerText = TR("推理规则名称中禁止出现空格或由系统保留的“:”或“,”符号，请重新命名");
            return res;
        }
        if (this.gui.formalSystem.deductions[n]) {
            this.cmdBuffer.pop();
            const res = this.getInputNewDeductionPos(prevLength);
            this.gui.hintText.innerText = TR(`推理规则名称`) + n + TR(`已存在或被系统保留，请重新命名`);
            return res;
        }
        return true;
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
        }
        else if (this.cmdBuffer[0] === "d") {
            if (this.cmdBuffer[this.cmdBuffer.length - 1] === "## error")
                this.cmdBuffer.pop();
            this.gui.actionInput.value = this.cmdBuffer.pop();
            if (this.cmdBuffer.length === 2)
                this.escClear = false;
            this.execCmdBuffer();
        }
        else
            throw "cannot reached";
    }
}
//# sourceMappingURL=cmd.js.map