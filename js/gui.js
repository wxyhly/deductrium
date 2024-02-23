import { FSCmd } from "./cmd.js";
import { initFormalSystem } from "./initial.js";
import { FormalSystem } from "./formalsystem.js";
export class FSGui {
    formalSystem = new FormalSystem();
    actionInput;
    hintText;
    propositionList;
    deductionList;
    metaRuleList;
    divCmdBtns;
    displayDs = new Set();
    deductions = [];
    isMobile = /Mobi|Android|iPhone/i.test(navigator.userAgent);
    cmd;
    constructor(propositionList, deductionList, metaRuleList, actionInput, hintText, displayPLayerSelect, divCmdBtns) {
        this.propositionList = propositionList;
        this.metaRuleList = metaRuleList;
        this.deductionList = deductionList;
        this.actionInput = actionInput;
        this.hintText = hintText;
        this.divCmdBtns = divCmdBtns;
        this.cmd = new FSCmd(this);
        const { fs, arrD } = initFormalSystem();
        this.formalSystem = fs;
        this.deductions = arrD;
        divCmdBtns.querySelectorAll("button").forEach(btn => {
            btn.addEventListener("click", () => {
                if (this.cmd.cmdBuffer.length)
                    return;
                this.cmd.cmdBuffer.push(btn.innerText.replace(/.+\((.+)\)/g, "$1"));
                this.cmd.execCmdBuffer();
            });
        });
        document.querySelectorAll("input[name='show-d']").forEach((sd) => {
            const from = sd.parentNode.innerText;
            this.displayDs.add(from);
            sd.addEventListener("change", () => {
                sd.checked ? this.displayDs.add(from) : this.displayDs.delete(from);
                this.updateDeductionList();
            });
        });
        document.querySelectorAll(".footer .right button").forEach((btn) => {
            btn.addEventListener("click", () => {
                if (btn.innerText === "OK") {
                    this.cmd.actionInputKeydown({ key: "Enter" });
                }
                else if (btn.innerText === "Esc") {
                    this.cmd.actionInputKeydown({ key: "Escape" });
                }
            });
        });
        this.updateMetaRuleList();
        this.updateDeductionList();
    }
    prettyPrint(s) {
        return s.replace(/<>/g, "↔").replace(/>/g, "→").replace(/</g, "⊂").replace(/@/g, "∈")
            .replace(/U/g, "∪").replace(/I/g, "∩").replace(/\*/g, "×").replace(/\//g, "÷").replace(/-/g, "−")
            .replace(/\|/g, "∨").replace(/&/g, "∧").replace(/~/g, "¬").replace(/V/g, "∀").replace(/E/g, "∃");
    }
    addSpan(parentSpan, text) {
        const span = document.createElement("span");
        span.innerHTML = text;
        parentSpan.appendChild(span);
        return span;
    }
    ast2HTML(idx, ast, scopes = []) {
        const varnode = document.createElement("span");
        const astStr = this.cmd.astparser.stringify(ast);
        varnode.setAttribute("ast-string", astStr);
        if (ast.type === "meta") {
            this.addSpan(varnode, "(");
            let firstTerm = true;
            for (const n of ast.nodes[0].nodes) {
                if (firstTerm) {
                    firstTerm = false;
                }
                else {
                    this.addSpan(varnode, ", ");
                }
                varnode.appendChild(this.ast2HTML(idx, n, scopes));
            }
            if (ast.name === "⊢M") {
                this.addSpan(varnode, ` ⊢<sub>M</sub> `);
            }
            else {
                this.addSpan(varnode, ` ${ast.name} `);
            }
            firstTerm = true;
            for (const n of ast.nodes[1].nodes) {
                if (firstTerm) {
                    firstTerm = false;
                }
                else {
                    this.addSpan(varnode, ", ");
                }
                varnode.appendChild(this.ast2HTML(idx, n, scopes));
            }
            this.addSpan(varnode, ")");
        }
        else if (ast.type === "fn") {
            const fnName = this.addSpan(varnode, ast.name);
            if (ast.name.startsWith("#"))
                fnName.classList.add("sysfn");
            if (this.formalSystem.fns.has(ast.name))
                fnName.classList.add("fn");
            this.addSpan(varnode, "(");
            const fonts = []; // 0 for mormal, 1 for sup, -1 for sub
            for (const [nidx, n] of ast.nodes.entries()) {
                let font = 0;
                if (ast.name.match(/^#(v*)nf/)) {
                    font = (nidx > ast.name.length - 3) ? -1 : 1;
                }
                if (ast.name.match(/^#?#crp/)) {
                    font = nidx === 2 ? -1 : 1;
                }
                if (ast.name.match(/^#?#rp/)) {
                    font = nidx === 3 ? 1 : 0;
                }
                if (!nidx)
                    font = 0;
                fonts.push(font);
                const noComma = (nidx >= 1);
                if (nidx && !font && !fonts[nidx - 1])
                    this.addSpan(varnode, ", ");
                const node = this.ast2HTML(idx, n, scopes);
                if (font) {
                    const wrappedNode = document.createElement(font === 1 ? "sup" : "sub");
                    if (nidx && font === fonts[nidx - 1])
                        wrappedNode.appendChild(this.addSpan(wrappedNode, ","));
                    wrappedNode.appendChild(node);
                    varnode.appendChild(wrappedNode);
                }
                else {
                    varnode.appendChild(node);
                }
            }
            this.addSpan(varnode, ")");
        }
        else if (ast.type === "replvar") {
            const el = this.addSpan(varnode, ast.name);
            const scopeStack = scopes.slice(0);
            if (this.formalSystem.consts.has(ast.name)) {
                el.classList.add("constant");
            }
            else if (ast.name.replace(/^\.\.\./, "").match(this.formalSystem.deductionReplNameRule)) {
                el.classList.add("replvar");
            }
            else {
                el.classList.add("freeVar");
            }
            if (scopeStack[0]?.type === "quantvar") {
                // quantvar is only aimed for mark css style
                if (!el.classList.contains("replvar")) {
                    el.classList.remove("freeVar");
                    el.classList.add("boundedVar");
                }
                scopeStack.pop();
            }
            do {
                if (scopeStack[0] && scopeStack[0]?.nodes[0]?.name === ast.name) {
                    varnode.setAttribute("ast-scope", this.cmd.astparser.stringify(scopeStack[0]));
                    if (!el.classList.contains("replvar")) {
                        el.classList.remove("freeVar");
                        el.classList.add("boundedVar");
                    }
                    break;
                }
            } while (scopeStack.shift());
        }
        else {
            switch (ast.name) {
                case "~":
                case "!":
                    this.addSpan(varnode, this.prettyPrint(ast.name));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes));
                    break;
                case "V":
                case "E":
                case "E!":
                    const outterLayers = [];
                    outterLayers.push(this.addSpan(varnode, "(" + this.prettyPrint(ast.name)));
                    const varast = this.ast2HTML(idx, ast.nodes[0], [{ type: "quantvar", name: "quantvar" }]);
                    varast.classList.add("boundedVar");
                    outterLayers.push(varnode.appendChild(varast));
                    outterLayers.push(this.addSpan(varnode, ":"));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], [ast, ...scopes]));
                    outterLayers.push(this.addSpan(varnode, ")"));
                    // hightlight constrained vars
                    const constrainedVars = Array.from(varnode.querySelectorAll("span")).filter(node => node.getAttribute("ast-scope") === astStr);
                    for (const node of constrainedVars) {
                        node.addEventListener('mouseover', ev => {
                            for (const node of outterLayers) {
                                node.classList.add("highlighted");
                            }
                        });
                        node.addEventListener('mouseout', ev => {
                            for (const node of outterLayers) {
                                node.classList.remove("highlighted");
                            }
                        });
                    }
                    outterLayers[1].addEventListener('mouseover', ev => {
                        for (const node of constrainedVars) {
                            node.classList.add("highlighted");
                        }
                    });
                    outterLayers[1].addEventListener('mouseout', ev => {
                        for (const node of constrainedVars) {
                            node.classList.remove("highlighted");
                        }
                    });
                    break;
                default:
                    // case "@": case "=": case "&": case "^": case ">": case "|":
                    this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes));
                    this.addSpan(varnode, ast.name.startsWith("$$") ? ` ${ast.name} ` : this.prettyPrint(ast.name));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes));
                    this.addSpan(varnode, ")");
            }
        }
        // clicks and hovers in this layer
        const spans = Array.from(varnode.childNodes).filter(node => !node.getAttribute("ast-string"));
        for (const node of spans) {
            node.addEventListener('mouseover', ev => {
                for (const node of spans) {
                    node.classList.add("highlighted");
                }
            });
            node.addEventListener('mouseout', ev => {
                for (const node of spans) {
                    node.classList.remove("highlighted");
                }
            });
            node.addEventListener('click', ev => {
                ev.stopPropagation();
                this.cmd.onClickSubAst(idx, astStr);
            });
        }
        return varnode;
    }
    _convert(d) {
        let str = this.cmd.astparser.stringify(d.value);
        let steps = d.steps?.map(step => [step.deductionIdx, step.replaceValues.map(v => this.cmd.astparser.stringify(v)), step.conditionIdxs]);
        return [str, JSON.stringify(steps)];
    }
    updateGuiList(prefix, logicArray, list, filter, setInfo, refresh, customIdx) {
        if (refresh) {
            while (list.lastChild) {
                list.removeChild(list.lastChild);
            }
            list.setAttribute("total", "0");
        }
        let listLength = Number(list.getAttribute("total")) || 0;
        const targetLength = logicArray.length;
        list.setAttribute("total", String(targetLength));
        for (; listLength > targetLength; listLength--) {
            const p = logicArray[listLength];
            if (!filter(p, listLength))
                continue;
            for (let i = 0; i < 8; i++)
                list.removeChild(list.lastChild);
        }
        for (; listLength < targetLength; listLength++) {
            const p = logicArray[listLength];
            const pname = customIdx ? customIdx[listLength] : prefix + listLength;
            if (!filter(p, listLength))
                continue;
            const itIdx = document.createElement("div");
            list.appendChild(itIdx);
            itIdx.classList.add("idx");
            itIdx.innerText = pname;
            const itVal = document.createElement("div");
            list.appendChild(itVal);
            itVal.classList.add("val");
            itVal.appendChild(this.ast2HTML(pname, p.value));
            const infoArr = [];
            for (let i = 0; i < 6; i++) {
                const itInfo = document.createElement("div");
                list.appendChild(itInfo);
                itInfo.className = "info";
                infoArr.push(itInfo);
            }
            setInfo(p, infoArr, itVal);
            itVal.addEventListener("click", () => {
                const inserted = this.cmd.astparser.stringify(p.value);
                this.cmd.onClickSubAst(pname, inserted);
            });
        }
        list.scroll({ top: list.scrollHeight });
    }
    updatePropositionList(refresh) {
        this.updateGuiList("p", this.formalSystem.propositions, this.propositionList, (p) => true, (p, itInfo, it) => {
            if (!p.from) {
                itInfo[0].innerText = "假设";
                return;
            }
            itInfo[0].innerHTML = this.stringifyDeductionStep(p.from).replaceAll("<", "&lt;").replaceAll(">", "&gt;");
        }, refresh);
    }
    updateDeductionList() {
        this.updateGuiList("", this.deductions.map(d => this.formalSystem.deductions[d]), this.deductionList, (p, idx) => (this.displayDs.has(p.from) || (this.displayDs.has("添加的规则") && p.from.endsWith("*"))), (p, itInfo, it) => {
            itInfo[0].innerText = p.from.replaceAll("<", "&lt;").replaceAll(">", "&gt;") + (p.steps?.length ? "[宏]" : "");
        }, true, this.deductions);
    }
    updateMetaRuleList(refresh) {
        this.updateGuiList("m", Object.values(this.formalSystem.metaRules), this.metaRuleList, (p) => true, (p, itInfo, it) => {
            itInfo[0].innerHTML = p.from.replaceAll("<", "&lt;").replaceAll(">", "&gt;");
        }, refresh, Object.keys(this.formalSystem.metaRules).map(e => "m" + e));
    }
    stringifyDeductionStep(step) {
        return `&nbsp;${step.deductionIdx} ${step.conditionIdxs.join(",")}`;
    }
    addToDeductions(name, after) {
        const oldpos = this.deductions.indexOf(name);
        // delete
        if (oldpos !== -1) {
            if (after === name)
                return; // x=S(x), aborted
            if (after === this.deductions[oldpos - 1])
                return; // identity
            this.deductions.splice(oldpos, 1);
        }
        // insert
        if (!after) {
            this.deductions.push(name);
            this.updateDeductionList();
            return;
        }
        const pos = this.deductions.indexOf(after);
        if (pos === -1) {
            this.deductions.push(name);
        }
        else {
            this.deductions.splice(pos + 1, 0, name);
        }
        this.updateDeductionList();
    }
}
//# sourceMappingURL=gui.js.map