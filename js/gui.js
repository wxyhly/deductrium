import { FSCmd } from "./cmd.js";
import { addZFC } from "./initial.js";
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
        addZFC(this.formalSystem);
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
                this.updateDeductionList(true);
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
    stringify(ast) {
        const nd = ast.nodes;
        if (ast.type === "fn") {
            return `${ast.name}(${nd.map(n => this.stringify(n)).join(", ")})`;
        }
        if (ast.type === "replvar") {
            return ast.name;
        }
        if (ast.type === "meta") {
            return `(${nd[0].nodes.map(n => this.stringify(n)).join(", ")} ${ast.name} ${nd[1].nodes.map(n => this.stringify(n)).join(", ")})`;
        }
        switch (ast.name) {
            case "~":
            case "!": return `${ast.name}${this.stringify(nd[0])}`;
            case "V":
            case "E":
            case "E!": return `(${ast.name}${this.stringify(nd[0])}: ${this.stringify(nd[1])})`;
            default:
                return `(${this.stringify(nd[0])} ${ast.name} ${this.stringify(nd[1])})`;
        }
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
        const astStr = this.stringify(ast);
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
            for (const [nidx, n] of ast.nodes.entries()) {
                const sub = ast.name.match(/^#?#(nf|(can)?repl)/) && nidx;
                const sup = ast.name.match(/^#?#(can)?repl/) && nidx === 1;
                const noComma = (nidx >= 1 && (sub || sup));
                if (nidx && (!noComma))
                    this.addSpan(varnode, ", ");
                const node = this.ast2HTML(idx, n, scopes);
                if (sub || sup) {
                    const wrappedNode = document.createElement(sup ? "sup" : "sub");
                    if (nidx > 1 && ast.name.match(/^#?#nf/))
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
            else if (scopeStack[0]) {
                el.classList.add("boundedVar");
            }
            else {
                el.classList.add("freeVar");
            }
            // quantvar is only aimed for mark css style
            if (scopeStack[0]?.type === "quantvar")
                scopeStack.pop();
            do {
                if (scopeStack[0] && scopeStack[0].nodes[0].name === ast.name) {
                    varnode.setAttribute("ast-scope", this.stringify(scopeStack[0]));
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
        let str = this.stringify(d.value);
        let steps = d.steps?.map(step => [step.deductionIdx, step.replaceValues.map(v => this.stringify(v)), step.conditionIdxs]);
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
                const inserted = this.stringify(p.value);
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
            itInfo[0].innerHTML = this.stringifyDeductionStep(p.from);
        }, refresh);
    }
    updateDeductionList(refresh) {
        this.updateGuiList("d", this.formalSystem.deductions, this.deductionList, (p, idx) => (this.displayDs.has(p.from.replace("[S]", "")) || (this.displayDs.has("添加的规则") && !p.from.endsWith("[S]"))), (p, itInfo, it) => {
            itInfo[0].innerText = p.from + (p.steps?.length ? "[宏]" : "");
        }, refresh);
    }
    updateMetaRuleList(refresh) {
        this.updateGuiList("m", Object.values(this.formalSystem.metaRules), this.metaRuleList, (p) => true, (p, itInfo, it) => {
            itInfo[0].innerText = p.from;
        }, refresh, Object.keys(this.formalSystem.metaRules).map(e => "m" + e));
    }
    stringifyDeductionStep(step) {
        return `&nbsp;d${step.deductionIdx} ${step.conditionIdxs.join(", ")}`;
    }
}
//# sourceMappingURL=gui.js.map