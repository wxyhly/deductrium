import { TR } from "../lang.js";
import { Assist } from "./assist.js";
import { AST, ASTParser, debugBoundVarId } from "./astparser.js";
import { Core, Context, assignContext } from "./core.js";
import { TypeRule, initTypeSystem } from "./initial.js";
const parser = new ASTParser;
const constructors = new Set<string>();
const destructors = new Set<string>();
const macro = new Set<string>();
const sysmacro = new Set<string>();

let consts = new Set<string>;
type definedConst = [string, AST];
const allrules = initTypeSystem();
const reservedConsts = new Set<string>;
export class TTGui {
    skipRendering = true;
    onStateChange = () => { };
    core = new Core;
    disableSimpleFn = false;
    enablecopygate = false;
    lastGateTarget = "";
    // gamecore = new HoTTGame;
    typeList = document.getElementById("type-list");
    unlockedTypes: Set<string>;
    unlockedTactics: Set<string>;
    inhabitList = document.getElementById("inhabit-list");
    // tactic mode: tactic-begin for waiting clicking theorem
    mode = null;
    // "_" for infered, "@" for original
    inferDisplayMode = "_";
    userDefinedConsts: definedConst[] = [];
    sysDefinedConsts: definedConst[] = [];
    initTypeList() {
        for (const rule of allrules) {
            if (rule.postfix === "计算") {
                const applyList = [];
                let sub = rule.ast.nodes[0];
                while (sub.type === "apply") {
                    applyList.unshift(sub.nodes[1]);
                    sub = sub.nodes[0];
                }
                applyList.unshift(sub);
                this.core.state.computeRules[sub.name] ??= [];
                this.core.state.computeRules[sub.name].push({
                    pattern: this.core.flattenApplyList(rule.ast.nodes[0]),
                    result: rule.ast.nodes[1]
                });
            }
        }
    }
    constructor(creative: boolean, skipRendering: boolean) {
        this.skipRendering = skipRendering;
        this.unlockedTypes = new Set(creative ? allrules.map(r => r.id) : ["True0", "True1", "False0"]);
        if (!skipRendering) this.updateTypeList(this.unlockedTypes);
        if (!creative) {
            this.unlockedTactics = new Set(["qed"]);
            this.disableSimpleFn = true;
        }
        this.initTypeList();
        this.updateInhabitList();
        document.getElementById("add-btn").addEventListener("click", () => {
            this.updateInhabitList();
        });
        const input = document.getElementById("tactic-input") as HTMLInputElement;
        input.addEventListener("keydown", (ev) => {
            if (ev.key === "Enter" || ev.key === "Escape") {
                document.getElementById("tactic-begin").click();
            }
        });
        document.getElementById("tactic-remove").addEventListener("click", () => {
            if (this.mode.length === 1) {
                this.mode = null;
            }
            document.getElementById("tactic-autofill").innerHTML = "";
            document.getElementById("tactic-hint").innerHTML = "";
            document.getElementById("tactic-errmsg").innerText = "";
            document.getElementById("tactic-state").innerHTML = "";
            document.getElementById("tactic-remove").classList.add("hide");
            input.value = "";
            document.getElementById("tactic-input").classList.add("hide");

            if (this.mode?.length > 1) {
                this.mode.pop();
                const newmode = this.mode.slice(1);
                // input.value = parser.stringify(this.mode[0].theorem);
                this.executeTactic(this.mode[0].theorem);
                for (let i = 0; i < newmode.length; i++) {
                    input.value = newmode[i];
                    this.addTactic(i < newmode.length - 1);
                }
                input.value = "";
            }
        });
        document.getElementById("tactic-begin").addEventListener("click", () => {
            this.addTactic(false);
        });
    }
    setLastGateTarget(target: string) {
        this.lastGateTarget = target;
        document.getElementById("copygate").innerText = "";
        const btn = document.createElement("button");
        document.getElementById("copygate").appendChild(document.createTextNode(TR("最近#t门上的目标：")));
        btn.classList.add("inhabitat-modify"); btn.innerText = "+";
        document.getElementById("copygate").appendChild(btn);
        btn.onclick = () => {
            this.executeTactic(target);
        }
        document.getElementById("copygate").appendChild(this.ast2HTML("", parser.parse(target)));
    }
    private autofillTactics(assist: Assist) {
        const allTactics = assist.autofillTactics();
        let tactics: string[];
        if (this.unlockedTactics) {
            tactics = [];
            // only for survival. If creative, this.unlockedTactics is undefined
            for (const t of allTactics) {
                const prefix = t.split(" ")[0];
                if (this.unlockedTactics.has(prefix)) {
                    tactics.push(t);
                }
            }
        } else {
            tactics = allTactics;
        }

        const div = document.getElementById("tactic-autofill");
        const inp = document.getElementById("tactic-input") as HTMLInputElement;
        const exec = document.getElementById("tactic-begin");
        div.innerHTML = tactics.length ? TR("推荐策略：<br>") : "";
        for (const t of tactics) {
            const btn = document.createElement("button");
            div.appendChild(btn);
            btn.innerText = t;
            btn.addEventListener("click", () => {
                inp.value = t;
                if (!t.includes("??")) {
                    exec.click();
                } else {
                    inp.focus();
                    inp.selectionStart = t.indexOf("??");
                    inp.selectionEnd = inp.selectionStart + 2;
                }
            });
        }
    }
    private updateTacticStateDisplay(assist: Assist, statediv: HTMLDivElement) {
        if (!assist.goal.length) {
            this.addSpan(statediv, TR("无目标，请输入qed结束"));
        }

        for (let count = assist.goal.length - 1; count >= 0; count--) {
            const g = assist.goal[count];
            statediv.appendChild(document.createElement("hr"));
            const goalDiv = document.createElement("div");
            const scope = g.context.map(e => ({ type: "var", name: e[0], bondVarId: e[2] } as AST));

            for (const [k, v, id] of g.context) {
                const ast = {
                    type: ":", name: "", nodes: [{ type: "var", name: k }, v]
                };
                ast.nodes[0].checked = ast.nodes[1];
                goalDiv.prepend(document.createElement("br"));
                goalDiv.prepend(this.ast2HTML("", ast, scope, g.context, this.getInhabitatArray().length));
            }
            goalDiv.appendChild(document.createElement("br"));
            this.addSpan(goalDiv, count ? TR("目标") + (count) + TR("：") : TR("当前目标："));
            const printType = Core.clone(g.type);
            try { this.core.checkType(printType, g.context, false); } catch (e) { }
            goalDiv.appendChild(this.ast2HTML("", printType, scope, g.context, this.getInhabitatArray().length));
            if (count) { goalDiv.style.opacity = "0.5"; goalDiv.style.backgroundColor = "#DDD"; }
            goalDiv.appendChild(document.createElement("br"));
            statediv.appendChild(goalDiv);
        }
    }
    private addSpan(parentSpan: HTMLSpanElement, text: string, parseHTML?: boolean) {
        const span = document.createElement("span");
        if (parseHTML) span.innerHTML = text; else span.innerText = text;
        parentSpan.appendChild(span);
        return span;
    }
    ast2HTML(idx: string, ast: AST, scopes: AST[] = [], context: Context = [], userLineNumber = 0) {
        const varnode = document.createElement("span");
        if (!ast) {
            varnode.innerText = TR("表达式因错误而丢失");
            return varnode;
        }
        const astStr = parser.stringify(ast);
        varnode.setAttribute("ast-string", astStr);
        if (ast.type === "var") {
            if (idx === "Checked" && ast.name === "_" && ast.checked?.type === ":") {
                return this.ast2HTML("Checked", ast.checked.nodes[0], scopes, context, userLineNumber);
            }
            let el: HTMLSpanElement;
            if (ast.name.startsWith("@") && (isFinite(Number(ast.name.slice(1))) || ast.name === "@succ" || ast.name === "@max")) {
                el = this.addSpan(varnode, "<sub>" + ast.name + "</sub>", true);
                el.classList.add("universe");
            } else if (ast.name.startsWith("U@")) {
                el = this.addSpan(varnode, "U<sub>" + ast.name.slice(1) + "</sub>", true);
                el.classList.add("universe");
            } else {
                el = this.addSpan(varnode, ast.name);
            }
            if (debugBoundVarId && ast.bondVarId) {
                this.addSpan(el, "<sup>" + ast.bondVarId + "</sup>", true);
            }
            const scopeStack = scopes.slice(0);
            const astname = ast.name.replace(/'+$/g, "");
            if (astname.match(/^[1-9][0-9]*$/)) el.classList.add("constructors");
            else if (destructors.has(astname)) el.classList.add("ind_fn");
            else if (constructors.has(astname)) el.classList.add("constructors");
            else if (consts.has(astname)) el.classList.add("constant");
            else if (macro.has(astname) || sysmacro.has(astname)) el.classList.add("macro");
            else if (!ast.name.startsWith("U@")) {
                el.classList.add("freeVar");
            }
            if (scopeStack[0]?.type === "quantvar") {
                // quantvar is only aimed for mark css style
                if (!el.classList.contains("replvar")) {
                    el.classList.remove("freeVar");
                    el.classList.remove("constant");
                    el.classList.add("boundedVar");
                }
                scopeStack.shift();
            } else {
                do {
                    if (ast.type === "var" && scopeStack[0] && scopeStack[0]?.name === ast.name) {
                        varnode.setAttribute("ast-scope", parser.stringify(scopeStack[0]));
                        if (!el.classList.contains("replvar")) {
                            el.classList.remove("freeVar");
                            el.classList.add("boundedVar");
                        }
                        break;
                    }
                } while (scopeStack.shift());
            }
        } else {
            switch (ast.type) {
                case ":": case ":=": case "===":
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, " &nbsp;" + ast.type + "&nbsp; ", true);
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    break;
                case "->": case "X": case "+":

                    const b1 = !(((ast.type === "+" || ast.type === "->") && ast.nodes[0].type === "X") || ["var"].includes(ast.nodes[0].type) || ast.nodes[0].nodes[0].name == "U");

                    const b2 = !(((ast.type === "+" || ast.type === "->") && ast.nodes[1].type === "X") || (["var", "->", "X"].includes(ast.nodes[1].type) && ast.type !== "X") || ["var"].includes(ast.nodes[1].type) || ast.nodes[1].nodes[0].name == "U");
                    if (b1) this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    if (b1) this.addSpan(varnode, ")");
                    this.addSpan(varnode, ast.type === "X" ? "×" : ast.type === "+" ? "+" : "→");
                    if (b2) this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    if (b2) this.addSpan(varnode, ")");
                    break;
                case ",": case "~": case "~=": case "*":
                    this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, ast.type === "," ? "," : ast.type === "~" ? "~" : ast.type === "~=" ? "≃" : ast.type === "*" ? "∘" : "→");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    this.addSpan(varnode, ")");
                    break;
                case "apply":
                    if (ast.nodes[0].name === "U") {
                        const sub = parser.stringify(ast.nodes[1]);
                        this.addSpan(varnode, `U<sub>${sub.replaceAll(/@([0-9])/g, "$1")}</sub>`, true).classList.add("universe");
                        break;
                    }
                    const br1 = !["apply", "var", ","].includes(ast.nodes[0].type);
                    const br2 = !(["var", ","].includes(ast.nodes[1].type) || ast.nodes[1].nodes[0].name == "U");
                    if (br1) this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    if (br1) this.addSpan(varnode, ")");
                    this.addSpan(varnode, " ");
                    if (br2) this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    if (br2) this.addSpan(varnode, ")");
                    break;
                case "L": case "P": case "S":
                    const outterLayers: HTMLSpanElement[] = [];
                    const newcontext = Object.assign({}, context);
                    const newType = Core.clone(ast.nodes[0]); //this.hott.unbeautify(newType);
                    newcontext[ast.name] = newType;
                    outterLayers.push(this.addSpan(varnode, "" + ast.type.replaceAll("S", "Σ").replaceAll("L", "λ").replaceAll("P", "Π")));
                    const varast = this.ast2HTML(idx, { type: "var", name: ast.name, checked: ast.nodes[0] }, [{ type: "quantvar", name: "quantvar" }, ...scopes], newcontext, userLineNumber);
                    varast.classList.add("boundedVar");
                    if (debugBoundVarId && ast.bondVarId) {
                        this.addSpan(varast, "<sup>" + ast.bondVarId + "</sup>", true);
                    }
                    outterLayers.push(varnode.appendChild(varast));
                    outterLayers.push(this.addSpan(varnode, ":"));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    outterLayers.push(this.addSpan(varnode, ast.type === "L" ? "." : ","));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], [ast, ...scopes], newcontext, userLineNumber));
                    // outterLayers.push(this.addSpan(varnode, ")"));

                    // hightlight constrained vars

                    const constrainedVars = Array.from(varnode.querySelectorAll("span")).filter(
                        node => (node as HTMLSpanElement).getAttribute("ast-scope") === astStr
                    ) as HTMLSpanElement[];
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
                        varnode.classList.add("mediumlighted");
                        for (const node of constrainedVars) {
                            node.classList.add("highlighted");
                        }
                    });
                    outterLayers[1].addEventListener('mouseout', ev => {
                        varnode.classList.remove("mediumlighted");
                        for (const node of constrainedVars) {
                            node.classList.remove("highlighted");
                        }
                    });
                    break;
            }
        }

        // clicks and hovers in this layer
        const spans = Array.from(varnode.childNodes).filter(
            node => !(node as HTMLSpanElement).getAttribute("ast-string")
        ) as HTMLSpanElement[];
        const floatTypeDiv = document.querySelector(".float-type") as HTMLDivElement;
        for (const node of spans) {
            const localCtxt = context;
            const localNumber = userLineNumber;
            node.addEventListener('mouseover', ev => {
                varnode.classList.add("mediumlighted");
                for (const node of spans) {
                    node.classList.add("highlighted");
                }
                floatTypeDiv.style.left = (ev.pageX - 4) + "px";
                floatTypeDiv.style.top = (ev.pageY + 30) + "px";
                this.getHottDefCtxt(localNumber);
                floatTypeDiv.style.display = "block";
                if (ast.checked) {
                    if (scopes[0]?.type === "quantvar") {
                        scopes = scopes.slice(1);
                    }
                    try { floatTypeDiv.appendChild(this.ast2HTML("Checked", ast.checked, scopes, localCtxt, userLineNumber)); } catch (e) {
                        floatTypeDiv.innerText = e;
                    }
                } else if (ast.err) {
                    floatTypeDiv.appendChild(document.createTextNode(ast.err));
                } else {
                    floatTypeDiv.style.display = "none";
                }
            });
            node.addEventListener('mouseout', ev => {
                varnode.classList.remove("mediumlighted");
                for (const node of spans) {
                    node.classList.remove("highlighted");
                }
                floatTypeDiv.style.display = "none";
                floatTypeDiv.innerHTML = "";
            });
        }
        return varnode;
    }
    updateTypeList(terms: Set<string>) {
        const list = this.typeList;
        consts.clear();
        while (list.lastChild) {
            list.removeChild(list.lastChild);
        }
        for (const rule of allrules) {

            // register systype and sysdef in core
            const vname = rule.ast.nodes?.[0]?.name;
            if (rule.ast.type !== "===") {
                reservedConsts.add(vname);
            }
            if (!terms.has(rule.id)) continue;

            if (rule.ast.type === ":") {
                this.core.state.sysTypes[vname] = this.core.desugar(Core.clone(rule.ast.nodes[1]), true);
            }
            // ast.nodes[0].type==="var" -> skip a X b := @Prod _ _ ...
            if (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var") {
                const val = rule.ast.nodes[1].type === ":" ? rule.ast.nodes[1].nodes[0] : rule.ast.nodes[1];
                this.core.state.sysDefs[vname] = this.core.desugar(Core.clone(val), true);
            }

            // register in gui highlight, only ignore ====

            if (rule.ast.type === "var" || rule.ast.type === ":" || (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var")) {
                const vname = rule.ast.type === "var" ? rule.ast.name : rule.ast.nodes[0].name;
                if (rule.postfix === "类型") consts.add(vname);
                if (rule.postfix === "构造") constructors.add(vname);
                if (rule.postfix === "解构") destructors.add(vname);
                if (rule.postfix === "定义") sysmacro.add(vname);
            }
            if (rule.inferMode === "@" && this.inferDisplayMode === "_") continue;
            if (rule.inferMode === "_" && this.inferDisplayMode === "@") continue;

            // register in gui type list

            const itIdx = document.createElement("div");
            list.appendChild(itIdx);
            itIdx.classList.add("idx");
            itIdx.style.width = "30px";
            itIdx.innerText = TR(rule.postfix);

            const itVal = document.createElement("div");
            list.appendChild(itVal);
            itVal.classList.add("val");
            const ast = Core.clone(rule.ast);
            // avoid check const for redefined const error
            // const def = this.core.state.sysDefs[vname];
            // delete this.core.state.sysDefs[vname];
            try { this.core.checkType(ast, [], false); } catch (e) { console.log(e); }
            // this.core.state.sysDefs[vname] = def;
            if (ast.type === "var") {
                itVal.appendChild(this.ast2HTML("", { type: ":", nodes: [ast, ast.checked], name: "" }));
            } else {
                itVal.appendChild(this.ast2HTML("", ast));
            }
            const infoArr = [];
            for (let i = 0; i < 6; i++) {
                const itInfo = document.createElement("div");
                list.appendChild(itInfo);
                itInfo.className = "info";
                infoArr.push(itInfo);
                if (!i) itInfo.innerText = rule.prefix;
            }
        }
    }
    getHottDefCtxt(input: HTMLInputElement | number) {
        macro.clear();
        for (const s of sysmacro) macro.add(s);
        this.core.state.userDefs = {};
        if (typeof input === "number") {
            for (let i = 0; i <= input; i++) {
                const def = this.userDefinedConsts[i];
                if (!def) continue;
                macro.add(def[0]);
                this.core.state.userDefs[def[0]] = def[1];
            }
            return input;
        }
        const arr = this.getInhabitatArray();
        let currentIdx: number;
        for (let i = 0; i < arr.length; i++) {
            const def = this.userDefinedConsts[i];
            if (!def) {
                if (arr[i] === input) { currentIdx = i; break; } else { continue; }
            }
            macro.add(def[0]);
            if (arr[i] === input) { currentIdx = i; break; }
            this.core.state.userDefs[def[0]] = def[1];
        }
        return currentIdx ?? arr.indexOf(input);
    }

    updateInhabitList() {
        const input = document.createElement("input");

        const div = document.createElement("div");
        const button = document.createElement("button");
        div.classList.add("inhabitat-div");
        div.classList.add("hide");
        input.addEventListener("keydown", ev => {
            if (ev.key === "Enter" || ev.key === "Escape") {
                input.blur();
            }
        });
        // updateDefs: true means update all inputs after it,
        // otherwise, update all inputs iff ast is xx := xxxx

        // todo: when remove a ":=", must be updated, so input must record value before edited
        // todo: left btn is to drag order(click: add new line after it), if trim ast str is empty, then remove it aotomatically
        input.onblur = ev => {
            if(!ev["updateDefs"]) ev["updateDefs"] = input["needUpdate"];
            delete input["needUpdate"];
            this.onStateChange();
            const currentIdx = this.getHottDefCtxt(input);
            const inputsarr = this.getInhabitatArray();
            const nextInput = inputsarr[currentIdx + 1];
            this.core.state.disableSimpleFn = this.disableSimpleFn;
            wrapper.classList.remove("error");
            wrapper.classList.remove("infering");
            if (!input.value.trim()) {
                if (nextInput && ev["updateDefs"]) {
                    nextInput.onblur({ updateDefs: true } as any);
                }
                return;
            }
            let ast: AST;
            let parseError = "";
            let error = "";
            try {
                ast = parser.parse(input.value);
            } catch (e) {
                parseError = e;
                wrapper.classList.add("error");
            }
            if (!ast && !parseError) {
                if (nextInput) {
                    nextInput.onblur({} as any);
                }
                return false;
            }
            div.classList.remove("hide");
            input.classList.add("hide");
            while (div.firstChild) {
                div.removeChild(div.firstChild);
            }
            const checkInfer = (ast: AST) => {
                const _checkInfer = (ast: AST, context: Context, expandConsts: Set<string>) => {
                    if (ast.type === "var") {
                        if (ast.name[0] === "?" || ast.name === "_") {
                            if (ast.checked?.type === ":") {
                                return _checkInfer(ast.checked.nodes[0], context, expandConsts);
                            }
                            return false;
                        }
                        if (!context.find(e => e[0] === ast.name)) {
                            // if this is a constant, check its value recursively
                            const pos = this.userDefinedConsts.findIndex(e => e && e[0] === ast.name);
                            if (pos >= 0 && inputsarr[pos].parentElement.classList.contains("infering")) {
                                expandConsts.add(ast.name);
                            }
                        }
                    }
                    if (ast.nodes) {
                        if (!_checkInfer(ast.nodes[0], context, expandConsts)) return false;
                        if (ast.type === "P" || ast.type === "L" || ast.type === "S") {
                            context = assignContext([ast.name, ast.nodes[0], 0], context);
                        }
                        if (!_checkInfer(ast.nodes[1], context, expandConsts)) return false;
                    }
                    return true;
                }
                let nast = ast;
                let expandConsts = new Set<string>;
                while (true) {
                    if (!_checkInfer(nast, [], expandConsts)) { wrapper.classList.add("infering"); return; }
                    if (!expandConsts.size) return;
                    if (nast === ast) { nast = Core.clone(ast); }
                    this.core.expandDef(nast, [], expandConsts);
                    this.core.checkType(nast, [], false);
                    expandConsts = new Set<string>;
                }

            }
            if (ast) {
                try {
                    if (ast.type === ":=") {
                        if (ast.nodes[0].type !== "var") {
                            throw TR(":=符号左侧仅允许出现自定义常量");
                        }
                        const defname = ast.nodes[0].name;
                        if (this.core.checkConst(defname, [])) throw defname + TR("的定义重复");
                        if (reservedConsts.has(defname)) throw defname + TR("由系统保留");
                        const defContent = ast.nodes[1];
                        if (defContent.type === ":") {
                            this.userDefinedConsts[currentIdx] = [defname, this.core.desugar(Core.clone(defContent.nodes[0]), true)];
                        } else {
                            this.userDefinedConsts[currentIdx] = [defname, this.core.desugar(Core.clone(ast.nodes[1]), true)];
                        }
                        // todo: if has error, do not add it
                        macro.add(defname);
                    }
                    this.core.checkType(ast, [], false);
                    checkInfer(ast);
                } catch (e) {
                    error += e;
                    wrapper.classList.add("error");
                }
            }
            const newDom = parseError ? this.addSpan(div, input.value + " - " + parseError) : this.ast2HTML("", ast, [], [], currentIdx);

            div.appendChild(newDom);
            if (ast && error) {
                this.addSpan(div, " - " + error);
            }
            if (ast && !error) {
                if (ast.type[0] != ":") {
                    this.addSpan(div, " &nbsp; : &nbsp; ", true);
                    div.appendChild(this.ast2HTML("", ast.checked, [], [], currentIdx));
                }
            }

            if (nextInput && (ast.type === ":=" || ev["updateDefs"])) {
                nextInput.onblur({ updateDefs: true } as any);
            }
        };
        div.addEventListener("click", ev => {
            if (this.mode === "tactic-begin") {
                this.executeTactic(input.value);
            } else {
                input.classList.remove("hide");
                input["needUpdate"] = input.value.includes(":="); 
                input.focus();
                div.classList.add("hide");
            }
        });
        button.classList.add("inhabitat-modify");
        button.innerText = "-";
        const wrapper = document.createElement("div");
        wrapper.classList.add("wrapper");
        this.inhabitList.insertBefore(wrapper, document.getElementById("add-btn"));
        wrapper.appendChild(button);
        wrapper.appendChild(input);
        wrapper.appendChild(div);
        button.addEventListener("click", () => {
            const current = this.getInhabitatArray().indexOf(input);
            const [removed] = this.userDefinedConsts.splice(current, 1);
            wrapper.remove();
            if (removed) macro.delete(removed[0]);
            const next = this.getInhabitatArray()[current];
            if (next && removed) next.onblur({ updateDefs: true } as any);
            this.onStateChange();
        });
        input.focus();
    }
    // find whether user has inhabitat of given type
    queryType(typeStr: string) {
        this.getHottDefCtxt(this.getInhabitatArray().length);
        const ref = parser.parse(typeStr);
        for (const e of this.getInhabitatArray()) {
            if (!e.classList.contains("hide")) {
                e.onblur({} as any);
            }
            if (e.parentElement.classList.contains("error") || e.parentElement.classList.contains("infering")) continue;
            let ast: AST;
            try {
                ast = parser.parse(e.value);
            } catch (e) {
                continue;
            }
            if (!ast) continue;
            try {
                if (ast.type === ":") {
                    if (this.core.checkType(Core.clone({
                        name: "", type: "===", nodes: [ast.nodes[1], ref]
                    }), [], true)) return true;
                } else if (ast.type === ":=") {
                    if (this.core.checkType(Core.clone({
                        name: "", type: ":", nodes: [ast.nodes[0], ref]
                    }), [], true)) return true;
                } else {
                    if (this.core.checkType(Core.clone({
                        name: "", type: ":", nodes: [ast.nodes[0], ref]
                    }), [], true)) return true;
                }
            } catch (e) {
                continue;
            }
        }
        return false;
    }
    executeTactic(value: string | AST) {
        try {
            this.getHottDefCtxt(this.getInhabitatArray().length);
            const ast = typeof value === "string" ? parser.parse(value) : value;
            if (!ast) throw TR("空表达式");
            if (ast.type === "===") throw TR("不是命题类型");
            if (ast.type === ":=") throw TR("不是命题类型");
            if (ast.type === ":") throw TR("已断言该类型有值");
            const type = this.core.checkType(ast, [], false);
            if (type.type !== "apply" || type.nodes[0].name !== "U") throw TR("不是命题类型");
            const assist = new Assist(this.core, value);
            this.mode = [assist];
            this.autofillTactics(assist);
            document.getElementById("tactic-remove").classList.remove("hide");
            document.getElementById("tactic-hint").innerText = "";
            const theorem = Core.clone(assist.theorem);
            this.core.checkType(theorem, [], false);
            document.getElementById("tactic-hint").appendChild(this.ast2HTML("",
                { type: ":", name: "", nodes: [assist.elem, theorem] }, [], assist.goal.map(g => [g.ast.name, g.type, 0]), this.getInhabitatArray().length));
            document.getElementById("tactic-input").classList.remove("hide");
            document.getElementById("tactic-input").focus();
            this.updateTacticStateDisplay(assist, document.getElementById("tactic-state") as HTMLDivElement);
            window.scrollTo(0, document.body.clientHeight);

        } catch (e) {
            document.getElementById("tactic-hint").innerText = TR("命题格式有误：") + e;
            this.mode = null;
        }
    }
    addTactic(noCheck: boolean) {
        const input = document.getElementById("tactic-input") as HTMLInputElement;
        const hint = document.getElementById("tactic-hint");
        if (!this.mode) {
            hint.innerText = TR("请在定理列表中点选待证命题");
            this.mode = "tactic-begin";
        }
        if (this.mode instanceof Array) {
            const statediv = document.getElementById("tactic-state") as HTMLDivElement;
            const val = input.value.trim();
            const cmdPosPtr = val.indexOf(" ");
            const cmd = cmdPosPtr === -1 ? val : val.slice(0, cmdPosPtr);
            const param = cmdPosPtr === -1 ? null : val.slice(cmdPosPtr);
            let assist = this.mode[0] as Assist;
            this.getHottDefCtxt(this.getInhabitatArray().length);
            document.getElementById("tactic-errmsg").innerText = "";
            while (hint.firstChild) hint.removeChild(hint.firstChild);
            try {
                if (cmd === "qed") {
                    assist.qed();
                    this.updateInhabitList();
                    const output = this.inhabitList.querySelector(".wrapper:last-of-type input") as HTMLInputElement;
                    output.focus();
                    output.value = parser.stringify(assist.elem) + ":" + parser.stringify(assist.theorem);
                    output.blur();
                    input.classList.add("hide");
                    document.getElementById("tactic-remove").classList.add("hide");
                    this.mode = null;
                    hint.innerHTML = "";
                    input.value = "";
                    statediv.innerHTML = "";
                    document.getElementById("tactic-autofill").innerHTML = "";
                    return;
                } else if (assist[cmd]) assist[cmd](param);
                else {
                    throw TR("未知的证明策略");
                }
                // assist.markTargets();
                hint.innerText = "";
                this.mode.push(input.value);
                input.value = "";
                if (noCheck) return;
                input.focus();
                statediv.innerHTML = "";
                for (const m of this.mode) {
                    if (typeof m === "string") {
                        this.addSpan(statediv, m + " . ").className = "blocked";
                    }
                }
                this.updateTacticStateDisplay(assist, statediv);
                this.autofillTactics(assist);

            } catch (e) {
                if (typeof e === "object") {
                    e = TR("当前策略因未知表达式错误执行失败");
                }
                document.getElementById("tactic-errmsg").innerText = e;
            }
            let astShow: AST;
            try {
                astShow = { type: ":", name: "", nodes: [assist.elem, Core.clone(assist.theorem, true)] };
                this.core.checkType(astShow.nodes[1], [], false);
                // this.core.checkType(astShow, [], false);
            } catch (e) {
                document.getElementById("tactic-errmsg").innerText = e;
            }

            assist.markTargets();
            hint.appendChild(this.ast2HTML("", astShow, [], assist.goal.map(g => [g.ast.name, g.type, 0]), this.getInhabitatArray().length));

            window.scrollTo(0, document.body.clientHeight);
            const wrapperDiv = document.getElementById("tactic-list").parentElement;
            wrapperDiv.scrollTo(0, wrapperDiv.clientHeight);
        }
    }
    getInhabitatArray() {
        return Array.from(document.querySelectorAll<HTMLInputElement>(".inhabitat .wrapper input"));
    }
    unlock(str: string, update?: boolean) {
        this.unlockedTypes.add(str);
        if (update && !this.skipRendering) {
            this.updateTypeList(this.unlockedTypes);
            this.getInhabitatArray()[0]?.onblur({ updateDefs: true } as any);
        }
    }
    updateAfterUnlock() {
        if (this.skipRendering) return;
        this.updateTypeList(this.unlockedTypes);
        this.getInhabitatArray()[0]?.onblur({ updateDefs: true } as any);
    }
}