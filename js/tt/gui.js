import { TR } from "../lang.js";
import { Assist } from "./assist.js";
import { ASTParser } from "./astparser.js";
import { Core } from "./core.js";
import { initTypeSystem } from "./initial.js";
const parser = new ASTParser;
const constructors = new Set();
const destructors = new Set();
const macro = new Set();
const sysmacro = new Set();
let consts = new Set;
const allrules = initTypeSystem();
export class TTGui {
    onStateChange = () => { };
    core = new Core;
    disableSimpleFn = false;
    enablecopygate = false;
    lastGateTarget = "";
    // gamecore = new HoTTGame;
    typeList = document.getElementById("type-list");
    unlockedTypes;
    unlockedTactics;
    inhabitList = document.getElementById("inhabit-list");
    // tactic mode
    mode = null;
    // "_" for infered, "@" for original
    inferDisplayMode = "_";
    userDefinedConsts = [];
    sysDefinedConsts = [];
    constructor(creative) {
        this.unlockedTypes = new Set(creative ? allrules.map(r => r.id) : ["True0", "True1", "False0"]);
        this.updateTypeList(this.unlockedTypes);
        if (!creative) {
            this.unlockedTactics = new Set(["qed"]);
            this.disableSimpleFn = true;
        }
        this.updateInhabitList();
        document.getElementById("add-btn").addEventListener("click", () => {
            this.updateInhabitList();
        });
        const input = document.getElementById("tactic-input");
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
                input.value = parser.stringify(this.mode[0].theorem);
                this.executeTactic(input.value);
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
    setLastGateTarget(target) {
        this.lastGateTarget = target;
        document.getElementById("copygate").innerText = "";
        const btn = document.createElement("button");
        document.getElementById("copygate").appendChild(document.createTextNode(TR("最近#t门上的目标：")));
        btn.classList.add("inhabitat-modify");
        btn.innerText = "+";
        document.getElementById("copygate").appendChild(btn);
        btn.onclick = () => {
            this.executeTactic(target);
        };
        document.getElementById("copygate").appendChild(this.ast2HTML("", parser.parse(target)));
    }
    autofillTactics(assist) {
        const allTactics = assist.autofillTactics();
        let tactics;
        if (this.unlockedTactics) {
            tactics = [];
            // only for survival. If creative, this.unlockedTactics is undefined
            for (const t of allTactics) {
                const prefix = t.split(" ")[0];
                if (this.unlockedTactics.has(prefix)) {
                    tactics.push(t);
                }
            }
        }
        else {
            tactics = allTactics;
        }
        const div = document.getElementById("tactic-autofill");
        const inp = document.getElementById("tactic-input");
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
                }
                else {
                    inp.focus();
                    inp.selectionStart = t.indexOf("??");
                    inp.selectionEnd = inp.selectionStart + 2;
                }
            });
        }
    }
    updateTacticStateDisplay(assist, statediv) {
        if (!assist.goal.length) {
            this.addSpan(statediv, TR("无目标，请输入qed结束"));
        }
        for (let count = assist.goal.length - 1; count >= 0; count--) {
            const g = assist.goal[count];
            statediv.appendChild(document.createElement("hr"));
            const goalDiv = document.createElement("div");
            const scope = Object.keys(g.context).map(n => ({ type: "var", name: n }));
            for (const [k, v] of Object.entries(g.context)) {
                const vc = Core.clone(v);
                const ast = {
                    type: ":", name: "", nodes: [
                        { type: "var", name: k }, vc
                    ]
                };
                this.core.checkType(ast, g.context);
                goalDiv.appendChild(this.ast2HTML("", ast, scope, g.context, this.getInhabitatArray().length));
                goalDiv.appendChild(document.createElement("br"));
            }
            goalDiv.appendChild(document.createElement("br"));
            this.addSpan(goalDiv, count ? TR("目标") + (count) + TR("：") : TR("当前目标："));
            try {
                this.core.checkType(g.type, g.context);
            }
            catch (e) { }
            goalDiv.appendChild(this.ast2HTML("", g.type, scope, g.context, this.getInhabitatArray().length));
            if (count) {
                goalDiv.style.opacity = "0.5";
                goalDiv.style.backgroundColor = "#DDD";
            }
            goalDiv.appendChild(document.createElement("br"));
            statediv.appendChild(goalDiv);
        }
    }
    addSpan(parentSpan, text) {
        const span = document.createElement("span");
        span.innerHTML = text;
        parentSpan.appendChild(span);
        return span;
    }
    ast2HTML(idx, ast, scopes = [], context = {}, userLineNumber = 0) {
        const varnode = document.createElement("span");
        if (!ast) {
            varnode.innerText = TR("表达式因错误而丢失");
            return varnode;
        }
        const astStr = parser.stringify(ast);
        varnode.setAttribute("ast-string", astStr);
        if (ast.type === "var") {
            let el;
            if (ast.name.startsWith("@") && isFinite(Number(ast.name.slice(1)))) {
                el = this.addSpan(varnode, "<sub>" + ast.name + "</sub>");
                el.classList.add("universe");
            }
            else if (ast.name.startsWith("U@")) {
                el = this.addSpan(varnode, "U<sub>" + ast.name.slice(1) + "</sub>");
                el.classList.add("universe");
            }
            else {
                el = this.addSpan(varnode, ast.name);
            }
            const scopeStack = scopes.slice(0);
            const astname = ast.name.replace(/'+$/g, "");
            if (astname.match(/^[1-9][0-9]*$/))
                el.classList.add("constructors");
            else if (destructors.has(astname))
                el.classList.add("ind_fn");
            else if (constructors.has(astname))
                el.classList.add("constructors");
            else if (consts.has(astname))
                el.classList.add("constant");
            else if (macro.has(astname) || sysmacro.has(astname))
                el.classList.add("macro");
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
            }
            else {
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
        }
        else {
            switch (ast.type) {
                case ":":
                case ":=":
                case "===":
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, " " + ast.type + " ");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    break;
                case "->":
                case "X":
                case "+":
                    const b1 = !(((ast.type === "+" || ast.type === "->") && ast.nodes[0].type === "X") || ["var"].includes(ast.nodes[0].type) || ast.nodes[0].nodes[0].name == "U");
                    const b2 = !(((ast.type === "+" || ast.type === "->") && ast.nodes[1].type === "X") || (["var", "->", "X"].includes(ast.nodes[1].type) && ast.type !== "X") || ["var"].includes(ast.nodes[1].type) || ast.nodes[1].nodes[0].name == "U");
                    if (b1)
                        this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    if (b1)
                        this.addSpan(varnode, ")");
                    this.addSpan(varnode, ast.type === "X" ? "×" : ast.type === "+" ? "+" : "→");
                    if (b2)
                        this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    if (b2)
                        this.addSpan(varnode, ")");
                    break;
                case ",":
                case "~":
                case "~=":
                case "*":
                    this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, ast.type === "," ? "," : ast.type === "~" ? "~" : ast.type === "~=" ? "≃" : ast.type === "*" ? "∘" : "→");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    this.addSpan(varnode, ")");
                    break;
                case "apply":
                    if (ast.nodes[0].name === "U") {
                        const sub = parser.stringify(ast.nodes[1]);
                        this.addSpan(varnode, `U<sub>${sub.replaceAll(/@([0-9])/g, "$1")}</sub>`).classList.add("universe");
                        break;
                    }
                    const br1 = !["apply", "var"].includes(ast.nodes[0].type);
                    const br2 = !(["var"].includes(ast.nodes[1].type) || ast.nodes[1].nodes[0].name == "U");
                    if (br1)
                        this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    if (br1)
                        this.addSpan(varnode, ")");
                    this.addSpan(varnode, " ");
                    if (br2)
                        this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    if (br2)
                        this.addSpan(varnode, ")");
                    break;
                case "L":
                case "P":
                case "S":
                    const outterLayers = [];
                    const newcontext = Object.assign({}, context);
                    const newType = Core.clone(ast.nodes[0]); //this.hott.unbeautify(newType);
                    newcontext[ast.name] = newType;
                    outterLayers.push(this.addSpan(varnode, "" + ast.type.replaceAll("S", "Σ").replaceAll("L", "λ").replaceAll("P", "Π")));
                    const varast = this.ast2HTML(idx, { type: "var", name: ast.name, checked: ast.nodes[0] }, [{ type: "quantvar", name: "quantvar" }, ...scopes], newcontext, userLineNumber);
                    varast.classList.add("boundedVar");
                    outterLayers.push(varnode.appendChild(varast));
                    outterLayers.push(this.addSpan(varnode, ":"));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    outterLayers.push(this.addSpan(varnode, ast.type === "L" ? "." : ","));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], [ast, ...scopes], newcontext, userLineNumber));
                    // outterLayers.push(this.addSpan(varnode, ")"));
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
        const spans = Array.from(varnode.childNodes).filter(node => !node.getAttribute("ast-string"));
        const floatTypeDiv = document.querySelector(".float-type");
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
                    try {
                        floatTypeDiv.appendChild(this.ast2HTML("", ast.checked, scopes, localCtxt, userLineNumber));
                    }
                    catch (e) {
                        floatTypeDiv.innerText = e;
                    }
                }
                else if (ast.err) {
                    floatTypeDiv.appendChild(document.createTextNode(ast.err));
                }
                else {
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
    updateTypeList(terms) {
        const list = this.typeList;
        consts.clear();
        while (list.lastChild) {
            list.removeChild(list.lastChild);
        }
        for (const rule of allrules) {
            if (!terms.has(rule.id))
                continue;
            // register in core
            if (rule.ast.type === ":") {
                const vname = rule.ast.nodes[0].name;
                this.core.state.sysTypes[vname] = Core.clone(rule.ast.nodes[1]);
            }
            if (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var") {
                const vname = rule.ast.nodes[0].name;
                this.core.state.sysDefs[vname] = Core.clone(rule.ast.nodes[1]);
            }
            // register in gui highlight, only ignore ====
            if (rule.ast.type === "var" || rule.ast.type === ":" || (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var")) {
                const vname = rule.ast.type === "var" ? rule.ast.name : rule.ast.nodes[0].name;
                if (rule.postfix === "类型")
                    consts.add(vname);
                if (rule.postfix === "构造")
                    constructors.add(vname);
                if (rule.postfix === "解构")
                    destructors.add(vname);
                if (rule.postfix === "定义")
                    sysmacro.add(vname);
            }
            if (rule.inferMode === "@" && this.inferDisplayMode === "_")
                continue;
            if (rule.inferMode === "_" && this.inferDisplayMode === "@")
                continue;
            // register in gui type list
            const itIdx = document.createElement("div");
            list.appendChild(itIdx);
            itIdx.classList.add("idx");
            itIdx.style.width = "30px";
            itIdx.innerText = TR(rule.postfix);
            const itVal = document.createElement("div");
            list.appendChild(itVal);
            itVal.classList.add("val");
            if (rule.ast.type === ":=") {
                try {
                    this.core.checkType(rule.ast.nodes[1]);
                }
                catch (e) {
                    console.log(e);
                }
                rule.ast.checked = rule.ast.nodes[0].checked = rule.ast.nodes[1].checked;
            }
            else if (rule.ast.type === "===") {
                try {
                    this.core.checkType(rule.ast.nodes[0]);
                    this.core.checkType(rule.ast.nodes[1], {}, null, this.core.state.inferValues);
                    rule.ast.checked = rule.ast.nodes[0].checked;
                }
                catch (e) {
                    // console.log(e);
                }
            }
            else {
                try {
                    this.core.checkType(rule.ast);
                }
                catch (e) {
                    // console.log(e);
                }
            }
            if (rule.ast.type === "var") {
                try {
                    this.core.checkType(rule.ast.checked, {}, null, this.core.state.inferValues);
                }
                catch (e) {
                    console.log(e);
                }
                itVal.appendChild(this.ast2HTML("", { type: ":", nodes: [rule.ast, rule.ast.checked], name: "" }));
            }
            else {
                itVal.appendChild(this.ast2HTML("", rule.ast));
            }
            const infoArr = [];
            for (let i = 0; i < 6; i++) {
                const itInfo = document.createElement("div");
                list.appendChild(itInfo);
                itInfo.className = "info";
                infoArr.push(itInfo);
                if (!i)
                    itInfo.innerText = rule.prefix;
            }
            itVal.addEventListener("click", () => {
                // const inserted = this.cmd.astparser.stringify(p.value);
                // this.cmd.onClickSubAst(pname, inserted);
            });
        }
    }
    getHottDefCtxt(input) {
        macro.clear();
        for (const s of sysmacro)
            macro.add(s);
        this.core.state.userDefs = {};
        if (typeof input === "number") {
            for (let i = 0; i <= input; i++) {
                const def = this.userDefinedConsts[i];
                if (!def)
                    continue;
                macro.add(def[0]);
                this.core.state.userDefs[def[0]] = def[1];
            }
            return input;
        }
        const arr = this.getInhabitatArray();
        let currentIdx;
        for (let i = 0; i < arr.length; i++) {
            const def = this.userDefinedConsts[i];
            if (!def) {
                if (arr[i] === input) {
                    currentIdx = i;
                    break;
                }
                else {
                    continue;
                }
            }
            macro.add(def[0]);
            if (arr[i] === input) {
                currentIdx = i;
                break;
            }
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
        input.onblur = ev => {
            this.onStateChange();
            const currentIdx = this.getHottDefCtxt(input);
            const inputsarr = this.getInhabitatArray();
            const nextInput = inputsarr[currentIdx + 1];
            this.core.state.disableSimpleFn = this.disableSimpleFn;
            wrapper.classList.remove("error");
            wrapper.classList.remove("infering");
            if (!input.value.trim()) {
                if (nextInput) {
                    nextInput.onblur({});
                }
                return;
            }
            let ast;
            let parseError = "";
            let error = "";
            try {
                ast = parser.parse(input.value);
            }
            catch (e) {
                parseError = e;
                wrapper.classList.add("error");
            }
            if (!ast && !parseError) {
                if (nextInput) {
                    nextInput.onblur({});
                }
                return false;
            }
            div.classList.remove("hide");
            input.classList.add("hide");
            while (div.firstChild) {
                div.removeChild(div.firstChild);
            }
            let type;
            // todo
            const checkInfer = (ast) => {
                const currentInferred = Object.assign({}, this.core.state.inferValues);
                const currentInferId = this.core.state.inferId;
                const allvars = Core.getFreeVars(ast);
                if (ast.checked)
                    Core.getFreeVars(ast.checked, allvars);
                for (const v of allvars) {
                    if (v.startsWith("?") || v === "_") {
                        wrapper.classList.add("infering");
                        return true;
                    }
                    if (this.core.state.userDefs[v]) {
                        const pos = this.userDefinedConsts.findIndex(e => e && e[0] === v);
                        if (!inputsarr[pos].parentElement.classList.contains("infering"))
                            continue;
                        const expcheck = Core.clone(ast, true);
                        this.core.expandDef(expcheck, new Set([v]));
                        this.core.check(expcheck, {}, false);
                        this.core.afterCheckType(expcheck, expcheck);
                        const res = checkInfer(expcheck);
                        this.core.state.inferValues = currentInferred;
                        this.core.state.inferId = currentInferId;
                        return res;
                    }
                }
                return false;
                // for (const v of Object.values(this.core.state.inferValues)) {
                //     const allvars = Core.getFreeVars(v);
                //     for (const v of allvars) {
                //         if (v.startsWith("?") || v === "_") {
                //             wrapper.classList.add("infering");
                //             return true;
                //         }
                //     }
                // }
                // return false;
            };
            if (ast) {
                try {
                    if (ast.type === ":=") {
                        if (ast.nodes[0].type !== "var") {
                            throw TR(":=符号左侧仅允许出现自定义常量");
                        }
                        const defname = ast.nodes[0].name;
                        if (this.core.checkConst(defname))
                            throw defname + TR("的定义重复");
                        const inferedAst = {};
                        this.core.checkType(ast.nodes[1], {}, inferedAst);
                        checkInfer(inferedAst);
                        macro.add(defname);
                        const defContent = ast.nodes[1];
                        if (defContent.type === ":") {
                            const type = defContent.nodes[1];
                            inferedAst.nodes[0].checked = type;
                            ast.nodes[0].checked = type;
                            this.userDefinedConsts[currentIdx] = [ast.nodes[0].name, inferedAst.nodes[0]];
                        }
                        else {
                            ast.nodes[0].checked = ast.nodes[1].checked;
                            this.userDefinedConsts[currentIdx] = [ast.nodes[0].name, ast.nodes[1]];
                        }
                    }
                    else {
                        const outast = {};
                        type = this.core.checkType(ast, {}, outast);
                        checkInfer(outast);
                    }
                }
                catch (e) {
                    error += e;
                    wrapper.classList.add("error");
                }
            }
            const newDom = parseError ? this.addSpan(div, input.value + " - " + parseError) : this.ast2HTML("", ast, [], {}, currentIdx);
            div.appendChild(newDom);
            if (ast && error) {
                this.addSpan(div, " - " + error);
            }
            if (ast && !error) {
                if (ast.type[0] != ":")
                    this.addSpan(div, " &nbsp; : &nbsp; ");
                if (type) {
                    try {
                        this.core.checkType(type, {}, null, this.core.state.inferValues);
                        checkInfer();
                    }
                    catch (e) {
                    }
                    div.appendChild(this.ast2HTML("", type, [], {}, currentIdx));
                }
            }
            if (nextInput) {
                nextInput.onblur({});
            }
        };
        div.addEventListener("click", ev => {
            if (this.mode === "tactic-begin") {
                this.executeTactic(input.value);
            }
            else {
                input.classList.remove("hide");
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
            if (removed)
                macro.delete(removed[0]);
            const next = this.getInhabitatArray()[current];
            if (next)
                next.onblur({});
            this.onStateChange();
        });
        input.focus();
    }
    // find whether user has inhabitat of given type
    queryType(typeStr) {
        this.getHottDefCtxt(this.getInhabitatArray().length);
        const ref = parser.parse(typeStr);
        for (const e of this.getInhabitatArray()) {
            if (!e.classList.contains("hide")) {
                e.onblur({});
            }
            if (e.parentElement.classList.contains("error") || e.parentElement.classList.contains("infering"))
                continue;
            let ast;
            try {
                ast = parser.parse(e.value);
            }
            catch (e) {
                continue;
            }
            if (!ast)
                continue;
            try {
                if (ast.type === ":") {
                    if (this.core.checkType({
                        name: "", type: "===", nodes: [ast.nodes[1], ref]
                    }))
                        return true;
                }
                else if (ast.type === ":=") {
                    if (this.core.checkType({
                        name: "", type: "===", nodes: [this.core.checkType(ast.nodes[0]), ref]
                    }))
                        return true;
                }
                else {
                    if (this.core.checkType({
                        name: "", type: "===", nodes: [this.core.checkType(ast), ref]
                    }))
                        return true;
                }
            }
            catch (e) {
                continue;
            }
        }
        return false;
    }
    updateGuiList(prefix, logicArray, list, filter, setInfo, refresh, customIdx) {
        if (refresh) {
            while (list.lastChild) {
                list.removeChild(list.lastChild);
            }
            list.setAttribute("total", "0");
        }
        let listLength = Number(list.getAttribute("total")) || 0;
        const values = Object.values(logicArray);
        const keys = Object.keys(logicArray);
        const targetLength = values.length;
        list.setAttribute("total", String(targetLength));
        for (; listLength > targetLength; listLength--) {
            const p = values[listLength];
            if (!filter(p, keys[listLength]))
                continue;
            for (let i = 0; i < 8; i++)
                list.removeChild(list.lastChild);
        }
        for (; listLength < targetLength; listLength++) {
            const p = values[listLength];
            const pname = customIdx ? customIdx[listLength] : prefix + listLength;
            if (!filter(p, keys[listLength]))
                continue;
            const itIdx = document.createElement("div");
            list.appendChild(itIdx);
            itIdx.classList.add("idx");
            itIdx.innerText = pname;
            const itVal = document.createElement("div");
            list.appendChild(itVal);
            itVal.classList.add("val");
            itVal.appendChild(this.ast2HTML(pname, p));
            const infoArr = [];
            for (let i = 0; i < 6; i++) {
                const itInfo = document.createElement("div");
                list.appendChild(itInfo);
                itInfo.className = "info";
                infoArr.push(itInfo);
            }
            setInfo(p, infoArr, itVal);
            itVal.addEventListener("click", () => {
                // const inserted = this.cmd.astparser.stringify(p.value);
                // this.cmd.onClickSubAst(pname, inserted);
            });
        }
        list.scroll({ top: list.scrollHeight });
    }
    executeTactic(value) {
        try {
            this.getHottDefCtxt(this.getInhabitatArray().length);
            const ast = parser.parse(value);
            if (!ast)
                throw TR("空表达式");
            if (ast.type === "===")
                throw TR("不是命题类型");
            if (ast.type === ":=")
                throw TR("不是命题类型");
            if (ast.type === ":")
                throw TR("已断言该类型有值");
            const type = this.core.checkType(ast);
            if (type.type !== "apply" || type.nodes[0].name !== "U")
                throw TR("不是命题类型");
            const assist = new Assist(this.core, value);
            this.mode = [assist];
            this.autofillTactics(assist);
            document.getElementById("tactic-remove").classList.remove("hide");
            document.getElementById("tactic-hint").innerText = "";
            document.getElementById("tactic-hint").appendChild(this.ast2HTML("", { type: ":", name: "", nodes: [assist.elem, ast] }, [], Object.fromEntries(assist.goal.map(g => [g.ast.name, g.type])), this.getInhabitatArray().length));
            document.getElementById("tactic-input").classList.remove("hide");
            document.getElementById("tactic-input").focus();
            this.updateTacticStateDisplay(assist, document.getElementById("tactic-state"));
            window.scrollTo(0, document.body.clientHeight);
        }
        catch (e) {
            document.getElementById("tactic-hint").innerText = TR("命题格式有误：") + e;
            this.mode = null;
        }
    }
    addTactic(noCheck) {
        const input = document.getElementById("tactic-input");
        const hint = document.getElementById("tactic-hint");
        if (!this.mode) {
            hint.innerText = TR("请在定理列表中点选待证命题");
            this.mode = "tactic-begin";
        }
        if (this.mode instanceof Array) {
            const statediv = document.getElementById("tactic-state");
            const val = input.value.trim();
            const cmdPosPtr = val.indexOf(" ");
            const cmd = cmdPosPtr === -1 ? val : val.slice(0, cmdPosPtr);
            const param = cmdPosPtr === -1 ? null : val.slice(cmdPosPtr);
            let assist = this.mode[0];
            this.getHottDefCtxt(this.getInhabitatArray().length);
            document.getElementById("tactic-errmsg").innerText = "";
            while (hint.firstChild)
                hint.removeChild(hint.firstChild);
            try {
                if (cmd === "qed") {
                    assist.qed();
                    this.updateInhabitList();
                    const output = this.inhabitList.querySelector(".wrapper:last-of-type input");
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
                }
                else if (assist[cmd])
                    assist[cmd](param);
                else {
                    throw TR("未知的证明策略");
                }
                assist.markTargets();
                hint.innerText = "";
                this.mode.push(input.value);
                input.value = "";
                if (noCheck)
                    return;
                input.focus();
                statediv.innerHTML = "";
                for (const m of this.mode) {
                    if (typeof m === "string") {
                        this.addSpan(statediv, m + " . ").className = "blocked";
                    }
                }
                this.updateTacticStateDisplay(assist, statediv);
                this.autofillTactics(assist);
            }
            catch (e) {
                document.getElementById("tactic-errmsg").innerText = e;
            }
            let astShow;
            try {
                astShow = { type: ":", name: "", nodes: [assist.elem, assist.theorem] };
                this.core.checkType(astShow);
            }
            catch (e) {
                // document.getElementById("tactic-errmsg").innerText = e;
            }
            assist.markTargets();
            hint.appendChild(this.ast2HTML("", astShow, [], Object.fromEntries(assist.goal.map(g => [g.ast.name, g.type])), this.getInhabitatArray().length));
            window.scrollTo(0, document.body.clientHeight);
            const wrapperDiv = document.getElementById("tactic-list").parentElement;
            wrapperDiv.scrollTo(0, wrapperDiv.clientHeight);
        }
    }
    getInhabitatArray() {
        return Array.from(document.querySelectorAll(".inhabitat .wrapper input"));
    }
    unlock(str, update) {
        this.unlockedTypes.add(str);
        if (update) {
            this.updateTypeList(this.unlockedTypes);
            this.getInhabitatArray()[0].onblur({});
        }
    }
    updateAfterUnlock() {
        this.updateTypeList(this.unlockedTypes);
        this.getInhabitatArray()[0].onblur({});
    }
}
//# sourceMappingURL=gui.js.map