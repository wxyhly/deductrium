import { Assist } from "./assist.js";
import { AST, ASTParser } from "./astparser.js";
import { Context, HoTT, HoTTFeatures } from "./check.js";
import { Core } from "./core.js";
import { TypeRule, initTypeSystem } from "./initial.js";
const parser = new ASTParser;
const constructors = new Set<string>();
const destructors = new Set<string>();
const macro = new Set<string>();
const sysmacro = new Set<string>();

const list = [

    "#pair",

    "pair : Pa:U,Pb:(Px:a,U),Px:a,Py:b x,Sx:a,b x",
    "ind_pair : Pa:U,Pb:(Px:a,U),PC:Pm:Sx:a,b x,U, Pc:Px:a,Py:b x,C (pair a b x y), Pm:Sx:a,b x, C m",
    "ind_pair $1 $2 $3 $4 (pair $1 $2 $5 $6):=$4 $5 $6",

    "ind_eq : Pa:U, PC:(Px:a,Py:a,Pm:eq a x y,U),Pc:Px:a,C x x (refl a x), Px:a,Py:a, Pm:eq a x y, C x y m",
    "ind_eq $1 $2 $3 $4 $4 (refl $1 $4) := $3 $4",

    "#True",

    "True : U",
    "true : True",
    "ind_True : PC:Pm:True,U,Pc:C true, Pm:True, C m",
    "ind_True $1 $2 true := $2",


    "Bool: U",
    "0b:Bool",
    "1b: Bool",
    "ind_Bool: PC:Pm:Bool,U,Pc1:C 0b,Pc2:C 1b, Pm:Bool, C m",


    "#False",

    "False : U",
    "ind_False : PC:Pm:False,U, Pm:False, C m",

    "#nat",

    "nat : U",
    "0 : nat",
    "succ : Px:nat,nat",
    "ind_nat : PC:Px:nat,U,Pc0:C 0,Pcs:(Px:nat,Py:C x,C (succ x)),Px:nat,C x",
    "ind_nat $1 $2 $3 0 := $2",
    "ind_nat $1 $2 $3 (succ $4) := $3 $4 (ind_nat $1 $2 $3 $4)",

    "#union",

    "union : Pa:U,Pb:U,U",
    "inl : Pa:U,Pb:U,Px:a,union a b",
    "inr : Pa:U,Pb:U,Px:b,union a b",
    "ind_union : Pa:U,Pb:U,PQ:Px:union a b,U,Pc1:Px:a,Q (inl a b x),Pc2:Px:b,Q (inr a b x),Px:union a b,Q x",
    "ind_union $1 $2 $3 $4 $5 (inl $1 $2 $6):=$4 $6",
    "ind_union $1 $2 $3 $4 $5 (inr $1 $2 $6):=$5 $6",

    "#nat macro",

    "add := ind_nat (Lx:nat.Py:nat,nat) (Lx:nat.x) Lx':nat.Lx:Py:nat,nat.Ly:nat.succ (x y)",
    "double:=ind_nat (Lx:nat.nat) 0 Lx':nat.Lx:nat.succ (succ x)",
    "mult:=ind_nat (Lx:nat.Py:nat,nat) (Lx:nat.0) Lx':nat.Lx:Py:nat,nat.Ly:nat.add (x y) y",
    "power:=ind_nat (Lx:nat.Py:nat,nat) (Lx:nat.1) Lx':nat.Lx:Py:nat,nat.Ly:nat.mult (x y) y",
    "pred:=ind_nat (Lx:nat.nat) 0 Lx':nat.Lx:nat.x'",

    "#hott axiom",

    "ua : Pa:U,Pb:U,Px:a~=b,eq' U a b",
    "funext : Pa:U,Pp:Px:a,U,Pf:Px:a,p x,Pg:Px:a,p x,Py:(Px:a,eq (p x) (f x) (g x)),(eq (Px:a,p x) f g)",

];
let info = "";
let listTerms: AST[] = [];
let listInfos: [string, string][] = [];
let consts = new Set<string>;
type definedConst = [AST, AST];
const allrules = initTypeSystem();
export class TTGui {
    onStateChange = () => { };
    core = new Core;
    // gamecore = new HoTTGame;
    typeList = document.getElementById("type-list");
    inhabitList = document.getElementById("inhabit-list");
    // tactic mode
    mode = null;
    // "_" for infered, "@" for original
    inferDisplayMode = "@";
    userDefinedConsts: definedConst[] = [];
    sysDefinedConsts: definedConst[] = [];

    constructor(creative: boolean) {

        this.updateTypeList(new Set(creative ? allrules.map(r => r.id) : []));
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
                input.value = parser.stringify(this.mode[0].theorem);
                this.executeTactic(input);
                for (const m of newmode) {
                    input.value = m;
                    document.getElementById("tactic-begin").click();
                }
                input.value = "";
            }
        });
        document.getElementById("tactic-begin").addEventListener("click", () => {
            this.addTactic();
        });
    }
    private autofillTactics(assist: Assist) {
        const tactics = assist.autofillTactics();
        const div = document.getElementById("tactic-autofill");
        const inp = document.getElementById("tactic-input") as HTMLInputElement;
        const exec = document.getElementById("tactic-begin");
        div.innerHTML = tactics.length ? "推荐策略：<br>" : "";
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
            this.addSpan(statediv, "无目标，请输入qed结束");
        }

        for (let count = assist.goal.length - 1; count >= 0; count--) {
            const g = assist.goal[count];
            statediv.appendChild(document.createElement("hr"));
            const goalDiv = document.createElement("div");
            const scope = Object.keys(g.context).map(n => ({ type: "var", name: n } as AST));

            for (const [k, v] of Object.entries(g.context)) {
                const vc = Core.clone(v);
                const ast = {
                    type: ":", name: "", nodes: [
                        { type: "var", name: k }, vc]
                };
                this.core.checkType(ast, g.context);
                goalDiv.appendChild(this.ast2HTML("", ast, scope, g.context, this.getInhabitatArray().length));
                goalDiv.appendChild(document.createElement("br"));
            }
            goalDiv.appendChild(document.createElement("br"));
            this.addSpan(goalDiv, count ? "目标" + (count) + "：" : "当前目标：");
            this.core.checkType(g.type, g.context);
            goalDiv.appendChild(this.ast2HTML("", g.type, scope, g.context, this.getInhabitatArray().length));
            if (count) { goalDiv.style.opacity = "0.5"; goalDiv.style.backgroundColor = "#DDD"; }
            goalDiv.appendChild(document.createElement("br"));
            statediv.appendChild(goalDiv);
        }
    }
    private addSpan(parentSpan: HTMLSpanElement, text: string) {
        const span = document.createElement("span");
        span.innerHTML = text;
        parentSpan.appendChild(span);
        return span;
    }
    ast2HTML(idx: string, ast: AST, scopes: AST[] = [], context: Context = {}, userLineNumber = 0) {
        const varnode = document.createElement("span");
        const astStr = parser.stringify(ast);
        varnode.setAttribute("ast-string", astStr);
        if (ast.type === "var") {
            let el: HTMLSpanElement;
            if (ast.name.startsWith("@") && isFinite(Number(ast.name.slice(1)))) {
                el = this.addSpan(varnode, "<sub>" + ast.name + "</sub>");
                el.classList.add("universe");
            } else if (ast.name.startsWith("U@")) {
                el = this.addSpan(varnode, "U<sub>" + ast.name.slice(1) + "</sub>");
                el.classList.add("universe");
            } else {
                el = this.addSpan(varnode, ast.name);
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
                    this.addSpan(varnode, " " + ast.type + " ");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    break;
                case "->": case "X": case "+":

                    const b1 = !((ast.type === "+" && ast.nodes[0].type === "X") || ["var"].includes(ast.nodes[0].type) || ast.nodes[0].nodes[0].name == "U");

                    const b2 = !(["var", "->", "x"].includes(ast.nodes[1].type) || ast.nodes[1].nodes[0].name == "U");
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
                        this.addSpan(varnode, `U<sub>${sub.replaceAll(/@([0-9])/g, "$1")}</sub>`).classList.add("universe");
                        break;
                    }
                    const br1 = !["apply", "var"].includes(ast.nodes[0].type);
                    const br2 = !(["var"].includes(ast.nodes[1].type) || ast.nodes[1].nodes[0].name == "U");
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
                    try { floatTypeDiv.appendChild(this.ast2HTML("", ast.checked, scopes, localCtxt, userLineNumber)); } catch (e) {
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
            if (!terms.has(rule.id)) continue;

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
            itIdx.innerText = rule.postfix;

            const itVal = document.createElement("div");
            list.appendChild(itVal);
            itVal.classList.add("val");
            if (rule.ast.type === ":=") {
                try { this.core.checkType(rule.ast.nodes[1]); } catch (e) { console.log(e); }
                rule.ast.checked = rule.ast.nodes[0].checked = rule.ast.nodes[1].checked;
            } else if (rule.ast.type === "===") {
                try {
                    this.core.checkType(rule.ast.nodes[0]);
                    this.core.checkType(rule.ast.nodes[1], {}, null, this.core.state.inferValues);
                    rule.ast.checked = rule.ast.nodes[0].checked;
                } catch (e) { console.log(e); }
            } else {
                try { this.core.checkType(rule.ast); } catch (e) { console.log(e); }
            }
            if (rule.ast.type === "var") {
                try { this.core.checkType(rule.ast.checked, {}, null, this.core.state.inferValues); } catch (e) { console.log(e); }
                itVal.appendChild(this.ast2HTML("", { type: ":", nodes: [rule.ast, rule.ast.checked], name: "" }));
            } else {
                itVal.appendChild(this.ast2HTML("", rule.ast));
            }
            const infoArr = [];
            for (let i = 0; i < 6; i++) {
                const itInfo = document.createElement("div");
                list.appendChild(itInfo);
                itInfo.className = "info";
                infoArr.push(itInfo);
                if (!i) itInfo.innerText = rule.prefix;
            }
            itVal.addEventListener("click", () => {
                // const inserted = this.cmd.astparser.stringify(p.value);
                // this.cmd.onClickSubAst(pname, inserted);
            });
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
                macro.add(def[0].name);
                this.core.state.userDefs[def[0].name] = def[1];
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
            macro.add(def[0].name);
            if (arr[i] === input) { currentIdx = i; break; }
            this.core.state.userDefs[def[0].name] = def[1];
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
            const nextInput = this.getInhabitatArray()[currentIdx + 1];
            wrapper.classList.remove("error");
            if (!input.value.trim()) {
                if (nextInput) {
                    nextInput.onblur({} as any);
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
            let type: AST;
            if (ast) {
                try {
                    if (ast.type === ":=") {
                        if (ast.nodes[0].type !== "var") {
                            throw ":=符号左侧仅允许出现自定义常量";
                        }
                        const defname = ast.nodes[0].name;
                        if (this.core.checkConst(defname)) throw defname + "的定义重复";
                        const inferedAst = {} as AST;
                        this.core.checkType(ast.nodes[1], {}, inferedAst);
                        macro.add(defname);
                        const defContent = ast.nodes[1];
                        if (defContent.type === ":") {
                            const type = defContent.nodes[1];
                            inferedAst.nodes[0].checked = type;
                            ast.nodes[0].checked = type;
                            this.userDefinedConsts[currentIdx] = [ast.nodes[0], inferedAst.nodes[0]];
                        } else {
                            ast.nodes[0].checked = ast.nodes[1].checked;
                            this.userDefinedConsts[currentIdx] = [ast.nodes[0], ast.nodes[1]];
                        }
                    } else {
                        type = this.core.checkType(ast);
                    }
                } catch (e) {
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
                if (ast.type[0] != ":") this.addSpan(div, " &nbsp; : &nbsp; ");
                if (type) {
                    try {
                        this.core.checkType(type, {}, null, this.core.state.inferValues);
                    } catch (e) {
                    }
                    div.appendChild(this.ast2HTML("", type, [], {}, currentIdx));
                }
            }
            if (nextInput) {
                nextInput.onblur({} as any);
            }
        };
        div.addEventListener("click", ev => {
            if (this.mode === "tactic-begin") {
                this.executeTactic(input);
            } else {
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
            if (removed) macro.delete(removed[0].name);
            const next = this.getInhabitatArray()[current];
            if (next) next.onblur({} as any);
            this.onStateChange();
        });
        input.focus();
    }
    // find whether user has inhabitat of given type
    queryType(typeStr: string) {
        // const ref = this.hott.parse(typeStr);
        // for (const e of this.getInhabitatArray()) {
        //     if (!e.classList.contains("hide")) {
        //         e.onblur({} as any);
        //     }
        //     if (e.parentElement.classList.contains("error")) continue;
        //     let ast: AST;
        //     try {
        //         ast = parser.parse(e.value);
        //     } catch (e) {
        //         continue;
        //     }
        //     if (!ast) continue;
        //     try {
        //         ast = this.hott.parse(e.value);
        //         if (ast.type === ":") {
        //             if (this.hott.equal(ast.nodes[1], ref, {})) return true;
        //         } else {
        //             if (this.hott.equal(this.hott.check(ast), ref, {})) return true;
        //         }
        //     } catch (e) {
        //         continue;
        //     }
        // }
        // return false;
    }
    private updateGuiList<T extends AST>(
        prefix: string, logicArray: T[] | { [name: string]: T }, list: HTMLElement,
        filter: (term: T, idx: string) => boolean,
        setInfo: (term: T, itInfo: HTMLElement[], it: HTMLElement) => void,
        refresh?: boolean, customIdx?: string[]
    ) {
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
            if (!filter(p, keys[listLength])) continue;
            for (let i = 0; i < 8; i++) list.removeChild(list.lastChild);
        }
        for (; listLength < targetLength; listLength++) {
            const p = values[listLength];
            const pname = customIdx ? customIdx[listLength] : prefix + listLength;
            if (!filter(p, keys[listLength])) continue;

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
    executeTactic(inputDom: HTMLInputElement) {
        try {
            this.getHottDefCtxt(this.getInhabitatArray().length);
            const ast = parser.parse(inputDom.value);
            if (!ast) throw "空表达式";
            if (ast.type === "===") throw "不是命题类型";
            if (ast.type === ":=") throw "不是命题类型";
            if (ast.type === ":") throw "已断言该类型有值";
            const type = this.core.checkType(ast);
            if (type.type !== "apply" || type.nodes[0].name !== "U") throw "不是命题类型";
            const assist = new Assist(this.core, inputDom.value);
            this.mode = [assist];
            this.autofillTactics(assist);
            document.getElementById("tactic-remove").classList.remove("hide");
            document.getElementById("tactic-hint").innerText = "";
            document.getElementById("tactic-hint").appendChild(this.ast2HTML("",
                { type: ":", name: "", nodes: [assist.elem, ast] }, [], Object.fromEntries(assist.goal.map(g => [g.ast.name, g.type])), this.getInhabitatArray().length));
            document.getElementById("tactic-input").classList.remove("hide");
            document.getElementById("tactic-input").focus();
            this.updateTacticStateDisplay(assist, document.getElementById("tactic-state") as HTMLDivElement);
            window.scrollTo(0, document.body.clientHeight);

        } catch (e) {
            document.getElementById("tactic-hint").innerText = "命题格式有误：" + e;
            this.mode = null;
        }
    }
    addTactic() {
        const input = document.getElementById("tactic-input") as HTMLInputElement;
        const hint = document.getElementById("tactic-hint");
        if (!this.mode) {
            hint.innerText = "请在定理列表中点选待证命题";
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
                    throw "未知的证明策略";
                }
                assist.markTargets();
                hint.innerText = "";
                this.mode.push(input.value);
                input.value = "";
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
                document.getElementById("tactic-errmsg").innerText = e;
            }
            const astShow = { type: ":", name: "", nodes: [assist.elem, assist.theorem] };
            this.core.checkType(astShow);

            assist.markTargets();
            hint.appendChild(this.ast2HTML("", astShow, [], Object.fromEntries(assist.goal.map(g => [g.ast.name, g.type])), this.getInhabitatArray().length));

            window.scrollTo(0, document.body.clientHeight);
        }
    }
    getInhabitatArray() {
        return Array.from(document.querySelectorAll<HTMLInputElement>(".inhabitat .wrapper input"));
    }
    unlock(str: string) {
        // switch (str) {
        //     case "fnLP": addTerm([
        //         "#lambda",
        //         "t::P$1:$2,$3 : U",
        //         "c::L$1:$2.$3 : P$1:$2,#typeof $3",
        //     ]); break;
        //     case "applyFn": addTerm([
        //         "#lambda",
        //         "e::(L$1:$2.$3) $4 : #typeof $3",
        //         "p::(L$1:$2.$3) $4 := #replace $3 $1 $4",
        //     ]); break;
        //     case "notFn": addTerm([
        //         "#not",
        //         "d::not:=Lx:U.x->False",
        //     ]); break;
        //     case "Eq": addTerm([
        //         "#eq",
        //         "t::eq : Pa:U,Px:a,Py:a,U",
        //         "c::refl : Pa:U,Px:a,eq a x x",
        //     ]); break;
        //     case "Nat": addTerm([
        //         "#nat",
        //         "t::nat : U",
        //         "c::0 : nat",
        //         "c::succ : Px:nat,nat",
        //     ]); break;
        //     case "Bool": addTerm([
        //         "#Bool",
        //         "t::Bool : U",
        //         "c::0b : Bool",
        //         "c::1b : Bool",
        //     ]); break;
        //     case "indBool": addTerm([
        //         "#Bool",
        //         "e::ind_Bool: PC:Pm:Bool,U,Pc1:C 0b,Pc2:C 1b, Pm:Bool, C m",
        //         "p::ind_Bool $1 $2 $3 0b:=$2",
        //         "p::ind_Bool $1 $2 $3 1b:=$3",
        //     ], "Bool"); break;
        //     case "indTrue": addTerm([
        //         "#True",
        //         "e::ind_True:PC:Pm:True,U,Pc:C true, Pm:True, C m",
        //         "p::ind_True $1 $2 true:=$2",
        //     ], "True"); break;
        //     case "indFalse": addTerm([
        //         "#False",
        //         "e::ind_False: PC:Pm:False,U,Pm:False, C m",
        //     ], "False"); break;
        //     case "simplFn": this.hott.features.add(HoTTFeatures.SimplFnType); break;
        // }
        // this.updateTypeList();
        this.getInhabitatArray().forEach(e => e.onblur({} as any));
    }
}