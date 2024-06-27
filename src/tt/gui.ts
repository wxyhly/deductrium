import { Assist } from "./assist.js";
import { AST, ASTParser } from "./astparser.js";
import { Context, HoTT, HoTTFeatures } from "./check.js";
import { Core } from "./core.js";
const parser = new ASTParser;
const constructors = new Set(["pair", "refl", "true", "0", "0b", "1b", "succ", "inl", "inr", "ua", "funext"]);
const macro = new Set<string>();
const sysmacro = new Set(["add", "pred", "double", "mult", "power", "not"]);
const initialTypeTerms = [
    "#Universe",
    "t::U : U'",
    "c::(#typeof $1) : U",
    "#False",
    "t::False : U",
    "#True",
    "t::True : U",
    "c::true : True",

];
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
function addTerm(list: string[], previnfo?: string) {
    for (const str of list) {
        if (str[0] === "#") { info = str.slice(1); continue; }
        const [prefix, value] = str.split("::");
        const ast = parser.parse(value);
        if (ast.nodes[0].type === "var") consts.add(ast.nodes[0].name);
        if (previnfo) {
            const insertPos = listInfos.map(v => v[1]).lastIndexOf(previnfo) + 1;
            listTerms.splice(insertPos, 0, ast);
            listInfos.splice(insertPos, 0, [prefix, info]);
        } else {
            listTerms.push(ast);
            listInfos.push([prefix, info]);
        }
    }
}
type definedConst = [AST, AST];
export class TTGui {
    onStateChange = () => { };
    hott = new HoTT;
    // gamecore = new HoTTGame;
    typeList = document.getElementById("type-list");
    inhabitList = document.getElementById("inhabit-list");
    mode = null;
    userDefinedConsts: definedConst[] = [];
    sysDefinedConsts: definedConst[] = [];

    constructor() {
        this.sysDefinedConsts = this.hott.beautifys.slice(0);
        addTerm(initialTypeTerms);
        this.updateTypeList();
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
                input.value = this.mode[0].theoremStr;
                this.executeTactic(input);
                for (const m of newmode) {
                    input.value = m;
                    document.getElementById("tactic-begin").click();
                }
                input.value = "";
            }
        });
        document.getElementById("tactic-begin").addEventListener("click", () => {
            const hint = document.getElementById("tactic-hint");
            if (!this.mode) {
                hint.innerText = "请在定理列表中点选待证命题";
                this.mode = "tactic-begin";
            }
            if (this.mode instanceof Array) {
                const statediv = document.getElementById("tactic-state") as HTMLDivElement;
                const val = input.value;
                let assist = this.mode[0] as Assist;
                this.getHottDefCtxt(this.getInhabitatArray().length);
                document.getElementById("tactic-errmsg").innerText = "";
                while (hint.firstChild) hint.removeChild(hint.firstChild);
                try {
                    if (val.startsWith("intros")) {
                        assist.intros(val.slice(6));
                    } else if (val.startsWith("intro")) {
                        assist.intro(val.slice(5));
                    } else if (val.startsWith("apply")) {
                        assist.apply(val.slice(5));
                    } else if (val === "simpl") {
                        assist.simpl();
                    } else if (val.startsWith("destruct")) {
                        assist.destruct(val.slice(8));
                    } else if (val.startsWith("reflexivity")) {
                        assist.reflexivity();
                    } else if (val.startsWith("rewriteBack")) {
                        assist.rewriteBack(val.slice(11));
                    } else if (val.startsWith("rewrite")) {
                        assist.rewrite(val.slice(7));
                    } else if (val.startsWith("qed")) {
                        assist.qed();
                        this.updateInhabitList();
                        const output = this.inhabitList.querySelector(".wrapper:last-of-type input") as HTMLInputElement;
                        output.focus();
                        output.value = this.hott.print(assist.elem) + ":" + assist.theoremStr;
                        output.blur();
                        input.classList.add("hide");
                        document.getElementById("tactic-remove").classList.add("hide");
                        this.mode = null;
                        hint.innerHTML = "";
                        input.value = "";
                        statediv.innerHTML = "";
                        document.getElementById("tactic-autofill").innerHTML = "";
                        return;
                    } else {
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
                const astShow = this.hott.clone({ type: ":", name: "", nodes: [assist.elem, parser.parse(assist.theoremStr)] });
                this.hott.beautify(astShow.nodes[0]);
                hint.appendChild(this.ast2HTML("", astShow, [], Object.fromEntries(assist.goal.map(g => [g.ast.name, g.type])), this.getInhabitatArray().length));

                window.scrollTo(0, document.body.clientHeight);
            }
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
                }
            });
        }
    }
    private updateTacticStateDisplay(assist: Assist, statediv: HTMLDivElement) {
        if (!assist.goal.length) {
            this.addSpan(statediv, "无目标，请输入qed结束");
        }
        let count = 0;
        for (const g of assist.goal) {

            statediv.appendChild(document.createElement("hr"));
            const scope = Object.keys(g.context).map(n => ({ type: "var", name: n } as AST));

            for (const [k, v] of Object.entries(g.context)) {
                const vc = this.hott.clone(v); this.hott.beautify(vc);
                statediv.appendChild(this.ast2HTML("", {
                    type: ":", name: "", nodes: [
                        { type: "var", name: k }, vc]
                }, scope, g.context, this.getInhabitatArray().length));
                statediv.appendChild(document.createElement("br"));
            }
            statediv.appendChild(document.createElement("br"));
            this.addSpan(statediv, count++ ? "目标" + (count - 1) + "：" : "当前目标：");
            const gtypeBeautified = this.hott.clone(g.type);
            this.hott.beautify(gtypeBeautified);
            statediv.appendChild(this.ast2HTML("", gtypeBeautified, scope, g.context, this.getInhabitatArray().length));
            statediv.appendChild(document.createElement("br"));
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
            const el = this.addSpan(varnode, ast.name);
            const scopeStack = scopes.slice(0);
            const astname = ast.name.replace(/'+$/g, "");
            if (astname.match(/^[1-9][0-9]*$/)) {
                el.classList.add("constant");
                el.classList.add("constructors");
            } else if (consts.has(astname.replace(/'+$/, "")) || ast.name.match(/^U'*/) || macro.has(astname.replace(/'+$/, ""))) {
                el.classList.add("constant");
                if (astname.startsWith("ind_")) el.classList.add("ind_fn");
                if (constructors.has(astname)) el.classList.add("constructors");
                if (macro.has(astname)) el.classList.add("macro");
            } else {
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
                case ":": case ":=":
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, " " + ast.type + " ");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    break;
                case "->": case "X": case ",": case "~": case "~=": case "*":
                    this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, ast.type === "X" ? "×" : ast.type === "," ? "," : ast.type === "~" ? "~" : ast.type === "~=" ? "≃" : ast.type === "*" ? "∘" : "→");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    this.addSpan(varnode, ")");
                    break;
                case "apply":
                    this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, " ");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    this.addSpan(varnode, ")");
                    break;
                case "L": case "P": case "S":
                    const outterLayers: HTMLSpanElement[] = [];
                    const newcontext = Object.assign({}, context);
                    const newType = this.hott.clone(ast.nodes[0]); this.hott.unbeautify(newType);
                    newcontext[ast.name] = newType;
                    outterLayers.push(this.addSpan(varnode, "(" + ast.type.replaceAll("S", "Σ").replaceAll("L", "λ").replaceAll("P", "Π")));
                    const varast = this.ast2HTML(idx, { type: "var", name: ast.name }, [{ type: "quantvar", name: "quantvar" }, ...scopes], newcontext, userLineNumber);
                    varast.classList.add("boundedVar");
                    outterLayers.push(varnode.appendChild(varast));
                    outterLayers.push(this.addSpan(varnode, ":"));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    outterLayers.push(this.addSpan(varnode, ast.type === "L" ? "." : ","));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], [ast, ...scopes], newcontext, userLineNumber));
                    outterLayers.push(this.addSpan(varnode, ")"));

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
                for (const node of spans) {
                    node.classList.add("highlighted");
                }
                floatTypeDiv.style.left = (ev.pageX - 4) + "px";
                floatTypeDiv.style.top = (ev.pageY + 30) + "px";
                this.getHottDefCtxt(localNumber);
                let astType = this.hott.clone(ast);
                this.hott.unbeautify(astType);

                floatTypeDiv.style.display = "block";
                try {
                    astType = new Core().check(astType, localCtxt) as AST;
                    // astType = this.hott.check(astType, localCtxt);
                    // console.log(localCtxt);
                    this.hott.beautify(astType, true);
                } catch (e) {
                    astType = { name: "", type: "" };
                    floatTypeDiv.style.display = "none";
                }
                if (scopes[0]?.type === "quantvar") {
                    scopes = scopes.slice(1);
                }
                try { floatTypeDiv.appendChild(this.ast2HTML("", astType, scopes, localCtxt, userLineNumber)); } catch (e) {
                    floatTypeDiv.innerText = e;
                }
            });
            node.addEventListener('mouseout', ev => {
                for (const node of spans) {
                    node.classList.remove("highlighted");
                }
                floatTypeDiv.style.display = "none";
                floatTypeDiv.innerHTML = "";
            });
        }
        return varnode;
    }
    updateTypeList() {

        let idx = 0;
        this.updateGuiList("", listTerms.map((ast, idx) => {
            const prefix = listInfos[idx][0];
            this.hott.beautify(ast, false);
            return ast;
        }), this.typeList, (p, idx) => true, (p, itInfo, it) => {
            itInfo[0].innerHTML = listInfos[idx++][1];
        }, true, listTerms.map((ast, idx) => {
            const prefix = listInfos[idx][0];
            return prefix === "t" ? "type" : prefix === "c" ? "cons" : prefix === "e" ? "elim" : prefix === "p" ? "comp" : prefix === "d" ? "def" : "??";
        }));
    }
    getHottDefCtxt(input: HTMLInputElement | number) {
        macro.clear();
        for (const s of sysmacro) macro.add(s);
        this.hott.beautifys = this.sysDefinedConsts.slice(0);
        if (typeof input === "number") {
            for (let i = 0; i <= input; i++) {
                const def = this.userDefinedConsts[i];
                if (!def) continue;
                macro.add(def[0].name);
                if (i !== input) this.hott.beautifys.push(def);
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
            this.hott.beautifys.push(def);
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
            let astexpd: AST;
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

            this.hott.startTimer();
            let type: AST;
            if (ast) {
                try {
                    astexpd = this.hott.parse(input.value);
                    if (astexpd.type === ":") {
                        this.hott.checkProof(astexpd.nodes[0], astexpd.nodes[1]);
                    } else if (astexpd.type === ":=") {
                        if (astexpd.nodes[0].type !== "var") {
                            throw ":=符号左侧仅允许出现自定义常量";
                        }
                        let redefined: boolean = true;
                        const defname = input.value.split(":=")[0].trim();
                        try {
                            this.hott.check(this.hott.parse(defname));
                        } catch (e) {
                            if (e === "由于系统性能问题，递归大数字超时") throw e;
                            redefined = false;
                        }
                        if (redefined) throw defname + "的定义重复";
                        this.hott.check(astexpd.nodes[1]);
                        macro.add(defname);
                        this.userDefinedConsts[currentIdx] = [astexpd.nodes[0], astexpd.nodes[1]];
                    } else {
                        type = this.hott.check(astexpd);
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
                    this.hott.beautify(type);
                    div.appendChild(this.ast2HTML("", type, [], {}, currentIdx));
                }
            }
            this.hott.stopTimer();

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
        const ref = this.hott.parse(typeStr);
        for (const e of this.getInhabitatArray()) {
            if (!e.classList.contains("hide")) {
                e.onblur({} as any);
            }
            if (e.parentElement.classList.contains("error")) continue;
            let ast: AST;
            try {
                ast = parser.parse(e.value);
            } catch (e) {
                continue;
            }
            if (!ast) continue;
            try {
                ast = this.hott.parse(e.value);
                if (ast.type === ":") {
                    if (this.hott.equal(ast.nodes[1], ref, {})) return true;
                } else {
                    if (this.hott.equal(this.hott.check(ast), ref, {})) return true;
                }
            } catch (e) {
                continue;
            }
        }
        return false;
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
            const ast = this.hott.parse(inputDom.value);
            if (!ast) throw "空表达式";
            const type = this.hott.check(ast);
            if (type.name[0] !== "U") throw "不是命题类型";
            const assist = new Assist(this.hott, inputDom.value);
            this.mode = [assist];
            this.autofillTactics(assist);
            document.getElementById("tactic-remove").classList.remove("hide");
            document.getElementById("tactic-hint").innerText = "";
            document.getElementById("tactic-hint").appendChild(this.ast2HTML("",
                { type: ":", name: "", nodes: [assist.elem, parser.parse(inputDom.value)] }, [], Object.fromEntries(assist.goal.map(g => [g.ast.name, g.type])), this.getInhabitatArray().length));
            document.getElementById("tactic-input").classList.remove("hide");
            document.getElementById("tactic-input").focus();
            this.updateTacticStateDisplay(assist, document.getElementById("tactic-state") as HTMLDivElement);
            window.scrollTo(0, document.body.clientHeight);

        } catch (e) {
            document.getElementById("tactic-hint").innerText = "命题格式有误：" + e;
            this.mode = null;
        }
    }
    getInhabitatArray() {
        return Array.from(document.querySelectorAll<HTMLInputElement>(".inhabitat .wrapper input"));
    }
    unlock(str: string) {
        switch (str) {
            case "fnLP": addTerm([
                "#lambda",
                "t::P$1:$2,$3 : U",
                "c::L$1:$2.$3 : P$1:$2,#typeof $3",
            ]); break;
            case "applyFn": addTerm([
                "#lambda",
                "e::(L$1:$2.$3) $4 : #typeof $3",
                "p::(L$1:$2.$3) $4 := #replace $3 $1 $4",
            ]); break;
            case "notFn": addTerm([
                "#not",
                "d::not:=Lx:U.x->False",
            ]); break;
            case "Eq": addTerm([
                "#eq",
                "t::eq : Pa:U,Px:a,Py:a,U",
                "c::refl : Pa:U,Px:a,eq a x x",
            ]); break;
            case "Nat": addTerm([
                "#nat",
                "t::nat : U",
                "c::0 : nat",
                "c::succ : Px:nat,nat",
            ]); break;
            case "Bool": addTerm([
                "#Bool",
                "t::Bool : U",
                "c::0b : Bool",
                "c::1b : Bool",
            ]); break;
            case "indBool": addTerm([
                "#Bool",
                "e::ind_Bool: PC:Pm:Bool,U,Pc1:C 0b,Pc2:C 1b, Pm:Bool, C m",
                "p::ind_Bool $1 $2 $3 0b:=$2",
                "p::ind_Bool $1 $2 $3 1b:=$3",
            ], "Bool"); break;
            case "indTrue": addTerm([
                "#True",
                "e::ind_True:PC:Pm:True,U,Pc:C true, Pm:True, C m",
                "p::ind_True $1 $2 true:=$2",
            ], "True"); break;
            case "indFalse": addTerm([
                "#False",
                "e::ind_False: PC:Pm:False,U,Pm:False, C m",
            ], "False"); break;
            case "simplFn": this.hott.features.add(HoTTFeatures.SimplFnType); break;
        }
        this.updateTypeList();
        this.getInhabitatArray().forEach(e => e.onblur({} as any));
    }
}