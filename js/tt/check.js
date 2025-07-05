import { TR } from "../lang.js";
import { ASTParser } from "./astparser.js";
const axiomstrs = {
    "pair": "Pa:U,Pb:(Px:a,U),Px:a,Py:b x,Sx:a,b x",
    "ind_pair": "Pa:U,Pb:(Px:a,U),PC:Pm:Sx:a,b x,U, Pc:Px:a,Py:b x,C (pair a b x y), Pm:Sx:a,b x, C m",
    "eq": "Pa:U,Px:a,Py:a,U",
    "refl": "Pa:U,Px:a,eq a x x",
    "ind_eq": "Pa:U, PC:(Px:a,Py:a,Pm:eq a x y,U),Pc:Px:a,C x x (refl a x), Px:a,Py:a, Pm:eq a x y, C x y m",
    "True": "U",
    "true": "True",
    "ind_True": "PC:Pm:True,U,Pc:C true, Pm:True, C m",
    "Bool": "U",
    "0b": "Bool",
    "1b": "Bool",
    "ind_Bool": "PC:Pm:Bool,U,Pc1:C 0b,Pc2:C 1b, Pm:Bool, C m",
    "False": "U",
    "ind_False": "PC:Pm:False,U, Pm:False, C m",
    "nat": "U",
    "0": "nat",
    "succ": "Px:nat,nat",
    "ind_nat": "PC:Px:nat,U,Pc0:C 0,Pcs:(Px:nat,Py:C x,C (succ x)),Px:nat,C x",
    "union": "Pa:U,Pb:U,U",
    "inl": "Pa:U,Pb:U,Px:a,union a b",
    "inr": "Pa:U,Pb:U,Px:b,union a b",
    "ind_union": "Pa:U,Pb:U,PQ:Px:union a b,U,Pc1:Px:a,Q (inl a b x),Pc2:Px:b,Q (inr a b x),Px:union a b,Q x",
    "ua": "Pa:U,Pb:U,Px:a~=b,eq' U a b",
    "funext": "Pa:U,Pp:Px:a,U,Pf:Px:a,p x,Pg:Px:a,p x,Py:(Px:a,eq (p x) (f x) (g x)),(eq (Px:a,p x) f g)",
};
const definitionstrs = {
    "not $1": "Pn:$1,False",
    "ind_nat $1 $2 $3 0": "$2",
    "ind_nat $1 $2 $3 (succ $4)": "$3 $4 (ind_nat $1 $2 $3 $4)",
    "ind_eq $1 $2 $3 $4 $4 (refl $1 $4)": "$3 $4",
    "ind_True $1 $2 true": "$2",
    "ind_Bool $1 $2 $3 0b": "$2",
    "ind_Bool $1 $2 $3 1b": "$3",
    "ind_pair $1 $2 $3 $4 ($5, $6)": "$4 $5 $6",
    "ind_pair $1 $2 $3 $4 (pair $1 $2 $5 $6)": "$4 $5 $6",
    "ind_union $1 $2 $3 $4 $5 (inl $1 $2 $6)": "$4 $6",
    "ind_union $1 $2 $3 $4 $5 (inr $1 $2 $6)": "$5 $6",
};
const beautify = {
    "add": "ind_nat (Lx:nat.Py:nat,nat) (Lx:nat.x) Lx':nat.Lx:Py:nat,nat.Ly:nat.succ (x y)",
    "double": "ind_nat (Lx:nat.nat) 0 Lx':nat.Lx:nat.succ (succ x)",
    "mult": "ind_nat (Lx:nat.Py:nat,nat) (Lx:nat.0) Lx':nat.Lx:Py:nat,nat.Ly:nat.add (x y) y",
    "power": "Lx:nat.Ly:nat.(ind_nat (Lx:nat.Py:nat,nat) (Lx:nat.1) Lx':nat.Lx:Py:nat,nat.Ly:nat.mult (x y) y)y x",
    "pred": "ind_nat (Lx:nat.nat) 0 Lx':nat.Lx:nat.x'",
    "not": "Lx:U.Pa:x,False"
};
const parser = new ASTParser();
const axioms = {};
for (const [k, v] of Object.entries(axiomstrs)) {
    axioms[k] = parser.parse(v);
}
const definitions = [];
for (const [k, v] of Object.entries(definitionstrs)) {
    definitions.push([parser.parse(k), parser.parse(v)]);
}
const beautifys = [];
for (const [k, v] of Object.entries(beautify)) {
    beautifys.push([parser.parse(k), parser.parse(v)]);
}
export var HoTTFeatures;
(function (HoTTFeatures) {
    HoTTFeatures[HoTTFeatures["Fn"] = 0] = "Fn";
    HoTTFeatures[HoTTFeatures["SimplFnType"] = 1] = "SimplFnType";
    HoTTFeatures[HoTTFeatures["NegSym"] = 2] = "NegSym";
    HoTTFeatures[HoTTFeatures["SimplEq"] = 3] = "SimplEq";
})(HoTTFeatures || (HoTTFeatures = {}));
export class HoTT {
    features = new Set;
    axioms = axioms;
    definitions = definitions;
    beautifys = beautifys;
    beginTime;
    beginTimeFlag;
    startTimer() {
        this.beginTimeFlag = 0;
        this.beginTime = new Date().getTime();
    }
    stopTimer() {
        this.beginTimeFlag = null;
        this.beginTime = null;
    }
    getFreeVars(ast, res = new Set, scope = []) {
        if (ast.type === "var" && !scope.includes(ast.name)) {
            res.add(ast.name);
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            this.getFreeVars(ast.nodes[0], res, scope);
            this.getFreeVars(ast.nodes[1], res, [ast.name, ...scope]);
        }
        else if (ast.type === "apply" || ast.type === "->" || ast.type === "X" || ast.type === "," || ast.type === "~" || ast.type === "~=") {
            this.getFreeVars(ast.nodes[0], res, scope);
            this.getFreeVars(ast.nodes[1], res, scope);
        }
        return res;
    }
    getNewName(refName, excludeSet) {
        let n = refName + "'";
        while (excludeSet.has(n)) {
            n += "'";
        }
        return n;
    }
    replaceVar(ast, name, dst, fvDst = this.getFreeVars(dst)) {
        if (ast.type === "var") {
            if (ast.name !== name)
                return;
            this.assign(ast, dst);
        }
        else if (ast.type === "apply" || ast.type === "->" || ast.type === "X" || ast.type === "," || ast.type === "~" || ast.type === "~=") {
            this.replaceVar(ast.nodes[0], name, dst, fvDst);
            this.replaceVar(ast.nodes[1], name, dst, fvDst);
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            this.replaceVar(ast.nodes[0], name, dst, fvDst);
            if (ast.name === name)
                return; // bounded
            const fvSrcBody = this.getFreeVars(ast.nodes[1]);
            if (!fvSrcBody.has(name))
                return; // not bounded, but not found
            if (!fvDst.has(ast.name))
                this.replaceVar(ast.nodes[1], name, dst, fvDst);
            else {
                const newName = this.getNewName(ast.name, new Set([...fvSrcBody, ...fvDst]));
                this.replaceVar(ast.nodes[1], ast.name, { type: "var", name: newName }, fvDst);
                this.replaceVar(ast.nodes[1], name, dst, fvDst);
                ast.name = newName;
            }
            return;
        }
    }
    clone(ast) {
        const newast = {
            type: ast.type, name: ast.name
        };
        if (ast.nodes) {
            newast.nodes = ast.nodes.map(p => this.clone(p));
        }
        return newast;
    }
    assign(ast, value) {
        const v = this.clone(value);
        ast.type = v.type;
        ast.name = v.name;
        ast.nodes = v.nodes;
    }
    exactEqual(ast1, ast2) {
        if (ast1 === ast2)
            return true;
        if (ast1.type !== ast2.type)
            return false;
        if (ast1.name !== ast2.name)
            return false;
        if (ast1.nodes?.length !== ast2.nodes?.length)
            return false;
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.exactEqual(ast1.nodes[i], ast2.nodes[i]))
                    return false;
            }
        }
        return true;
    }
    checkProof(witness, theorem, context = {}) {
        const t = this.check(witness);
        if (this.equal(t, theorem, context)) {
            this.expandDefinition(t, context);
            return t;
        }
        ;
        throw TR("类型断言失败：“:” 左边表达式类型为") + this.print(t);
    }
    isNatLiteral(ast) {
        return ast.type === "var" && (ast.name === "0" && ast.name.match(/^[1-9][0-9]*$/));
    }
    predNatLiteral(num) {
        if (num === "0")
            throw "0 has no predicator";
        if (!num.endsWith("0")) {
            return num.slice(0, -1) + "0012345678"[num[num.length - 1]];
        }
        return (this.predNatLiteral(num.slice(0, -1)) + "9").replace(/^0+/, "");
    }
    succNatLiteral(num) {
        if (!num.endsWith("9")) {
            return num.slice(0, -1) + "1234567890"[num[num.length - 1]];
        }
        return this.succNatLiteral(num.slice(0, -1) || "0") + "0";
    }
    equal(ast1, ast2, context) {
        if (ast1 === ast2)
            return true;
        if (this.exactEqual(ast1, ast2))
            return true;
        ast1 = this.clone(ast1);
        this.expandDefinition(ast1, context);
        ast2 = this.clone(ast2);
        this.expandDefinition(ast2, context);
        // if (this.isNatLiteral(ast1) && ast2.type === "apply" && ast2.nodes[0].name === "succ") {
        //     return this.equal(this.predNatLiteral(ast1.name), ast2.nodes[1], context);
        // } else if (this.isNatLiteral(ast2) && ast1.type === "apply" && ast1.nodes[0].name === "succ") {
        //     return this.equal(this.predNatLiteral(ast2.name), ast1.nodes[1], context);
        // }
        if (ast1.type === "~=") {
            ast1 = this.expandEquivalence(ast1, context);
        }
        if (ast2.type === "~=") {
            ast2 = this.expandEquivalence(ast2, context);
        }
        if (ast1.type === "~") {
            ast1 = this.expandHomotopy(ast1, context);
        }
        if (ast2.type === "~") {
            ast2 = this.expandHomotopy(ast2, context);
        }
        if (ast1.type !== ast2.type)
            return false;
        if ((ast1.type === "L" || ast1.type === "S" || ast1.type === "P") && ast1.name !== ast2.name) {
            // try alpha conversion
            this.replaceVar(ast2.nodes[1], ast2.name, { type: "var", name: ast1.name });
            ast2.name = ast1.name;
        }
        if (ast1.name !== ast2.name)
            return false;
        if (ast1.nodes?.length !== ast2.nodes?.length)
            return false;
        const ctxt = Object.assign({}, context);
        if (ast1.type === "L" || ast1.type === "P" || ast1.type === "S") {
            ctxt[ast1.name] = ast1.nodes[0];
        }
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.equal(ast1.nodes[i], ast2.nodes[i], i ? ctxt : context))
                    return false;
            }
        }
        return true;
    }
    expandDefinition(ast, context) {
        // this.check(ast, context); // prevent ill typed ast
        let modified = false;
        if (ast.type === "var")
            return false;
        let submodified = false;
        do {
            submodified = this.expandOperatorNatLiteral(ast);
            modified ||= submodified;
        } while (submodified);
        // expand nondependent pair
        if (ast.type === ",") {
            const name1 = this.getNewName("x", this.getFreeVars(ast));
            const typeA = this.check(ast.nodes[0], context);
            const typeB = this.check(ast.nodes[1], context);
            modified = true;
            this.assign(ast, {
                type: "apply", name: "", nodes: [{
                        type: "apply", name: "", nodes: [{
                                type: "apply", name: "", nodes: [{
                                        type: "apply", name: "", nodes: [{
                                                type: "var", name: "pair"
                                            }, typeA]
                                    },
                                    { type: "L", name: name1, nodes: [typeA, typeB] },
                                ]
                            }, ast.nodes[0]]
                    }, ast.nodes[1]]
            });
        }
        // first expand fns by definitions
        for (const [k, v] of definitions) {
            const res = this.match(ast, k);
            if (!res)
                continue;
            const replaced = this.clone(v);
            this.replaceByMatch(replaced, res);
            this.assign(ast, replaced);
            modified = true;
        }
        modified = this.expandIndNatLiteral(ast);
        if (!ast.nodes?.length)
            return modified;
        const ctxt = Object.assign({}, context);
        if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            // cancel dangerous loop quote by alpha conversion
            const newVarname = this.getNewName(ast.name, new Set(Object.keys(ctxt)));
            ctxt[newVarname] = ctxt[ast.name];
            const newtype = this.clone(ast.nodes[0]);
            this.replaceVar(newtype, ast.name, { type: "var", name: newVarname });
            ctxt[ast.name] = newtype;
            modified ||= this.expandDefinition(ast.nodes[0], context);
            modified ||= this.expandDefinition(ast.nodes[1], ctxt);
        }
        else {
            for (const n of ast.nodes)
                modified ||= this.expandDefinition(n, ctxt);
        }
        while (ast.type === "apply") {
            const t1 = this.check(ast.nodes[0], context);
            if (t1.type !== "P")
                throw TR("非函数尝试作用");
            const t2 = this.check(ast.nodes[1], context);
            if (!this.equal(t2, t1.nodes[0], context))
                throw TR("函数与作用目标类型不匹配：函数") + this.print(ast.nodes[0]) + TR("需要接受的参数类型为") + this.print(t1.nodes[0]) + TR("，作用对象") + this.print(ast.nodes[1]) + TR("类型为") + this.print(t2);
            if (ast.nodes[0].type === "L") {
                const nt1 = this.clone(ast.nodes[0].nodes[1]);
                this.replaceVar(nt1, ast.nodes[0].name, ast.nodes[1]);
                this.assign(ast, nt1);
                modified = true;
            }
            else {
                break;
            }
        }
        if (modified) {
            this.expandDefinition(ast, context);
        }
        return modified;
    }
    match(ast, pattern, res = {}) {
        if (pattern.type === "var" && pattern.name.match(/^\$/)) {
            res[pattern.name] ??= ast;
            if (!this.exactEqual(ast, res[pattern.name]))
                return null;
            return res;
        }
        if (ast.type !== pattern.type)
            return null;
        if (ast.name && ast.name !== pattern.name) {
            if (pattern.name.padEnd(ast.name.length, "'") !== ast.name)
                return null;
            res[".U"] = { type: "note", name: (ast.name.length - pattern.name.length).toString() };
        }
        if (ast.nodes?.length !== pattern.nodes?.length)
            return null;
        if (ast.nodes?.length) {
            for (let i = 0; i < ast.nodes.length; i++) {
                if (!this.match(ast.nodes[i], pattern.nodes[i], res))
                    return null;
            }
        }
        return res;
    }
    replaceByMatch(ast, res) {
        if (!res)
            throw TR("未匹配");
        if (ast.type === "var" && axioms[ast.name]) {
            const levels = Number(res[".U"]?.name);
            if (levels)
                ast.name = ast.name.padEnd(levels + ast.name.length, "'");
        }
        else if (ast.type === "var" && ast.name.match(/^\$/)) {
            if (!res[ast.name])
                return;
            this.assign(ast, this.clone(res[ast.name]));
            // this.assign(ast, this.levelUp(this.clone(res[ast.name]), Number(res[".U"]?.name)));
        }
        else if (ast.nodes?.length) {
            for (const n of ast.nodes) {
                this.replaceByMatch(n, res);
            }
        }
    }
    mergeUniverse(us) {
        let l = 1;
        for (const u of us) {
            if (u.type !== "var" || u.name[0] !== "U")
                throw TR("意外出现非全类：") + this.print(u);
            l = Math.max(l, u.name.length);
        }
        return { type: "var", name: "U".padEnd(l, "'") };
    }
    check(ast, context = {}) {
        if (this.beginTime && this.beginTimeFlag++ === 0xFF) {
            if (new Date().getTime() - this.beginTime > 1000) {
                throw TR("由于系统性能问题，递归大数字超时");
            }
            this.beginTimeFlag = 0;
        }
        if (ast.type === "var") {
            // Universe
            const jeg = ast.name.match(/^U('*)$/);
            if (jeg) {
                return { type: "var", name: jeg[0] + "'" };
            }
            // natural number
            if (ast.name.match(/^[1-9][0-9]*$/)) {
                return { type: "var", name: "nat" };
            }
            // hypotheses and axioms
            let varType = context[ast.name];
            if (varType)
                return this.clone(varType);
            let astname = ast.name;
            let level = 1;
            while (astname.endsWith("'")) {
                astname = astname.slice(0, -1);
                level++;
            }
            varType = axioms[astname];
            if (varType) {
                const clonet = this.clone(varType);
                this.replaceVar(clonet, "U", { type: "var", name: "U".padEnd(level, "'") });
                this.replaceVar(clonet, "eq", { type: "var", name: "eq".padEnd(level + 1, "'") });
                this.replaceVar(clonet, "pair", { type: "var", name: "pair".padEnd(level + 3, "'") });
                this.replaceVar(clonet, "union", { type: "var", name: "union".padEnd(level + 4, "'") });
                return clonet;
            }
            throw TR("未知的变量：") + ast.name;
        }
        if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            const domain = this.check(ast.nodes[0], context);
            const ctxt = Object.assign({}, context);
            if (this.getFreeVars(ast.nodes[0]).has(ast.name)) {
                // cancel dangerous loop quote by alpha conversion
                const newVarname = this.getNewName(ast.name, new Set(Object.keys(ctxt)));
                ctxt[newVarname] = ctxt[ast.name];
                const newtype = this.clone(ast.nodes[0]);
                this.replaceVar(newtype, ast.name, { type: "var", name: newVarname });
                ctxt[ast.name] = newtype;
            }
            ctxt[ast.name] = ast.nodes[0];
            // A:U,T:A->U, Lx:A.y:Tx : Px:A.Tx
            const ucodomain = this.check(ast.nodes[1], ctxt);
            if (ast.type === "P" || ast.type === "S") {
                return this.mergeUniverse([domain, ucodomain]);
            }
            const lt = { type: "P", name: ast.name, nodes: [ast.nodes[0], ucodomain] };
            return lt; // L
        }
        if (ast.type === "apply") {
            const t1 = this.check(ast.nodes[0], context);
            if (t1.type !== "P")
                throw TR("非函数尝试作用");
            const t2 = this.check(ast.nodes[1], context);
            if (!this.equal(t2, t1.nodes[0], context))
                throw TR("函数与作用目标类型不匹配：函数") + parser.stringify(ast.nodes[0]) + TR("需要接受的参数类型为") + parser.stringify(t1.nodes[0]) + TR("，作用对象") + parser.stringify(ast.nodes[1]) + TR("类型为") + parser.stringify(t2);
            const nt1 = this.clone(t1.nodes[1]);
            this.replaceVar(nt1, t1.name, ast.nodes[1]);
            this.expandDefinition(nt1, context);
            return nt1;
        }
        if (ast.type === ",") {
            const name1 = this.getNewName("x", this.getFreeVars(ast));
            const typeA = this.check(ast.nodes[0], context);
            const typeB = this.check(ast.nodes[1], context);
            const expanded = {
                type: "apply", name: "", nodes: [{
                        type: "apply", name: "", nodes: [{
                                type: "apply", name: "", nodes: [{
                                        type: "apply", name: "", nodes: [{
                                                type: "var", name: "pair"
                                            }, typeA]
                                    },
                                    { type: "L", name: name1, nodes: [typeA, typeB] },
                                ]
                            }, ast.nodes[0]]
                    }, ast.nodes[1]]
            };
            return this.check(expanded);
        }
        if (ast.type === "~=") {
            return this.check(this.expandEquivalence(ast, context), context);
        }
        if (ast.type === "~") {
            return this.check(this.expandHomotopy(ast, context), context);
        }
        if (ast.type === "*") {
            return this.check(this.expandComposite(ast, context), context);
        }
        throw TR("未知的语法树");
    }
    expandHomotopy(ast, context) {
        const typeA = this.check(ast.nodes[0], context);
        const typeB = this.check(ast.nodes[1], context);
        if (!this.equal(typeA, typeB, context))
            throw "同伦关系符“~”两边类型不相等";
        if (typeA.type !== "P")
            throw "同伦关系符“~”仅能对函数作用";
        const name = this.getNewName("x", this.getFreeVars(ast));
        const fx = { type: "apply", name: "", nodes: [ast.nodes[0], { type: "var", name }] };
        const gx = { type: "apply", name: "", nodes: [ast.nodes[1], { type: "var", name }] };
        const ctxt = Object.assign({}, context);
        ctxt[name] = typeA.nodes[0];
        const targetType = this.check(fx, ctxt);
        const us = "'".repeat(this.check(targetType, ctxt).name.length - 1);
        const expanded = {
            type: "P", name, nodes: [
                typeA.nodes[0], {
                    type: "apply", name: "", nodes: [{
                            type: "apply", name: "", nodes: [{
                                    type: "apply", name: "", nodes: [{
                                            type: "var", name: "eq" + us
                                        }, targetType]
                                }, fx]
                        }, gx]
                }
            ]
        };
        return expanded;
    }
    expandEquivalence(ast, context) {
        const nameF = this.getNewName("f", this.getFreeVars(ast));
        const nameG = this.getNewName("g", this.getFreeVars(ast));
        const nameH = this.getNewName("h", this.getFreeVars(ast));
        const _name = this.getNewName("x", this.getFreeVars(ast));
        const fType = { type: "P", name: _name, nodes: ast.nodes };
        const ghType = { type: "P", name: _name, nodes: [ast.nodes[1], ast.nodes[0]] };
        const ctxt = Object.assign({}, context);
        ctxt[nameF] = fType;
        ctxt[nameG] = ghType;
        ctxt[nameH] = ghType;
        const f_g = {
            type: "L", name: _name, nodes: [ast.nodes[1], {
                    type: "apply", name: "", nodes: [
                        { type: "var", name: nameF },
                        { type: "apply", name: "", nodes: [{ type: "var", name: nameG }, { type: "var", name: _name }] }
                    ]
                }]
        };
        const h_f = {
            type: "L", name: _name, nodes: [ast.nodes[0], {
                    type: "apply", name: "", nodes: [
                        { type: "var", name: nameH },
                        { type: "apply", name: "", nodes: [{ type: "var", name: nameF }, { type: "var", name: _name }] }
                    ]
                }]
        };
        const idA = { type: "L", name: _name, nodes: [ast.nodes[0], { type: "var", name: _name }] };
        const idB = { type: "L", name: _name, nodes: [ast.nodes[1], { type: "var", name: _name }] };
        const f_gIsIdB = this.expandHomotopy({ type: "~", name: "", nodes: [f_g, idB] }, ctxt);
        const h_fIsIdA = this.expandHomotopy({ type: "~", name: "", nodes: [h_f, idA] }, ctxt);
        const expanded = {
            type: "S", name: nameF, nodes: [
                fType, {
                    type: "S", name: _name, nodes: [{
                            type: "S", name: nameG, nodes: [ghType, f_gIsIdB]
                        }, {
                            type: "S", name: nameH, nodes: [ghType, h_fIsIdA]
                        },]
                }
            ]
        };
        return expanded;
    }
    expandComposite(ast, context) {
        const [f, g] = ast.nodes;
        const tf = this.check(f, context);
        const tg = this.check(g, context);
        if (tf.type === "P" && tg.type === "P") {
            const nameX = this.getNewName("x", this.getFreeVars(ast));
            const expanded = {
                type: "L", name: nameX,
                nodes: [
                    g.nodes[0], {
                        type: "apply", name: "", nodes: [
                            f, {
                                type: "apply", name: "", nodes: [
                                    g, { type: "var", name: nameX }
                                ]
                            }
                        ]
                    }
                ]
            };
            return expanded;
        }
    }
    print(ast) {
        const cast = this.clone(ast);
        try {
            this.expandDefinition(cast, {});
        }
        catch (e) {
            this.assign(cast, ast);
        }
        this.beautify(cast);
        return parser.stringify(cast);
    }
    parse(aststr) {
        const ast = parser.parse(aststr);
        if (!ast)
            throw TR("意外的空表达式");
        this.unbeautify(ast);
        return ast;
    }
    beautify(ast, shrinkDef = true) {
        let modified = false;
        if (shrinkDef) {
            for (const [k, v] of this.beautifys) {
                const res = this.match(ast, v);
                if (!res)
                    continue;
                modified = true;
                const replaced = this.clone(k);
                this.replaceByMatch(replaced, res);
                this.assign(ast, replaced);
            }
        }
        if (ast.type === "P" && !this.getFreeVars(ast.nodes[1]).has(ast.name) && this.features.has(HoTTFeatures.SimplFnType)) {
            modified = true;
            ast.type = "->";
            ast.name = "";
        }
        if (ast.type === "S" && !this.getFreeVars(ast.nodes[1]).has(ast.name)) {
            modified = true;
            ast.type = "X";
            ast.name = "";
        }
        if (!ast.nodes?.length)
            return modified;
        for (const n of ast.nodes)
            if (this.beautify(n, shrinkDef))
                modified = true;
        this.normalizeNatLiteral(ast);
        if (modified) {
            this.beautify(ast, shrinkDef);
        }
        return modified;
    }
    unbeautify(ast) {
        let modified = false;
        let submodified = false;
        do {
            submodified = this.expandOperatorNatLiteral(ast);
            modified ||= submodified;
        } while (submodified);
        if (ast.type === "->") {
            modified = true;
            ast.type = "P";
            ast.name = this.getNewName("x", this.getFreeVars(ast));
        }
        if (ast.type === "X") {
            modified = true;
            ast.type = "S";
            ast.name = this.getNewName("x", this.getFreeVars(ast));
        }
        for (const [k, v] of this.beautifys) {
            const res = this.match(ast, k);
            if (!res)
                continue;
            modified = true;
            const replaced = this.clone(v);
            this.replaceByMatch(replaced, res);
            this.assign(ast, replaced);
        }
        if (!ast.nodes?.length)
            return modified;
        for (const n of ast.nodes)
            if (this.unbeautify(n))
                modified = true;
        this.normalizeNatLiteral(ast);
        if (modified) {
            this.unbeautify(ast);
        }
        return modified;
    }
    normalizeNatLiteral(ast) {
        if (ast.type === "apply" && ast.nodes[0].name === "succ") {
            this.normalizeNatLiteral(ast.nodes[1]);
            if (this.isNatLiteral(ast.nodes[1]) || ast.nodes[1].name === "0") {
                this.assign(ast, { type: "var", name: this.succNatLiteral(ast.nodes[1].name) });
            }
        }
        else if (ast.nodes) {
            for (const n of ast.nodes)
                this.normalizeNatLiteral(n);
        }
        return ast;
    }
    expandIndNatLiteral(ast) {
        let modified = false;
        if (ast.type === "apply" && this.isNatLiteral(ast.nodes[1])) {
            if (ast.nodes[0].type === "apply" && ast.nodes[0].nodes[0].type === "apply" && ast.nodes[0].nodes[0].nodes[0].type === "apply") {
                if (ast.nodes[0].nodes[0].nodes[0].nodes[0].name.match(/^ind_nat'*$/)) {
                    modified = true;
                    const recursive = this.clone(ast);
                    const predNum = { type: "var", name: this.predNatLiteral(ast.nodes[1].name) };
                    this.assign(recursive.nodes[1], predNum);
                    this.assign(ast, {
                        type: "apply", name: "", nodes: [
                            {
                                type: "apply", name: "", nodes: [
                                    ast.nodes[0].nodes[1], predNum
                                ]
                            }, recursive
                        ]
                    });
                }
            }
            else if (ast.nodes) {
                for (const n of ast.nodes)
                    modified ||= this.expandIndNatLiteral(n);
            }
            return modified;
        }
    }
    addNatLiteral(n1, n2) {
        if (Number(n1) + Number(n2) < Number.MAX_SAFE_INTEGER) {
            return (Number(n1) + Number(n2)).toString();
        }
        throw TR("整数太大超过表示上限");
    }
    mulNatLiteral(n1, n2) {
        if (Number(n1) * Number(n2) < Number.MAX_SAFE_INTEGER) {
            return (Number(n1) * Number(n2)).toString();
        }
        throw TR("整数太大超过表示上限");
    }
    powNatLiteral(n1, n2) {
        const res = Math.pow(Number(n1), Number(n2));
        if (res < Number.MAX_SAFE_INTEGER) {
            return res.toString();
        }
        throw TR("整数太大超过表示上限");
    }
    expandOperatorNatLiteral(ast) {
        let modified = false;
        if (ast.type === "apply" && this.isNatLiteral(ast.nodes[1])) {
            if (ast.nodes[0].type === "apply" && this.isNatLiteral(ast.nodes[0].nodes[1])) {
                const operator = ast.nodes[0].nodes[0].name;
                if (operator === "add") {
                    modified = true;
                    this.assign(ast, { type: "var", name: this.addNatLiteral(ast.nodes[1].name, ast.nodes[0].nodes[1].name) });
                }
                if (operator === "mult") {
                    modified = true;
                    this.assign(ast, { type: "var", name: this.mulNatLiteral(ast.nodes[1].name, ast.nodes[0].nodes[1].name) });
                }
                if (operator === "power") {
                    modified = true;
                    this.assign(ast, { type: "var", name: this.powNatLiteral(ast.nodes[1].name, ast.nodes[0].nodes[1].name) });
                }
            }
            else if (ast.nodes[0].name === "double") {
                modified = true;
                this.assign(ast, { type: "var", name: this.mulNatLiteral(ast.nodes[1].name, "2") });
            }
        }
        else if (ast.nodes) {
            for (const n of ast.nodes)
                modified ||= this.expandOperatorNatLiteral(n);
        }
        return modified;
    }
}
//# sourceMappingURL=check.js.map