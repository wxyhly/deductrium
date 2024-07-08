import { AST, ASTParser } from "./astparser.js";
const parser = new ASTParser;
export type TypeRule = { prefix: string, inferMode: string, ast: AST, id: string, postfix: string };
export function initTypeSystem() {
    let typeName: string;
    let localId: { [key: string]: number } = {};
    const ruleList: TypeRule[] = [];
    function addRule(postfix: string, astStr: string) {
        const ast = parser.parse(astStr);
        let inferMode = "";
        if (postfix[0] === "@" || postfix[0] === "_") {
            inferMode = postfix[0];
            postfix = postfix.slice(1);
        }
        localId[typeName] ??= 0;
        ruleList.push({ prefix: typeName, ast, id: typeName + (localId[typeName]++), postfix, inferMode });
    }

    typeName = "True";
    addRule("类型", "True:U");
    addRule("构造", "true:True");
    addRule("@解构", "@ind_True : Pu:U@,PC:True->Uu,Pc:C true,Px:True,C x");
    addRule("@解构", "ind_True := @ind_True _");
    addRule("_解构", "ind_True");
    addRule("计算", "ind_True ?C ?ctrue true === ?ctrue");

    typeName = "False";
    addRule("类型", "False:U");
    addRule("构造", "true:False");
    addRule("@解构", "@ind_False : Pu:U@,PC:False->Uu,Px:False,C x");
    addRule("@解构", "ind_False := @ind_False _");
    addRule("_解构", "ind_False");

    typeName = "(False)";
    addRule("定义", "not:=La:U_.a->False");

    typeName = "Bool";
    addRule("类型", "Bool:U");
    addRule("构造", "0b:Bool");
    addRule("构造", "1b:Bool");
    addRule("@解构", "@ind_Bool : Pu:U@,PC:Bool->Uu,Pc0b:C 0b,Pc1b:C 1b,Px:Bool,C x");
    addRule("@解构", "ind_Bool := @ind_Bool _");
    addRule("_解构", "ind_Bool");
    addRule("计算", "ind_Bool ?C ?c0b ?c1b 0b === ?c0b");
    addRule("计算", "ind_Bool ?C ?c0b ?c1b 1b === ?c1b");

    typeName = "nat";
    addRule("类型", "nat:U");
    addRule("构造", "0:nat");
    addRule("构造", "succ:nat->nat");
    addRule("@解构", "@ind_nat : Pu:U@,PC:nat->Uu,Pc0:C 0,Pcs:(Px:nat,Py:C x,C (succ x)),Px:nat,C x");
    addRule("@解构", "ind_nat := @ind_nat _");
    addRule("_解构", "ind_nat");
    addRule("计算", "ind_nat ?C ?c0 ?csucc 0 === ?c0");
    addRule("计算", "ind_nat ?C ?c0 ?csucc (succ ?cn) === ?csucc ?cn (ind_nat ?C ?c0 ?csucc ?cn)");
    typeName = "(nat)";
    addRule("定义", "add:=ind_nat (Lx:nat.nat->nat) (Lx:nat.x) (Ly:nat.Lh:nat->nat.Lx:nat.succ (h x))");
    addRule("定义", "mul:=ind_nat (Lx:nat.nat->nat) (Lx:nat.0) (Ly:nat.Lh:nat->nat.Lx:nat.add (h x) x)");


    typeName = "eq";
    addRule("@类型", "@eq : Pu:U@,Pa:Uu,a->a->Uu");
    addRule("@类型", "eq := @eq _ _");
    addRule("_类型", "eq");
    addRule("@构造", "@refl : Pu:U@,Pa:Uu,Px:a,@eq u a x x");
    addRule("@构造", "refl := @refl _ _");
    addRule("@构造", "rfl := @refl _ _ _");
    addRule("_构造", "refl");
    addRule("_构造", "rfl");
    addRule("@解构", "@ind_eq : Pu:U@,Pv:U@,Pa:Uu,Px:a,PC:Py:a,(@eq u a x y)->Uv,Pc:C x (@refl u a x),Py:a,Pm:@eq u a x y,C y m");
    addRule("@解构", "@ind_eq2 : Pu:U@,Pv:U@,Pa:Uu,PC:Px:a,Py:a,(@eq u a x y)->Uv,Pc:Px:a,C x x (@refl u a x),Px:a,Py:a,Pm:@eq u a x y,C x y m");
    addRule("@解构", "ind_eq := @ind_eq _ _ _");
    addRule("@解构", "ind_eq2 := @ind_eq2 _ _ _");
    addRule("_解构", "ind_eq");
    addRule("_解构", "ind_eq2");
    addRule("计算", "ind_eq ?x ?C ?crfl ?x (refl ?x) === ?crlf");
    addRule("计算", "ind_eq2 ?C ?crfl ?x ?x (refl ?x) === ?crfl ?x");


    typeName = "Prod";
    addRule("@类型", "@Prod : Pu:U@,Pv:U@,Pa:Uu,Pb:a->Uv,(U(@max u v))");
    addRule("@类型", "Sx:?A,?B x := @Prod _ _ ?A (Lx:?A.?B x)");
    addRule("@类型", "?A X ?B := @Prod _ _ ?A (Lx:?A.?B)");
    addRule("_类型", "Sx:?A,?B x");
    addRule("_类型", "?A X ?B := Sx:?A,?B");
    addRule("@构造", "@pair : Pu:U@,Pv:U@,Pa:Uu,Pb:a->Uv,Pxa:a,Pxb:b xa,Sx:a,b x");
    addRule("@构造", "pair := @pair _ _ _");
    addRule("_构造", "pair");
    addRule("构造", "(?a,?b) := pair (Lx:?a：.?b：) ?a ?b");
    addRule("@解构", "@ind_Prod : Pu:U@,Pv:U@,Pw:U@,Pa:Uu,Pb:a->Uv,PC:(Sx:a,b x)->Uw,(Pxa:a,Pxb:b xa,(C (pair b xa xb)))->(Px:Sx:a,b x,C x)");
    addRule("@解构", "ind_Prod := @ind_Prod _ _ _ _");
    addRule("_解构", "ind_Prod");
    addRule("计算", "ind_Prod ?b ?C ?c (pair ?b ?xa ?xb) === ?c ?xa ?xb");
    addRule("定义", "@pr0:=La:U_.Lb:U_.ind_Prod (Lx:a.b) (Lx:aXb.a) (Lx:a.Ly:b.x)");
    addRule("定义", "pr0:=@pr0 _ _");
    addRule("定义", "@prd1:=La:U_.Lb:a->U_.ind_Prod b (Lm:Sz:a,b z.b (pr0 m)) (Lxa:a.Lxb:b xa.xb)");
    addRule("定义", "prd1:=@prd1 _ ");
    addRule("定义", "@pr1:=La:U_.Lb:U_.ind_Prod (Lx:a.b) (Lm:aXb.b) (Lxa:a.Lxb:b.xb)");
    addRule("定义", "pr1:=@pr1 _ _");

    typeName = "Sum";
    addRule("@类型", "@Sum : Pu:U@,Pv:U@,Uu->Uv->(U(@max u v))");
    addRule("@类型", "?A + ?B := @Sum _ _ ?A ?B");
    addRule("_类型", "?A + ?B");
    addRule("@构造", "@inl : Pu:U@,Pv:U@,Pa:Uu,Pb:Uv,Pxa:a,a + b");
    addRule("@构造", "inl := @inl _ _ _ _");
    addRule("_构造", "inl");
    addRule("@构造", "@inr : Pu:U@,Pv:U@,Pa:Uu,Pb:Uv,Pxb:b,a + b");
    addRule("@构造", "inr := @inr _ _ _ _");
    addRule("_构造", "inr");
    addRule("@解构", "@ind_Sum : Pu:U@,Pv:U@,Pw:U@,Pa:Uu,Pb:Uv,PC:(a + b)->Uw,(Pxa:a,(C (inl xa)))->(Pxb:b,(C (inr xb)))->(Px:a + b,C x)");
    addRule("@解构", "ind_Sum := @ind_Sum _ _ _ _ _");
    addRule("_解构", "ind_Sum");
    addRule("计算", "ind_Sum ?C ?cinl ?cinr (inl ?xa) === ?cinl ?xa");
    addRule("计算", "ind_Sum ?C ?cinl ?cinr (inr ?xb) === ?cinr ?xb");


    // state: State = {
    //     sysTypes: {
    //         "nat": parser.parse("U"),
    //         "Bool": parser.parse("U"),
    //         "0b": parser.parse("Bool"),
    //         "1b": parser.parse("Bool"),
    //         "True": parser.parse("U"),
    //         "true": wrapVar("True"),
    //         "succ": parser.parse("nat->nat"),
    //         "False": parser.parse("U"),
    //         "@ind_nat": parser.parse("Pu:U@,PC:nat->Uu,Pc0:C 0,Pcs:(Px:nat,Py:C x,C (succ x)),Px:nat,C x"),
    //         "@ind_True": parser.parse("Pu:U@,PC:True->Uu,Pc:C true,Px:True,C x"),
    //         "@ind_False": parser.parse("Pu:U@,PC:False->Uu,Px:False,C x"),
    //         "@ind_Bool": parser.parse("Pu:U@,PC:Bool->Uu,Pc0b:C 0b,Pc1b:C 1b,Px:Bool,C x"),
    //         "@ind_eq2": parser.parse("Pu:U@,Pv:U@,Pa:Uu,PC:Px:a,Py:a,(@eq u a x y)->Uv,Pc:Px:a,C x x (@refl u a x),Px:a,Py:a,Pm:@eq u a x y,C x y m"),
    //         "@ind_eq": parser.parse("Pu:U@,Pv:U@,Pa:Uu,Px:a,PC:Py:a,(@eq u a x y)->Uv,Pc:C x (@refl u a x),Py:a,Pm:@eq u a x y,C y m"),
    //         "@eq": parser.parse("Pu:U@,Pa:Uu,a->a->Uu"),
    //         "@refl": parser.parse("Pu:U@,Pa:Uu,Px:a,@eq u a x x"),
    //         "@Prod": parser.parse("Pu:U@,Pv:Un,Pa:Uu,Pb:Uv,a->b->(U(@max u v))"),
    //         "@pair": parser.parse("Pu:U@,Pv:U@,Pa:Uu,Pb:Px:a,Uv,  Pxa:a,Pxb:b xa, Sx:a,b x"),
    //         "funext": parser.parse("Pf:_,Pg:_,(homotopy f g)->(eq f g)"),
    //         // "ua":parser.parse(""),
    //     },
    //     sysDefs: {
    //         "eq": parser.parse("@eq _ _"),
    //         "rfl": parser.parse("@refl _ _ _"),
    //         "refl": parser.parse("@refl _ _"),
    //         "pair": parser.parse("@pair _ _ _"),
    //         "ind_nat": parser.parse("@ind_nat _"),
    //         "ind_True": parser.parse("@ind_True _"),
    //         "ind_False": parser.parse("@ind_False _"),
    //         "ind_Bool": parser.parse("@ind_Bool _"),
    //         "ind_eq": parser.parse("@ind_eq _ _ _"),
    //         "ind_eq2": parser.parse("@ind_eq2 _ _ _"),
    //     },
    //     userDefs: {},
    //     errormsg: []
    // };
    return ruleList;
}