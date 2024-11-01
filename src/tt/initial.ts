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
    addRule("计算", "ind_nat ?C ?c0 ?csucc (succ ?n) === ?csucc ?n (ind_nat ?C ?c0 ?csucc ?n)");
    typeName = "(nat)";
    addRule("定义", "pred:=ind_nat (Lx:nat.nat) 0 (Lx:nat.Ly:nat.x)");
    addRule("定义", "double:=ind_nat (Lx:nat.nat) 0 (Ly:nat.Lz:nat.succ (succ z))");
    addRule("定义", "add:=Lx:nat.Ly:nat.ind_nat (Lx:nat.nat->nat) (Lx:nat.x) (Ly:nat.Lh:nat->nat.Lx:nat.succ (h x))y x");
    addRule("定义", "mul:=Lx:nat.Ly:nat.ind_nat (Lx:nat.nat->nat) (Lx:nat.0) (Ly:nat.Lh:nat->nat.Lx:nat.add (h x) x)y x");
    addRule("定义", "encode_nat:=ind_nat (Lx:nat.nat->U ) (ind_nat (Ly:nat.U ) True (Lz:nat.Lz':U .False ))  (Ly':nat,Lfn:nat->U.(ind_nat (Ly:nat.U ) False (Lz:nat.Lz':U .fn z )))");


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
    addRule("@解构", "ind_eq := @ind_eq _ _ _");
    addRule("_解构", "ind_eq");
    addRule("计算", "ind_eq ?x ?C ?crfl ?x (refl ?x) === ?crlf");
    addRule("@解构", "@ind_eq2 : Pu:U@,Pv:U@,Pa:Uu,PC:Px:a,Py:a,(@eq u a x y)->Uv,Pc:Px:a,C x x (@refl u a x),Px:a,Py:a,Pm:@eq u a x y,C x y m");
    addRule("@解构", "ind_eq2 := @ind_eq2 _ _ _");
    addRule("_解构", "ind_eq2");
    addRule("计算", "ind_eq2 ?C ?crfl ?x ?x (refl ?x) === ?crfl ?x");
    typeName = "(eq)";
    addRule("定义", "@ap:=La:U_.Lb:U_.Lx:a.Ly:a.Lf:a->b.Lp:eq x y.ind_eq x (Ly:a.Lm:eq x y.eq (f x) (f y)) rfl y p");
    addRule("定义", "ap:=@ap _ _ _ _");
    addRule("定义", "@trans:=La:U_.Lx:a.Ly:a.Lb:a->U_.ind_eq x (Ly:a.Lm:eq x y.(b x)->(b y)) (Lx:b x.x) y");
    addRule("定义", "trans:=@trans _ _ _");
    addRule("定义", "@apd:=La:U_.Lx:a.Ly:a.Lb:a->U_.Lf:Px:a,b x.Lp:eq x y.ind_eq x (Ly:a.Lp:eq x y. eq (@trans a x y b p (f x)) (f y)) (refl (f x)) y p");
    addRule("定义", "apd:=@apd _ _ _");
    addRule("定义", "@inveq:=La:U_.Lx:a.ind_eq x (Ly:a.Lm:eq x y.eq y x) rfl");
    addRule("定义", "inveq:=@inveq _ _ _");
    addRule("定义", "@compeq:=La:U_.Lx:a.Ly:a.Lz:a.ind_eq x (Ly:a.Lm:eq x y.(eq y z)->(eq x z)) (Lm:eq x z.m) y");
    addRule("定义", "compeq:=@compeq _ _ _ _");


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
    typeName = "(Prod)";
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
    typeName = "eqv";
    addRule("_定义", "@eqv:=Lu:U@,La:Uu,Lb:Uu,Sf:a->b,(Sg:b->a,Px:a,eq x (g(f x)))X(Sh:b->a,Px:b, eq x (f(h x)))");
    addRule("_定义", "eqv:=@eqv _");
    addRule("_定义", "eqv");
    addRule("定义", "@id2eqv:=Lu:U@.(λa:Uu.(λb:Uu.(λh':((eq a) b).((((((ind_eq a) (λy':Uu.(λm':((eq a) y').((Σf:(y'→b),((Σg:(b→y'),(Πx:y',((eq x) (g (f x)))))×(Σh:(b→y'),(Πx:b,((eq x) (f (h x)))))))→(Σf:(a→b),((Σg:(b→a),(Πx:a,((eq x) (g (f x)))))×(Σh:(b→a),(Πx:b,((eq x) (f (h x))))))))))) (λm':(Σf:(a→b),((Σg:(b→a),(Πx:a,((eq x) (g (f x)))))×(Σh:(b→a),(Πx:b,((eq x) (f (h x))))))).m')) b) h') (((pair (λf:(b→b).((Σg:(b→b),(Πx:b,((eq x) (g (f x)))))×(Σh:(b→b),(Πx:b,((eq x) (f (h x)))))))) (λx:b.x)) ((((pair (λg:(b→b).(Πx:b,((eq x) (g x))))) (λx:b.x)) (λx:b.rfl)),(((pair (λh:(b→b).(Πx:b,((eq x) (h x))))) (λx:b.x)) (λx:b.rfl)))))))):Pu:U@,(Πa:Uu,(Πb:Uu,(((eq a) b)→((eqv a) b))))");
    addRule("定义", "id2eqv:=@id2eqv _ _ _");
    addRule("@构造", "@ua:Pu:U@,Pv:U@,Pa:Uu,Pb:Uv,(eqv a b)->(eq a b)");
    addRule("@构造", "ua:=@ua _ _ _ _");
    addRule("_构造", "ua");
    addRule("计算", "ua (id2eqv ?p) === ?p");
    addRule("计算", "id2eqv (ua ?p) === ?p");

    typeName = "S1";
    addRule("类型", "S1:U");
    addRule("构造", "base:S1");
    addRule("@构造", "loop:@eq @0 S1 base base");
    addRule("_构造", "loop");
    addRule("解构", "ind_S1: PC:S1->U,Pcb:(C base),Pcl: @eq _ (C base) cb cb,Pm:S1,C m");
    addRule("计算", "ind_S1 ?C ?cb ?cl base === ?cb");
    addRule("计算", "apd ?C (ind_S1 ?C ?cb ?cl) ?p === ?cl");
    typeName = "Ord"
    addRule("类型","Ord:U");
    addRule("构造","0O:Ord");
    addRule("构造","succO:Ord->Ord");
    addRule("构造","limO:(nat->Ord)->Ord");
    addRule("@解构","@ind_Ord:Pu:U@,PC:Ord->Uu,Pc0:C 0O,Pcs:Po:Ord,(C o)->(C (succO o)),Pclim:Parr:nat->Ord,(Pn:nat,C (arr n))->(C (limO arr)),Px:Ord,C x");
    addRule("@解构","ind_Ord:=@ind_Ord _");
    addRule("_解构","ind_Ord");
    addRule("计算","ind_Ord ?C ?c0 ?cs ?clim 0O === ?c0");
    addRule("计算","ind_Ord ?C ?c0 ?cs ?clim (succO ?o) === ?cs ?o (ind_Ord ?C ?c0 ?cs ?clim ?o)");
    addRule("计算","ind_Ord ?C ?c0 ?cs ?clim (limO ?f) === ?clim ?f (Ln:nat.ind_Ord ?C ?c0 ?cs ?clim (?f n))");
    typeName = "(Ord)"
    addRule("定义","natO:=ind_nat (λx:nat.Ord) 0O λx:nat.λh:Ord.(succO h)");
    addRule("定义","omega:=limO natO");
    addRule("定义","leqO:=ind_Ord (Lx:Ord.Ord->U) (Lx:Ord.True) (Lo:Ord.Lleqo:Ord->U.ind_Ord (Lx:Ord.U) False (Lm:Ord.Lleqm:U.leqo m) (Larr:nat->Ord,Lfnleq:Pn:nat,U.Sx:nat,fnleq x)) (Larr:nat->Ord.Lg:nat->Ord->U.Lo:Ord.Px:nat,g x o)");
    addRule("定义","addO:=ind_Ord (Lx:Ord.Ord->Ord) (Lx:Ord.x) (Lx:Ord.Lf:Ord->Ord,Ly:Ord.succO(f y)) (Larr:nat->Ord.Lg:nat->Ord->Ord.Ly:Ord.limO (Ln:nat.g n y ))");

    return ruleList;
}