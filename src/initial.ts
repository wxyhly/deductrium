import { ASTParser } from "./astparser.js";
import { Deduction, DeductionStep, FormalSystem } from "./formalsystem.js";
const astparser = new ASTParser;
let deductionFrom = "";
type DeductionStepString = [deductionIdx: number, replaceValues: string[], conditionIdxs: number[]];

export function addZFC(fs: FormalSystem) {
    function addDeduction(str: string, macro?: DeductionStepString[]) {
        fs.addDeduction(astparser.parse(str), deductionFrom + "[S]", macro?.map(step => ({
            deductionIdx: step[0],
            conditionIdxs: step[2],
            replaceValues: step[1].map(s => astparser.parse(s))
        })));
    }
    function addMetaRule(key: string, str: string) {
        fs.addMetaRule(key, astparser.parse(str), deductionFrom);
    }

    deductionFrom = "普遍化公理模式";
    addMetaRule("q", "##isaxiom( ⊢ $$0 ) ⊢M ##axiom( ⊢ V$$1 $$0 )");
    deductionFrom = "常数定义公理模式";
    addMetaRule("c", "##newconst($$0) ⊢M ( ##axiom( ⊢  (E$$1:$$2) > ##repl($$2,$$1,$$0)) )");
    deductionFrom = "函数定义公理模式";
    addMetaRule("f", "##newfn($$0) ⊢M ( ##axiom( ⊢ V$$1:E$$2: $$3) > (V$$1: ##repl($$3,$$2,$$0($$1))))");
    deductionFrom = "演绎元定理";
    addMetaRule("dt", "(...$$0, $$1 ⊢ $$2 ) ⊢M (...$$0 ⊢ $$1 > $$2 )");
    deductionFrom = "普遍化元定理";
    addMetaRule("qt", "(##nofree(...$$1,$$0)⊢ $$2 ) ⊢M (##nofree(...$$1,$$0) ⊢ V$$0:$$2 )");
    // deductionFrom = "符号定义";
    // addMetaRule("##new($$0) ⊢M (⊢ $0 $$0 $1 <> $$1($0,$1) ) ");
    // deductionFrom = "函数定义";
    // addMetaRule("##new(#$0) ⊢M (⊢ #$0($0, $1) <> $$1($0,$1) ) ");

    deductionFrom = "命题逻辑";
    addDeduction("$0> $1, $0 ⊢ $1");
    addDeduction("⊢ $0>($1>$0)");
    addDeduction("⊢ ($0>($1>$2)) > (($0>$1)>($0>$2))");
    addDeduction("⊢ (~$0 > ~$1) > ($1>$0)");

    deductionFrom = "一阶逻辑";
    addDeduction("⊢ (V$0 #canrepl($1,$0,$2)) > #repl($1,$0,$2)");
    addDeduction("⊢ (V$0 ($1>$2)) > ((V$0 $1)>(V$0 $2))");
    addDeduction("⊢ #nofree($1,$0) >( V$0 #nofree($1,$0))");

    deductionFrom = "符号定义";

    addDeduction("⊢($0>$1)>(($1>$0)>($0<>$1))");
    addDeduction("⊢($0<>$1)>($0>$1)");
    addDeduction("⊢($0<>$1)>($1>$0)");
    addDeduction("⊢($0|$1) <> (~$0>$1)");
    addDeduction("⊢($0&$1) <> ~($0>~$1)");
    addDeduction("⊢(E$0:$1) <> ~(V$0:~$1)");
    addDeduction("⊢ (#nofree($a,$0)=#nofree($b,$0)) <> (V$0:$0@#nofree($a,$0)<>$0@#nofree($b,$0))");
    addDeduction("⊢ (#nofree($a,$0)<#nofree($b,$0)) <> (V$0:$0@#nofree($a,$0) > $0@#nofree($b,$0))");
    deductionFrom = "ZFC集合论";
    addDeduction("⊢ Ex: (Vy: ~(y @ x))");
    addDeduction("⊢ (Vx:Vy:Ea:Vz:(z@a <> (z=x | z=y)))");
    addDeduction("⊢ (Va:Eb:Vc:(x@b <> (Ed:(c@d & d@a))))");
    addDeduction("⊢ (Va:Eb:Vc:(c@b <> ((Vd:d@c) > d@a))))");

    addDeduction("⊢ (Vx:(~x=0 > (Ey: (y@x > ~(Ez:(z@y & z@x))))))");
    addDeduction("⊢ Ex:(0@x & (Vy: (y@x > S(y)@x))))");

    deductionFrom = "符号定义";
    addDeduction("( ⊢ ((Vx: (Ey: (((x @ y) & (Vz: ((z @ x) > (z @ y)))) & (Vz: ((z @ y) > ((z = x) | (z @ x))))))) > (Vx: (((x @ S(x)) & (Vz: ((z @ x) > (z @ S(x))))) & (Vz: ((z @ S(x)) > ((z = x) | (z @ x))))))))");
    addDeduction("( ⊢ (Vx:Vy: S(x+y)=(x+S(y)))))");
    addDeduction("( ⊢ (Vx: (x+0=x)))");
    addDeduction("( ⊢ ((Ex: (Vy: ~(y @ x))) > (Vy: ~(y @ 0))))");
    addDeduction("( ⊢ ((Ex: (x = S(0))) > (1 = S(0))))");
    addDeduction("( ⊢ ((Ex: (x = S(1))) > (2 = S(1))))");
    addDeduction("( ⊢ ((Ex: (x = S(2))) > (3 = S(2))))");
    addDeduction("( ⊢ ((Ex: (x = S(3))) > (4 = S(3))))");
    addDeduction("( ⊢ ((Ex: (x = S(4))) > (5 = S(4))))");
    addDeduction("( ⊢ ((Ex: (x = S(5))) > (6 = S(5))))");
    addDeduction("( ⊢ ((Ex: (x = S(6))) > (7 = S(6))))");
    addDeduction("( ⊢ ((Ex: (x = S(7))) > (8 = S(7))))");
    addDeduction("( ⊢ ((Ex: (x = S(8))) > (9 = S(8))))");

    deductionFrom = "paddings";
    while (fs.deductions.length < 100 - 8) addDeduction("⊢ #nofree(x,x)");
    deductionFrom = "内置宏";
    // d92-d99

    addDeduction('( ⊢ ($0 > $0))', [[1, ["$0", "($0 > $0)"], []], [1, ["$0", "$0"], []], [2, ["$0", "($0 > $0)", "$0"], []], [0, [], [-1, -3]], [0, [], [-1, -3]]]);
    addDeduction("(($0 > $1), ($1 > $2) ⊢ ($0 > $2))", [[1, ["($1 > $2)", "$0"], []], [0, [], [-1, 1]], [2, ["$0", "$1", "$2"], []], [0, [], [-1, -2]], [0, [], [-1, 0]]]);
    addDeduction("($0 ⊢ (($0 > $1) > $1))", [[92, ["($0 > $1)"], []], [2, ["($0 > $1)", "$0", "$1"], []], [0, [], [-1, -2]], [1, ["$0", "($0 > $1)"], []], [0, [], [-1, 0]], [0, [], [-3, -1]]]);
    addDeduction("((($0 > $1) > $0) ⊢ (($0 > $1) > $1))", [[92, ["($0 > $1)"], []], [2, ["($0 > $1)", "$0", "$1"], []], [0, [], [-1, -2]], [0, [], [-1, 0]]]);
    addDeduction("(($0 > ($1 > $2)), $1 ⊢ ($0 > $2))", [[2, ["$0", "$1", "$2"], []], [0, [], [-1, 0]], [1, ["$1", "$0"], []], [0, [], [-1, 1]], [0, [], [-3, -1]]]);
    addDeduction("(($0 > ($0 > $1)) ⊢ ($0 > $1))", [[92, ["$0"], []], [2, ["$0", "$0", "$1"], []], [0, [], [-1, 0]], [0, [], [-1, -3]]]);
    addDeduction("(($0 > ($1 > $2)), ($0 > $1) ⊢ ($0 > $2))", [[2, ["$0", "$1", "$2"], []], [0, [], [-1, 0]], [0, [], [-1, 1]]]);
    addDeduction("((V$2: ($0 > $1)), (V$2: $0) ⊢ (V$2: $1))", [[5, ["$2", "$0", "$1"], []], [0, [], [-1, 0]], [0, [], [-1, 1]]]);

    // addDeduction("⊢V$0: Esatisfy($1,$0): Vsatisfy(nofree($2,$1),$0): $2@$1 <> ($2@$0 & nofree(nofree(nofree($3,$2),$1),$0))");
    // addDeduction("$0 ⊢#replace($0,(E#0:#1)&(Vx:(Vy:(#replace(#1,#0,x)&#replace(#1,#0,y) <> x=y))),E!#0:#1)");
    // addDeduction("$0 ⊢#replace($0,E!#0:#1,(E#0:#1)&(Vx:(Vy:(#replace(#1,#0,x)&#replace(#1,#0,y) <> x=y))))");


}