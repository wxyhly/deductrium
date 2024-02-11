import { ASTParser } from "./astparser.js";
import { Deduction, DeductionStep, FormalSystem } from "./formalsystem.js";
const astparser = new ASTParser;
let deductionFrom = "";
type DeductionStepString = [deductionIdx: number, replaceValues: string[], conditionIdxs: number[]];

export function addZFC(fs: FormalSystem) {
    function addDeduction(str: string, macro?: DeductionStepString[]) {
        fs.addDeduction(astparser.parse(str), deductionFrom, macro?.map(step => ({
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
    addMetaRule("qt", "(##nf(...$$1,$$0)⊢ $$2 ) ⊢M (##nf(...$$1,$$0) ⊢ V$$0:$$2 )");


    deductionFrom = "命题逻辑";
    addDeduction("$0> $1, $0 ⊢ $1");
    addDeduction("⊢ $0>($1>$0)");
    addDeduction("⊢ ($0>($1>$2)) > (($0>$1)>($0>$2))");
    addDeduction("⊢ (~$0 > ~$1) > ($1>$0)");

    deductionFrom = "一阶逻辑";
    addDeduction("⊢ (V$0 #canrepl($1,$0,$2)) > #repl($1,$0,$2)");
    addDeduction("⊢ (V$0 ($1>$2)) > ((V$0 $1)>(V$0 $2))");
    addDeduction("⊢ #nf($1,$0) >( V$0 #nf($1,$0))");

    deductionFrom = "符号定义";

    addDeduction("⊢($0<>$1) > ~(($0>$1)>~($1>$0))");
    addDeduction("⊢~(($0>$1)>~($1>$0)) > ($0<>$1)");
    addDeduction("⊢($0|$1) <> (~$0>$1)");
    addDeduction("⊢($0&$1) <> ~($0>~$1)");
    addDeduction("⊢(E$0:$1) <> ~(V$0:~$1)");

    addDeduction("⊢ (#nf($a,$0)<#nf($b,$0)) <> (V$0:$0@#nf($a,$0) > $0@#nf($b,$0))");
    addDeduction("⊢ ($a=$b <> ($a < $b & $b < $a))");
    // addDeduction(`⊢ (E!#nf($0,$2):#nf($1,$2))`.replaceAll("\n",""));
    addDeduction(`
    ⊢ (E!#nf($0,$2):#nf($1,$2)) <> 
    (
        (E#nf($0,$2):#nf($1,$2))
         &
        (V#nf($0,$2):V$2:(
            (#nf($1,$2) & #repl(#nf($1,$2),#nf($0,$2),$2) )
            > 
            (#nf($0,$2)=$2)
        
        ))
    )`.replaceAll("\n",""));
    addDeduction("⊢ (#nf($z,$0) @ Union(#nf($x,$0))) <> (V$0 ($0@#nf($x,$0) > #nf($z,$0)@$0))");
    addDeduction("⊢ ($z @ ($x U $y)) <> (($z @ $x) | ($z @ $y)))");
    addDeduction("⊢ ($z @ ($x I $y)) <> (($z @ $x) & ($z @ $y)))");
    addDeduction("⊢ ($z @ P($x,$y) <> ($z=$x|$z=$y))");
    addDeduction("⊢ ($z @ Pow($x) <> ($z<$x))");
    addDeduction("⊢ (S($0) = $0 U P($0,$0))");
    addDeduction("⊢ (Vx: ~(x @ 0))");
    addDeduction("⊢ 1 = S(0)");
    addDeduction("⊢ 2 = S(1)");
    addDeduction("⊢ 3 = S(2)");
    addDeduction("⊢ 4 = S(3)");
    addDeduction("⊢ 5 = S(4)");
    addDeduction("⊢ 6 = S(5)");
    addDeduction("⊢ 7 = S(6)");
    addDeduction("⊢ 8 = S(7)");
    addDeduction("⊢ 9 = S(8)");
    addDeduction("( ⊢ S($x+$y)=($x+S($y)))");
    addDeduction("( ⊢ $x+0=$x)");
    addDeduction("( ⊢ $x*0=0)");
    addDeduction("( ⊢ S($x)*$y=$y+$x*$y)");

    deductionFrom = "ZFC集合论";
    addDeduction("⊢ Ex: x=0");
    addDeduction("⊢ (Vx:Vy:Ea:a=P(x,y))");
    addDeduction("⊢ (Vx:Ey:y=Pow(x))");
    addDeduction("⊢ (Vx:Ey:y=Union(x))");
    addDeduction("⊢ Vx: (~x=0 > Ey (y@x & x I y = 0))");
    addDeduction("⊢ Va(Vx (x@a > E!y:#nf($0,z))>Eb:Vx:(x@a > Ey (y@b & #nf($0,z))))");
    addDeduction("⊢ Vx:Ey:Vz:(z@y<>(z@x&#nf($0,x)))");
    addDeduction("⊢ Ex:(0@x & (Vy: (y@x > S(y)@x))))");

    deductionFrom = "paddings";
    while (fs.deductions.length < 100 - 8) addDeduction("⊢ #nf(x,x)");
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

    fs.deductions.forEach(d => d.from += "[S]");
}