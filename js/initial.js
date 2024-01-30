import { ASTParser } from "./astparser.js";
const astparser = new ASTParser;
let deductionFrom = "";
export function addZFC(fs) {
    function addDeduction(str, macro) {
        fs.addDeduction(astparser.parse(str), deductionFrom, macro?.map(step => ({
            deductionIdx: step[0],
            conditionIdxs: step[2],
            replaceValues: step[1].map(s => astparser.parse(s))
        })));
    }
    function addMetaRule(str) {
        fs.addMetaRule(astparser.parse(str), deductionFrom);
    }
    deductionFrom = "演绎元定理";
    addMetaRule("(...$$0, $$1 ⊢ $$2 ) ⊢M (...$$0 ⊢ $$1 > $$2 )");
    deductionFrom = "符号定义";
    addMetaRule("##new($$0) ⊢M (⊢ $0 > #replace($0, #0 $$0 #1, $$1)) ,( ⊢ $0 > #replace($0,$$1, #0 $$0 #1)) ");
    deductionFrom = "常数定义";
    addMetaRule("(E!$$0 : $$1), ##new($$2) ⊢M ( ⊢ ##replace($$1,$$0,$$2) )");
    deductionFrom = "命题逻辑";
    addDeduction("$0> $1, $0 ⊢ $1");
    addDeduction("⊢ $0>($1>$0)");
    addDeduction("⊢ ($0>($1>$2)) > (($0>$1)>($0>$2))");
    addDeduction("⊢ (~$0 > ~$1) > ($1>$0)");
    deductionFrom = "一阶逻辑";
    addDeduction("⊢ (V$0 $1) > #replace($1,$0,$2)");
    addDeduction("⊢ (V$0 #satisfy($1,!$0)>$2) > ($1>(V$0 $2))");
    addDeduction("⊢ (V$0 $1>$2) > ((V$0 $1)>(V$0 $2))");
    addDeduction("$0 ⊢V$1 $0");
    deductionFrom = "m0所需宏";
    addDeduction('( ⊢ ($0 > $0))', [[1, ["$0", "($0 > $0)"], []], [1, ["$0", "$0"], []], [2, ["$0", "($0 > $0)", "$0"], []], [0, [], [-1, -3]], [0, [], [-1, -3]]]);
    addDeduction("(($0 > $1), ($1 > $2) ⊢ ($0 > $2))", [[1, ["($1 > $2)", "$0"], []], [0, [], [-1, 1]], [2, ["$0", "$1", "$2"], []], [0, [], [-1, -2]], [0, [], [-1, 0]]]);
    addDeduction("($0 ⊢ (($0 > $1) > $1))", [[8, ["($0 > $1)"], []], [2, ["($0 > $1)", "$0", "$1"], []], [0, [], [-1, -2]], [1, ["$0", "($0 > $1)"], []], [0, [], [-1, 0]], [0, [], [-3, -1]]]);
    addDeduction("((($0 > $1) > $0) ⊢ (($0 > $1) > $1))", [[8, ["($0 > $1)"], []], [2, ["($0 > $1)", "$0", "$1"], []], [0, [], [-1, -2]], [0, [], [-1, 0]]]);
    addDeduction("(($0 > ($1 > $2)), $1 ⊢ ($0 > $2))", [[2, ["$0", "$1", "$2"], []], [0, [], [-1, 0]], [1, ["$1", "$0"], []], [0, [], [-1, 1]], [0, [], [-3, -1]]]);
    addDeduction("(($0 > ($0 > $1)) ⊢ ($0 > $1))", [[8, ["$0"], []], [2, ["$0", "$0", "$1"], []], [0, [], [-1, 0]], [0, [], [-1, -3]]]);
    addDeduction("(($0 > ($1 > $2)), ($0 > $1) ⊢ ($0 > $2))", [[2, ["$0", "$1", "$2"], []], [0, [], [-1, 0]], [0, [], [-1, 1]]]);
    addDeduction("( ⊢ ($0 > (V$1: $0)))", [[8, ["$0"], []], [7, ["$1"], [-1]], [5, ["$1", "$0", "$0"], []], [0, [], [-1, -2]]]);
    deductionFrom = "符号宏";
    addDeduction("⊢($0>$1)>(($1>$0)>($0<>$1))");
    addDeduction("⊢($0<>$1)>(~($0>$1)>($1>$0))");
    addDeduction("⊢(~$0>$1) <> ($0|$1)");
    addDeduction("⊢~($0>~$1) <> ($0&$1)");
    addDeduction("⊢~($0>~$1) <> ($0&$1)");
    addDeduction("⊢~(V$0:~$1) <> (E$0:$1)");
    addDeduction("⊢(V$0:($0@#satisfy($1,!$0) <> $0@#satisfy($2,!$0))) <> ($1=$2)");
    // addDeduction("$0 ⊢#replace($0,(E#0:#1)&(Vx:(Vy:(#replace(#1,#0,x)&#replace(#1,#0,y) <> x=y))),E!#0:#1)");
    // addDeduction("$0 ⊢#replace($0,E!#0:#1,(E#0:#1)&(Vx:(Vy:(#replace(#1,#0,x)&#replace(#1,#0,y) <> x=y))))");
}
//# sourceMappingURL=initial.js.map