import { ASTParser } from "./astparser.js";
import { FormalSystem } from "./formalsystem.js";
import { SavesParser } from "./savesparser.js";
const astparser = new ASTParser;
let deductionFrom = "";
export function initFormalSystem(creative) {
    const fs = new FormalSystem;
    function addMetaRule(key, str, condIdxs, replNames) {
        fs.addMetaRule(key, astparser.parse(str), condIdxs, replNames, deductionFrom);
    }
    deductionFrom = "[v]一阶逻辑公理模式";
    addMetaRule("q", "##isaxiom( ⊢ $$0 ) ⊢M ##axiom( ⊢ V$#0 $$0 )", [0], []);
    // deductionFrom = "常数定义公理模式";
    // addMetaRule("c", "##newconst($$0) ⊢M ( ##axiom( ⊢  (E$$1:$$2) > ##rp($$2,$$1,$$0)) )", [], ["$$0", "$$1", "$$2"]);
    // deductionFrom = "函数定义公理模式";
    // addMetaRule("f", "##newfn($$0) ⊢M ( ##axiom( ⊢ V$$1:E$$2: $$3) > (V$$1: ##rp($$3,$$2,$$0($$1))))", [], ["$$0", "$$1", "$$2", "$$3"]);
    deductionFrom = "[c]条件演绎元定理";
    addMetaRule("cdt", "(...$$0 ⊢ $$1 ) ⊢M (##map($$0, $#0 > #0) ⊢ $#0 > $$1 )", [0], []);
    deductionFrom = "[>]演绎元定理";
    addMetaRule("dt", "(...$$0, $$1 ⊢ $$2 ) ⊢M (...$$0 ⊢ $$1 > $$2 )", [0], []);
    deductionFrom = "[<]逆演绎元定理";
    addMetaRule("idt", "(...$$0 ⊢ $$1 > $$2 ) ⊢M (...$$0, $$1 ⊢ $$2 )", [0], []);
    deductionFrom = "[v]条件概括元定理";
    addMetaRule("cvt", "(...$$0 ⊢ $$1 ) ⊢M (##map($$0, V$#0 #0) ⊢ V$#0: $$1 )", [0], []);
    deductionFrom = "[u]概括元定理";
    addMetaRule("vt", "(...$$0⊢ $$1 ) ⊢M (##map($$0, #nf(#0,$#0)) ⊢ V$#0:$$1 )", [0], []);
    deductionFrom = "[:]组合元定理";
    addMetaRule("cmt", "( ...$$0 ⊢ $$1a),($$1b ⊢ $$2) ⊢M (...$$0 ⊢ ##rp($$2,##match($$1a,$$1b)))", [0, 1], []);
    deductionFrom = "充要替换元定理";
    addMetaRule("ifft", "(⊢ $$0 <> $$1) ⊢M (⊢ $$2 <> ##matchrp($$2,$$0,$$1,$$3))", [0], ["$$2", "$$3"]);
    deductionFrom = "完备性元定理";
    addMetaRule("cpt", "( ⊧ $$0) ⊢M (⊢ $$0)", [], ["$$0"]);
    const sysAxioms = {
        // axioms
        "mp": ["$0>$1,$0⊢$1", "命题逻辑", null],
        "a1": ["⊢$0>($1>$0)", "命题逻辑", null],
        "a2": ["⊢($0>($1>$2))>(($0>$1)>($0>$2))", "命题逻辑", null],
        "a3": ["⊢(~$0>~$1)>($1>$0)", "命题逻辑", null],
        "a4": ["⊢(V$0:#crp($1,$0,$2))>#rp($1,$0,$2)", "一阶逻辑", null],
        "a5": ["⊢(V$0:($1>$2))>((V$0:$1)>(V$0:$2))", "一阶逻辑", null],
        "a6": ["⊢#nf($1,$0)>(V$0:#nf($1,$0))", "一阶逻辑", null],
        "a7": ["⊢$0=$0", "一阶逻辑", null],
        "a8": ["⊢($0=$1)>(#crp($2,$0,$1,$3)>#rp($2,$0,$1,$3))", "一阶逻辑", null],
        "apn1": ["⊢Vx:~S(x)=0", "皮亚诺公理", null],
        "apn2": ["⊢VxVy:(S(x)=S(y)>x=y)", "皮亚诺公理", null],
        "apn3": ["⊢#rp($0,$1,0)>(Vx:(#rp($0,$1,x)>#rp($0,$1,S(x)))>Vx:#rp($0,$1,x))", "皮亚诺公理", null],
        "aExt": ["⊢VxVy(Vz(~(((z @ x) > (z @ y)) > ~((z @ y) > (z @ x)))) > x=y)", "ZFC集合论", null],
        "aReg": ["⊢(Vx:((~Va~(a@x))>(~Vy:(((y@x)>~(Vz:~(z@y>~z@x)))))))", "ZFC集合论", null],
        "aPair": ["⊢VxVy~Vz:(x@z>~y@z)", "ZFC集合论", null],
        ".apair": ["⊢VxVyEz(x@z & y@z)", "内置宏", [["vvv.dn", [], ["x", "y", "z", "((x @ z) > ~(y @ z))"]], ["vv<.<>rV", [-1], []], ["vv.<>r~", [-1], []], ["v<.<>rV", [-1], []], ["<.<>rV", [-1], []], ["vvv:d&,.<>4", [], ["x", "y", "z", "(x @ z)", "(y @ z)"]], ["vvv.<>r~", [-1], []], ["vv<.<>rV", [-1], []], ["vv.<>r~", [-1], []], ["v<.<>rV", [-1], []], ["<.<>rV", [-1], []], ["vv:dE,.<>4", [], ["x", "y", "z", "((x @ z) & (y @ z))"]], ["v<.<>rV", [-1], []], ["<.<>rV", [-1], []], [".<>5", [-10, -4], []], [".<>5", [-1, -2], []], ["aPair", [], []], ["<.<>1", [-2], []], ["mp", [-1, -2], []]]],
        "aUnion": ["⊢Vx~Va~VyVz:(z@y>(y@x>z@a))", "ZFC集合论", null],
        "aPow": ["⊢Vx~Vy~Vz (Va (a@z>a@x) > z@y)", "ZFC集合论", null],
        "aSep": ["⊢(Vx: ~(Vy: ~(Vz: ~(((z @ y) > ~((z @ x) > ~#nf($0, x))) > ~(~((z @ x) > ~#nf($0, x)) > (z @ y))))))", "ZFC集合论", null],
        "aRepl": ["⊢(Va: ((Vx: ((x @ a) > ~((Vy: (Vz: (~(#crp(#nf($0, b, z), y, z) > ~#rp(#nf($0, b, z), y, z)) > (y = z)))) > (Vy: ~#crp(#nf($0, b, z), y, z))))) > ~(Vb: ~(Vx: ((x @ a) > ~(Vy: ((y @ b) > ~#crp(#nf($0, b, z), y, z))))))))", "ZFC集合论", null],
        "aInf": ["⊢~(Vx: ((Vy: ((y @ x) > ~(Vz: ((Va: ((a @ z) > (~(a @ y) > (a = y)))) > ((Va: ((a @ y) > (a @ z))) > ((z @ x) > ~(y @ z))))))) > (Vy: ((Vz: ~(z @ y)) > ~(y @ x)))))", "ZFC集合论", null],
        "aChoice": ["⊢(Vx: ((Vc: ~(Ve: ((e @ x) > ~(Va: ((Vb: (~((b @ e) > ~(b @ c)) > (a = b))) > ((a @ e) > ~(a @ c))))))) > ((Va: (Vb: (Vc: (~((c @ b) > ((c @ a) > ((a @ x) > ~(b @ x)))) > (a = b))))) > ~(Vo: ((o @ x) > ~(Vn: ~(n @ o)))))))", "ZFC集合论", null],
        // definitions
        "d<>1": ["⊢($0<>$1)>~(($0>$1)>~($1>$0))", "逻辑符号定义", null],
        "d<>2": ["⊢~(($0>$1)>~($1>$0))>($0<>$1)", "逻辑符号定义", null],
        "d|": ["⊢($0|$1)<>(~$0>$1)", "逻辑符号定义", null],
        "d&": ["⊢($0&$1)<>~($0>~$1)", "逻辑符号定义", null],
        "dE": ["⊢(E$0:$1)<>~(V$0:~$1)", "逻辑符号定义", null],
        "dE!": ["⊢(E!#nf($0,$2):#nf($1,$2))<>((E#nf($0,$2):#nf($1,$2))&(V#nf($0,$2):(V$2:((#nf($1,$2)&#rp(#nf($1,$2),#nf($0,$2),$2))>(#nf($0,$2)=$2)))))", "逻辑符号定义", null],
        "d{}": ["⊢Vx:~x@{}", "集合符号定义", null],
        "d{.}": ["⊢$1@{$2}<>$1=$2", "集合符号定义", null],
        "d{..}": ["⊢$1@{$2,$3}<>($1=$2|$1=$3)", "集合符号定义", null],
        "d<": ["⊢(#nf($a,$0)<#nf($b,$0))<>(V$0:(($0@#nf($a,$0))>($0@#nf($b,$0))))", "集合符号定义", null],
        "dUnion": ["⊢(#nf($z,$0)@Union(#nf($x,$0)))<>(V$0:(($0@#nf($x,$0))>(#nf($z,$0)@$0)))", "集合符号定义", null],
        "dU": ["⊢($z@($xU$y))<>(($z@$x)|($z@$y))", "集合符号定义", null],
        "dI": ["⊢($z@($xI$y))<>(($z@$x)&($z@$y))", "集合符号定义", null],
        "dPow": ["⊢($z@Pow($x))<>($z<$x)", "集合符号定义", null],
        "dS": ["⊢S($0)=($0U{$0})", "集合算数连接", null],
        "d0": ["⊢0={}", "集合算数连接", null],
        "d1": ["⊢1=S(0)", "算数符号定义", null],
        "d2": ["⊢2=S(1)", "算数符号定义", null],
        "d3": ["⊢3=S(2)", "算数符号定义", null],
        "d4": ["⊢4=S(3)", "算数符号定义", null],
        "d5": ["⊢5=S(4)", "算数符号定义", null],
        "d6": ["⊢6=S(5)", "算数符号定义", null],
        "d7": ["⊢7=S(6)", "算数符号定义", null],
        "d8": ["⊢8=S(7)", "算数符号定义", null],
        "d9": ["⊢9=S(8)", "算数符号定义", null],
        "d10": ["⊢10=S(9)", "算数符号定义", null],
        "d+1": ["⊢($x+S($y))=S($x+$y)", "算数符号定义", null],
        "d+2": ["⊢($x+0)=$x", "算数符号定义", null],
        "d*1": ["⊢($x*0)=0", "算数符号定义", null],
        "d*2": ["⊢($x*S($y))=($x*$y+$x)", "算数符号定义", null],
        "dPrime": ["⊢Prime($x)<>~Ex:(~x=1&~x=$x&Ey:x*y=$x)", "算数符号定义", null],
        // macro library
        ".i": ["⊢$0>$0", "内置宏", [["a1", [], ["$0", "$0>$0"]], ["a1", [], ["$0", "$0"]], ["a2", [], ["$0", "$0>$0", "$0"]], ["mp", [-1, -3], []], ["mp", [-1, -3], []]]],
        ".t": ["$0>$1,$1>$2⊢$0>$2", "内置宏", [["a1", [], ["$1>$2", "$0"]], ["mp", [-1, 1], []], ["a2", [], ["$0", "$1", "$2"]], ["mp", [-1, -2], []], ["mp", [-1, 0], []]]],
        ".ne": ["⊢~~$0>$0", "内置宏", [["a1", [], ["~~$0", "~~~~$0"]], ["a3", [], ["~~~$0", "~$0"]], ["a3", [], ["$0", "~~$0"]], [".t", [-3, -2], []], [".t", [-1, -2], []], [".i", [], ["~~$0"]], ["a2", [], ["~~$0", "~~$0", "$0"]], ["mp", [-1, -3], []], ["mp", [-1, -3], []]]],
        ".ni": ["⊢$0>~~$0", "内置宏", [[".ne", [], ["~$0"]], ["a3", [], ["~~$0", "$0"]], ["mp", [-1, -2], []]]],
        ".cs": ["$0>($1>$2)⊢$1>($0>$2)", "内置宏", [["<a1", [0], ["$1"]], ["a1", [], ["$1", "$0"]], ["ccmp", [-2, -1], []]]],
        ".a30": ["⊢($0>$1)>(~$1>~$0)", "内置宏", [[".i", [], ["$0>$1"]], [".ne", [], ["$0"]], [".ni", [], ["$1"]], ["<a1", [-2], ["$0>$1"]], ["<a1", [-2], ["$0>$1"]], ["c.t", [-2, -5], []], ["c.t", [-1, -2], []], ["a3", [], ["~$0", "~$1"]], [".t", [-2, -1], []]]],
        ".a31": ["⊢(~$0>$1)>(~$1>$0)", "内置宏", [[".i", [], ["~$0>$1"]], [".ni", [], ["$1"]], ["<a1", [-1], ["~$0>$1"]], ["c.t", [-3, -1], []], ["a3", [], ["$0", "~$1"]], [".t", [-2, -1], []]]],
        ".a32": ["⊢($0>~$1)>($1>~$0)", "内置宏", [[".a30", [], ["$0", "~$1"]], ["c.ni", [], ["($0 > ~$1)", "$1"]], ["c.t", [-1, -2], []]]],
        ".m": ["$0,~$0⊢$1", "内置宏", [[".ni", [], ["$0"]], ["mp", [-1, 0], []], ["a1", [], ["~~$0", "~$1"]], ["mp", [-1, -2], []], ["a3", [], ["$1", "~$0"]], ["mp", [-1, -2], []], ["mp", [-1, 1], []]]],
        ".mn": ["⊢(~$0>$0)>$0", "内置宏", [["a1", [], ["~$0", "(~$0 > $0)"]], ["c.i", [], ["~$0", "(~$0 > $0)"]], ["ccmp", [-1, -2], []], ["c<.a30", [-1], []], ["<a2", [-1], []], [".i", [], ["~$0"]], ["mp", [-2, -1], []], ["<a3", [-1], []]]],
        ".m1": ["~$0>~$1,~$0>$1⊢$0", "内置宏", [["<.a31", [1], []], [".t", [0, -1], []], ["<.mn", [-1], []]]],
        ".m2": ["$0>$1,~$0>$1⊢$1", "内置宏", [["<.a30", [0], []], ["<.a31", [1], []], [".m1", [-2, -1], []]]],
        ".m&": ["$0,$1⊢~($0>~$1)", "内置宏", [[".i", [], ["($0 > ~$1)"]], ["a1", [], ["$0", "($0 > ~$1)"]], ["mp", [-1, 0], []], ["a2", [], ["($0 > ~$1)", "$0", "~$1"]], ["mp", [-1, -4], []], ["mp", [-1, -3], []], ["a3", [], ["~($0>~$1)", "$1"]], [".ne", [], ["$0>~$1"]], [".t", [-1, -3], []], ["mp", [-3, -1], []], ["mp", [-1, 1], []]]],
        ".m&1": ["⊢~($0>$1)>$0", "内置宏", [[">>.m", [], ["~$0", "$1"]], ["c.ni", [], ["~$0", "$0"]], ["c.t", [-1, -2], []], [".ni", [], ["$0>$1"]], [".t", [-2, -1], []], ["a3", [], ["$0", "~($0>$1)"]], ["mp", [-1, -2], []]]],
        ".m&2": ["⊢~($0>$1)>~$1", "内置宏", [["a1", [], ["$1", "$0"]], [".ne", [], ["$1"]], [".ni", [], ["$0>$1"]], [".t", [-2, -3], []], [".t", [-1, -2], []], ["a3", [], ["~$1", "~($0>$1)"]], ["mp", [-1, -2], []]]],
        ".pierce": ["⊢(($0>$1)>$0)>$0", "内置宏", [[".m&1", [], ["$0", "$1"]], [".i", [], ["($0>$1)>$0"]], ["<a1", [-2], ["($0>$1)>$0"]], ["c.m2", [-2, -1], []]]],
        ".<>": ["$0>$1,$1>$0⊢$0<>$1", "内置宏", [[".m&", [0, 1], []], ["d<>2", [], ["$0", "$1"]], ["mp", [-1, -2], []]]],
        ".<>1": ["⊢($0<>$1)>($0>$1)", "内置宏", [[".m&1", [], ["$0>$1", "~($1>$0)"]], ["d<>1", [], ["$0", "$1"]], [".t", [-1, -2], []]]],
        ".<>2": ["⊢($0<>$1)>($1>$0)", "内置宏", [[".m&2", [], ["$0>$1", "~($1>$0)"]], [".ne", [], ["$1>$0"]], [".t", [-2, -1], []], ["d<>1", [], ["$0", "$1"]], [".t", [-1, -2], []]]],
        ".<>i": ["⊢$0<>$0", "内置宏", [[".i", [], ["$0"]], [".<>", [-1, -1], []]]],
        ".<>s": ["$0<>$1⊢$1<>$0", "内置宏", [[".<>2", [], ["$0", "$1"]], [".<>1", [], ["$0", "$1"]], ["mp", [-1, 0], []], ["mp", [-3, 0], []], [".<>", [-1, -2], []]]],
        ".<>t": ["$0<>$1,$1<>$2⊢$0<>$2", "内置宏", [[".<>2", [], ["$0", "$1"]], [".<>1", [], ["$0", "$1"]], [".<>2", [], ["$1", "$2"]], [".<>1", [], ["$1", "$2"]], ["mp", [-4, 0], []], ["mp", [-4, 0], []], ["mp", [-4, 1], []], ["mp", [-4, 1], []], [".t", [-3, -1], []], [".t", [-3, -5], []], [".<>", [-2, -1], []]]],
        ".&": ["$0,$1⊢$0&$1", "内置宏", [[".m&", [0, 1], []], ["d&", [], ["$0", "$1"]], ["<<.<>2", [-1, -2], []]]],
        ".&1": ["$0&$1⊢$0", "内置宏", [["d&", [], ["$0", "$1"]], ["<<.<>1", [-1, 0], []], ["<.m&1", [-1], []]]],
        ".&2": ["$0&$1⊢$1", "内置宏", [["d&", [], ["$0", "$1"]], ["<<.<>1", [-1, 0], []], ["<.m&2", [-1], []], ["<.ne", [-1], []]]],
        ".&n1": ["~$0⊢~($0&$1)", "内置宏", [[">.&1", [], ["$0", "$1"]], ["<.a30", [-1], []], ["mp", [-1, 0], []]]],
        ".&n2": ["~$1⊢~($0&$1)", "内置宏", [[">.&2", [], ["$0", "$1"]], ["<.a30", [-1], []], ["mp", [-1, 0], []]]],
        ".&s": ["$0&$1⊢$1&$0", "内置宏", [[".&1", [0], []], [".&2", [0], []], [".&", [-1, -2], []]]],
        ".&a": ["($0&$1)&$2⊢$0&($1&$2)", "内置宏", [[".&1", [0], []], [".&2", [0], []], [".&2", [-2], []], [".&1", [-3], []], [".&", [-2, -3], []], [".&", [-2, -1], []]]],
        ".&m1": ["($0&$1)>$2⊢$0>($1>$2)", "内置宏", [["<a1", [0], ["$1"]], ["<a1", [-1], ["$0"]], [">>.&", [], ["$0", "$1"]], ["ccmp", [-2, -1], []]]],
        ".&m2": ["$0>($1>$2)⊢($0&$1)>$2", "内置宏", [["<a1", [0], ["$0&$1"]], [">.&1", [], ["$0", "$1"]], ["cmp", [-2, -1], []], [">.&2", [], ["$0", "$1"]], ["cmp", [-2, -1], []]]],
        ".|i": ["$0|$0⊢$0", "内置宏", [["d|", [], ["$0", "$0"]], ["<<.<>1", [-1, 0], []], ["<.mn", [-1], []]]],
        ".|1": ["$0⊢$0|$1", "内置宏", [[">.m", [0], ["$1"]], ["d|", [], ["$0", "$1"]], ["<<.<>2", [-1, -2], []]]],
        ".|2": ["$1⊢$0|$1", "内置宏", [["<a1", [0], ["~$0"]], ["d|", [], ["$0", "$1"]], ["<<.<>2", [-1, -2], []]]],
        ".|n": ["~$0,~$1⊢~($0|$1)", "内置宏", [[".m&", [0, 1], []], [".i", [], ["(~$0 > $1)"]], ["c.ni", [], ["~$0>$1", "$1"]], ["c.t", [-2, -1], []], ["<.a30", [-1], []], ["mp", [-1, -5], []], ["d|", [], ["$0", "$1"]], ["<.<>1", [-1], []], ["<.a30", [-1], []], ["mp", [-1, -4], []]]],
        ".|n1": ["~($0|$1)⊢~$0", "内置宏", [[">.|1", [], ["$0", "$1"]], ["<.a30", [-1], []], ["mp", [-1, 0], []]]],
        ".|n2": ["~($0|$1)⊢~$1", "内置宏", [[">.|2", [], ["$1", "$0"]], ["<.a30", [-1], []], ["mp", [-1, 0], []]]],
        ".|s": ["$0|$1⊢$1|$0", "内置宏", [["d|", [], ["$0", "$1"]], ["<<.<>1", [-1, 0], []], ["<.a31", [-1], []], ["d|", [], ["$1", "$0"]], ["<<.<>2", [-1, -2], []]]],
        ".|a": ["($0|$1)|$2⊢$0|($1|$2)", "内置宏", [["d|", [], ["$0", "$1"]], ["d|", [], ["$0|$1", "$2"]], ["<<.<>1", [-1, 0], []], ["<.<>1", [-3], []], ["<.a30", [-1], []], [".t", [-1, -3], []], ["<a1", [-1], ["~$1"]], ["<a1", [-1], ["~$0"]], [">>.m&", [], ["~$0", "~$1"]], ["ccc.ni", [], ["~$0", "~$1", "~$0>$1", "$1"]], ["cc.i", [], ["~$0", "~$1", "~$0>$1"]], ["ccc.t", [-1, -2], []], ["cc<.a30", [-1], []], ["ccmp", [-1, -5], []], ["ccmp", [-7, -1], []], ["d|", [], ["$1", "$2"]], ["<.<>2", [-1], []], [".t", [-3, -1], []], ["d|", [], ["$0", "$1|$2"]], ["<.<>2", [-1], []], ["mp", [-1, -3], []]]],
        ".|m": ["$0>$2,$1>$2⊢($0|$1)>$2", "内置宏", [["<a1", [1], ["~$0"]], ["<a2", [-1], []], ["<a1", [0], ["~$0>$1"]], ["c.m2", [-1, -2], []], ["d|", [], ["$0", "$1"]], ["<.<>1", [-1], []], [".t", [-1, -3], []]]],
        ".n|&": ["~($0|$1)⊢~$0&~$1", "内置宏", [[".|n1", [0], []], [".|n2", [0], []], [".&", [-2, -1], []]]],
        ".nn|&": ["~$0|~$1⊢~($0&$1)", "内置宏", [["d|", [], ["~$0", "~$1"]], ["<<.<>1", [-1, 0], []], ["<a3", [-1], []], ["d&", [], ["$0", "$1"]], ["<.<>1", [-1], []], ["<.a32", [-1], []], ["<.a32", [-4], []], ["mp", [-2, -1], []]]],
        ".n&|": ["~($0&$1)⊢~$0|~$1", "内置宏", [["d&", [], ["$0", "$1"]], ["<.<>2", [-1], []], ["<.a31", [-1], []], ["mp", [-1, 0], []], [".ne", [], ["$0"]], [".t", [-1, -2], []], ["d|", [], ["~$0", "~$1"]], ["<<.<>2", [-1, -2], []]]],
        ".nn&|": ["~$0&~$1⊢~($0|$1)", "内置宏", [[".&1", [0], []], [".&2", [0], []], [".|n", [-2, -1], []]]],
        ".|nn&": ["$0|$1⊢~(~$0&~$1)", "内置宏", [[">.nn&|", [], ["$0", "$1"]], ["<.a32", [-1], []], ["mp", [-1, 0], []]]],
        ".&nn|": ["$0&$1⊢~(~$0|~$1)", "内置宏", [[">.nn|&", [], ["$0", "$1"]], ["<.a32", [-1], []], ["mp", [-1, 0], []]]],
        ".<>d": ['⊢(($0<>$1)<>~(($0>$1)>~($1>$0)))', "内置宏", [["d<>1", [], ["$0", "$1"]], ["d<>2", [], ["$0", "$1"]], [".<>", [-2, -1], []]]],
        ".n": ["⊢$0<>~~$0", "内置宏", [[".ne", [], ["$0"]], [".ni", [], ["$0"]], [".<>", [-1, -2], []]]],
        ".<>r>": ["$a1<>$a2,$b1<>$b2⊢($a1>$b1)<>($a2>$b2)", "内置宏", [[".i", [], ["$a1>$b1"]], [".<>2", [], ["$a1", "$a2"]], ["mp", [-1, 0], []], ["a1", [], ["$a2>$a1", "$a1>$b1"]], ["mp", [-1, -2], []], [".<>1", [], ["$b1", "$b2"]], ["mp", [-1, 1], []], ["a1", [], ["$b1>$b2", "$a1>$b1"]], ["mp", [-1, -2], []], ["c.t", [-5, -9], []], ["c.t", [-1, -2], []], [".i", [], ["$a2>$b2"]], [".<>1", [], ["$a1", "$a2"]], ["mp", [-1, 0], []], [".<>2", [], ["$b1", "$b2"]], ["mp", [-1, 1], []], ["a1", [], ["$b2>$b1", "$a2>$b2"]], ["mp", [-1, -2], []], ["a1", [], ["$a1>$a2", "$a2>$b2"]], ["mp", [-1, -6], []], ["c.t", [-1, -9], []], ["c.t", [-1, -4], []], [".<>", [-12, -1], []]]],
        ".<>r~": ["$0<>$1⊢~$0<>~$1", "内置宏", [[".<>2", [], ["$0", "$1"]], [".<>1", [], ["$0", "$1"]], ["mp", [-1, 0], []], ["mp", [-3, 0], []], [".ne", [], ["$0"]], [".ni", [], ["$1"]], [".t", [-2, -4], []], [".t", [-1, -2], []], ["a3", [], ["~$0", "~$1"]], ["mp", [-1, -2], []], [".ne", [], ["$1"]], [".ni", [], ["$0"]], [".t", [-2, -9], []], [".t", [-1, -2], []], ["a3", [], ["~$1", "~$0"]], ["mp", [-1, -2], []], [".<>", [-1, -7], []]]],
        ".<>r<>": ["$a1<>$a2,$b1<>$b2⊢($a1<>$b1)<>($a2<>$b2)", "内置宏", [[".<>s", [0], []], [".<>s", [1], []], [".i", [], ["$a1<>$b1"]], ["a1", [], ["$a2<>$a1", "$a1<>$b1"]], ["a1", [], ["$b1<>$b2", "$a1<>$b1"]], ["mp", [-1, 1], []], ["mp", [-3, -6], []], ["c.<>t", [-1, -5], []], ["c.<>t", [-1, -3], []], [".i", [], ["$a2<>$b2"]], ["a1", [], ["$a1<>$a2", "$a2<>$b2"]], ["a1", [], ["$b2<>$b1", "$a2<>$b2"]], ["mp", [-2, 0], []], ["mp", [-2, -12], []], ["c.<>t", [-2, -5], []], ["c.<>t", [-1, -2], []], [".<>", [-8, -1], []]]],
        ".<>r&": ["$a1<>$a2,$b1<>$b2⊢($a1&$b1)<>($a2&$b2)", "内置宏", [["d&", [], ["$a1", "$b1"]], [".<>r~", [1], []], [".<>r>", [0, -1], []], [".<>r~", [-1], []], [".<>t", [-4, -1], []], ["d&", [], ["$a2", "$b2"]], [".<>s", [-1], []], [".<>t", [-3, -1], []]]],
        ".<>r|": ["$a1<>$a2,$b1<>$b2⊢($a1|$b1)<>($a2|$b2)", "内置宏", [["d|", [], ["$a1", "$b1"]], ["d|", [], ["$a2", "$b2"]], [".<>r~", [0], []], [".<>r>", [-1, 1], []], [".<>s", [-3], []], [".<>t", [-5, -2], []], [".<>t", [-1, -2], []]]],
        ".<>rV": ["⊢(V$2:($0<>$1))>((V$2:$0)<>(V$2:$1))", "内置宏", [["v.<>1", [], ["$2", "$0", "$1"]], ["v.<>2", [], ["$2", "$0", "$1"]], ["<a5", [-2], []], ["<a5", [-2], []], ["c<a5", [-2], []], ["c<a5", [-2], []], ["c.<>", [-2, -1], []]]],
        ".<>rE": ["~(V$2:~$0)<>~(V$2:~$1)⊢(E$2:$0)<>(E$2:$1)", "内置宏", [["dE", [], ["$2", "$0"]], ["dE", [], ["$2", "$1"]], [".<>s", [-1], []], [".<>t", [-3, 0], []], [".<>t", [-1, -2], []]]],
        ".>TF": ["$0,~$1⊢~($0>$1)", "内置宏", [[".m&", [0, 1], []], [".i", [], ["($0 > $1)"]], ["c.ni", [], ["($0 > $1)", "$1"]], ["c.t", [-2, -1], []], ["<.a30", [-1], []], ["mp", [-1, -5], []]]],
        ".>FU": ["~$0⊢$0>$1", "内置宏", [["<a1", [0], ["~$1"]], ["<a3", [-1], []]]],
        ".<>TT": ["$0,$1⊢$0<>$1", "内置宏", [["<a1", [1], ["$0"]], ["<a1", [0], ["$1"]], [".<>", [-2, -1], []]]],
        ".<>FF": ["~$0,~$1⊢$0<>$1", "内置宏", [["<a1", [1], ["~$0"]], ["<a1", [0], ["~$1"]], ["<a3", [-2], []], ["<a3", [-2], []], [".<>", [-1, -2], []]]],
        ".<>TF": ["$0,~$1⊢~($0<>$1)", "内置宏", [[".>TF", [0, 1], []], ["d<>1", [], ["$0", "$1"]], [".ne", [], ["$0<>$1"]], [".t", [-1, -2], []], ["<a3", [-1], []], ["<a1", [-5], ["$1>$0"]], [".ne", [], ["$1>$0"]], [".t", [-1, -2], []], ["<a3", [-1], []], ["mp", [-5, -1], []]]],
        ".<>FT": ["~$0,$1⊢~($0<>$1)", "内置宏", [[".<>TF", [1, 0], []], [">.<>s", [], ["$0", "$1"]], ["<.a30", [-1], []], ["mp", [-1, -3], []]]],
        ".nEVn": ["⊢~(E$0:$1)<>(V$0:~$1)", "内置宏", [["dE", [], ["$0", "$1"]], [".<>r~", [-1], []], [".n", [], ["(V$0:~$1)"]], [".<>s", [-1], []], [".<>t", [-3, -1], []]]],
        ".nVVn": ["⊢(E$2:(E$0:$1))<>~(V$2:(V$0:~$1))", "内置宏", [["v.nEVn", [], ["$2", "$0", "$1"]], ["<.<>rV", [-1], []], [".<>r~", [-1], []], ["dE", [], ["$2", "(E$0:$1)"]], [".<>t", [-1, -2], []]]],
        ".Ve": ["(V$0:$1)⊢$1", "内置宏", [["<a4", [0], ["$0"]]]],
        ".Vs": ["(V$0:(V$1:$2))⊢(V$1:(V$0:$2))", "内置宏", [["a6", [], ["(V$0:(V$1:#vvnf($2,$1,$0,$1,$0)))", "$1"]], ["mp", [-1, 0], []], ["va6", [], ["$1", "(V$0:(V$1:#vvnf(#vvnf($2,$1,$0,$1,$0),$1,$0,$0)))", "$0"]], ["vmp", [-1, -2], []], ["vv.Ve", [-1], []], ["vv.Ve", [-1], []]]],
        ".V&1": ["(V$0:($1&$2))⊢(V$0:$1)&(V$0:$2)", "内置宏", [["v.&1", [0], []], ["v.&2", [0], []], [".&", [-2, -1], []]]],
        ".V&2": ["(V$0:$1)&(V$0:$2)⊢(V$0:($1&$2))", "内置宏", [[".&1", [0], []], [".&2", [0], []], ["v.&", [-2, -1], []]]],
        ".Es": ["⊢(E$0:(E$2:$1))<>(E$2:(E$0:$1))", "内置宏", [[".VV", [], ["$2", "$0", "~$1"]], [".dEE", [], ["$2", "$0", "$1"]], [".<>r~", [-2], []], [".dEE", [], ["$2", "$0", "$1"]], [".dEE", [], ["$0", "$2", "$1"]], [".<>4", [-3], []], [".<>4", [-3], []], [".<>5", [-3, -2], []], [".<>5", [-1, -2], []]]],
        ".EV": ["⊢(E$x:(V$y:$0))>(V$y:(E$x:$0))", "内置宏", [["vva4", [], ["$y", "$x", "$y", "$0", "$y"]], ["vv.a31", [], ["$y", "$x", "(V$y:$0)", "$0"]], ["vv.<>1", [], ["$y", "$x", "(V$y:$0)>$0", "~$0>~(V$y:$0)"]], ["vvmp", [-1, -2], []], ["vvmp", [-1, -4], []], ["v<a5", [-1], []], ["v.a31", [], ["$y", "(V$x:~$0)", "(V$x:~(V$y:$0))"]], ["v<.<>1", [-1], []], ["vmp", [-1, -3], []], ["<a5", [-1], []], ["a6", [], ["~(V$x:~(V$y:$0))", "$y"]], [".d1", [-1, -2], []], ["dE", [], ["$x", "(V$y:$0)"]], ["vdE", [], ["$y", "$x", "$0"]], ["<.<>rV", [-1], []], [".<>r>", [-3, -1], []], ["<.<>2", [-1], []], ["mp", [-1, -6], []]]],
        // ".a3TF": ["$0>$1,~$0>$1⊢$1", "内置宏", [[".a31", [], ["$0", "$1"]], ["<.<>1", [-1], []], ["mp", [-1, 0], []], [".d1", [-1, 1], []], ["a1", [], ["~$1", "~$1>$1"]], ["c.i", [], ["~$1", "~$1>$1"]], ["ccmp", [-1, -2], []], [".a31", [], ["~$1>$1", "$1"]], ["<.<>1", [-1], []], [".d1", [-3, -1], []], [".i", [], ["~$1"]], ["a2", [], ["~$1", "~$1", "~(~$1>$1)"]], ["mp", [-1, -3], []], ["mp", [-1, -3], []], ["<a3", [-1], []], ["mp", [-1, -12], []]]],
        // ".|TU": ["$0⊢$0|$1", "内置宏", [["d|", [], ["$0", "$1"]], [">.m", [0], ["$1"]], ["<.<>2", [-2], []], ["mp", [-1, -2], []]]],
        // ".|UT": ["$1⊢$0|$1", "内置宏", [["d|", [], ["$0", "$1"]], ["<a1", [0], ["~$0"]], ["<.<>2", [-2], []], ["mp", [-1, -2], []]]],
        // ".|FF": ["~$0,~$1⊢~($0|$1)", "内置宏", [["d|", [], ["$0", "$1"]], [".>TF", [0, 1], []], ["<.<>1", [-2], []], [".a31", [], ["$0|$1", "~$0>$1"]], ["<.<>1", [-1], []], ["mp", [-1, -3], []], ["mp", [-1, -5], []]]],
        // ".&TT": ["$0,$1⊢$0&$1", "内置宏", [[".m1", [0, 1], []], ["d&", [], ["$0", "$1"]], ["<.<>2", [-1], []], ["mp", [-1, -3], []]]],
        // ".&FU": ["~$0⊢~($0&$1)", "内置宏", [[".m2", [], ["$0", "~$1"]], [".a32", [], ["$0>~$1", "$0"]], ["<.<>1", [-1], []], ["mp", [-1, -3], []], ["mp", [-1, 0], []], ["d&", [], ["$0", "$1"]], ["<.<>1", [-1], []], [".dne", [], ["$0&$1"]], [".d1", [-1, -2], []], ["<a3", [-1], []], ["mp", [-1, -6], []]]],
        // ".&UF": ["~$1⊢~($0&$1)", "内置宏", [[".m3", [], ["$0", "~$1"]], ["<a3", [-1], []], ["mp", [-1, 0], []], ["d&", [], ["$0", "$1"]], ["<.<>1", [-1], []], [".dne", [], ["$0&$1"]], [".d1", [-1, -2], []], ["<a3", [-1], []], ["mp", [-1, -6], []]]]
        // ".i": ["⊢$0>$0", "内置宏", [["a1", [], ["$0", "$0>$0"]], ["a1", [], ["$0", "$0"]], ["a2", [], ["$0", "$0>$0", "$0"]], ["mp", [-1, -3], []], ["mp", [-1, -3], []]]],
        // ".d1": ["$0>$1,$1>$2⊢$0>$2", "内置宏", [["a1", [], ["$1>$2", "$0"]], ["mp", [-1, 1], []], ["a2", [], ["$0", "$1", "$2"]], ["mp", [-1, -2], []], ["mp", [-1, 0], []]]],
        // ".d2": ["$0>($1>$2),$1⊢$0>$2", "内置宏", [["a1", [], ["$1", "$0"]], ["mp", [-1, 1], []], ["a2", [], ["$0", "$1", "$2"]], ["mp", [-1, 0], []], ["mp", [-1, -3], []]]],
        // ".dne": ["⊢~~$0>$0", "内置宏", [["a1", [], ["~~$0", "~~~~$0"]], ["a3", [], ["~~~$0", "~$0"]], ["a3", [], ["$0", "~~$0"]], [".d1", [-3, -2], []], [".d1", [-1, -2], []], [".i", [], ["~~$0"]], ["a2", [], ["~~$0", "~~$0", "$0"]], ["mp", [-1, -3], []], ["mp", [-1, -3], []]]],
        // ".dni": ["⊢$0>~~$0", "内置宏", [[".dne", [], ["~$0"]], ["a3", [], ["~~$0", "$0"]], ["mp", [-1, -2], []]]],
        // ".dn": ["⊢$0<>~~$0", "内置宏", [[".dne", [], ["$0"]], [".dni", [], ["$0"]], [".<>0", [-1, -2], []]]],
        // ".m0": ["$0,~$0⊢$1", "内置宏", [[".dni", [], ["$0"]], ["mp", [-1, 0], []], ["a1", [], ["~~$0", "~$1"]], ["mp", [-1, -2], []], ["a3", [], ["$1", "~$0"]], ["mp", [-1, -2], []], ["mp", [-1, 1], []]]],
        // ".m1": ["$0,$1⊢~($0>~$1)", "内置宏", [[".i", [], ["$0>~$1"]], [".d2", [-1, 0], []], ["a3", [], ["~($0>~$1)", "$1"]], [".dne", [], ["$0>~$1"]], [".d1", [-1, -3], []], ["mp", [-3, -1], []], ["mp", [-1, 1], []]]],
        // ".m2": ["⊢~($0>$1)>$0", "内置宏", [[">>.m0", [], ["~$0", "$1"]], ["c.dni", [], ["~$0", "$0"]], ["c.d1", [-1, -2], []], [".dni", [], ["$0>$1"]], [".d1", [-2, -1], []], ["a3", [], ["$0", "~($0>$1)"]], ["mp", [-1, -2], []]]],
        // ".m3": ["⊢~($0>$1)>~$1", "内置宏", [["a1", [], ["$1", "$0"]], [".dne", [], ["$1"]], [".dni", [], ["$0>$1"]], [".d1", [-2, -3], []], [".d1", [-1, -2], []], ["a3", [], ["~$1", "~($0>$1)"]], ["mp", [-1, -2], []]]],
        // ".<>0": ["$0>$1,$1>$0⊢$0<>$1", "内置宏", [[".m1", [0, 1], []], ["d<>2", [], ["$0", "$1"]], ["mp", [-1, -2], []]]],
        // ".<>1": ["⊢($0<>$1)>($0>$1)", "内置宏", [[".m2", [], ["$0>$1", "~($1>$0)"]], ["d<>1", [], ["$0", "$1"]], [".d1", [-1, -2], []]]],
        // ".<>2": ["⊢($0<>$1)>($1>$0)", "内置宏", [[".m3", [], ["$0>$1", "~($1>$0)"]], [".dne", [], ["$1>$0"]], [".d1", [-2, -1], []], ["d<>1", [], ["$0", "$1"]], [".d1", [-1, -2], []]]],
        // ".<>3": ["⊢$0<>$0", "内置宏", [[".i", [], ["$0"]], [".<>0", [-1, -1], []]]],
        // ".<>4": ["$0<>$1⊢$1<>$0", "内置宏", [[".<>2", [], ["$0", "$1"]], [".<>1", [], ["$0", "$1"]], ["mp", [-1, 0], []], ["mp", [-3, 0], []], [".<>0", [-1, -2], []]]],
        // ".<>5": ["$0<>$1,$1<>$2⊢$0<>$2", "内置宏", [[".<>2", [], ["$0", "$1"]], [".<>1", [], ["$0", "$1"]], [".<>2", [], ["$1", "$2"]], [".<>1", [], ["$1", "$2"]], ["mp", [-4, 0], []], ["mp", [-4, 0], []], ["mp", [-4, 1], []], ["mp", [-4, 1], []], [".d1", [-3, -1], []], [".d1", [-3, -5], []], [".<>0", [-2, -1], []]]],
        // ".<>d": ['⊢(($0<>$1)<>~(($0>$1)>~($1>$0)))', "内置宏", [["d<>1", [], ["$0", "$1"]], ["d<>2", [], ["$0", "$1"]], [".<>0", [-2, -1], []]]],
        // ".<>r>": ["$a1<>$a2,$b1<>$b2⊢($a1>$b1)<>($a2>$b2)", "内置宏", [[".i", [], ["$a1>$b1"]], [".<>2", [], ["$a1", "$a2"]], ["mp", [-1, 0], []], ["a1", [], ["$a2>$a1", "$a1>$b1"]], ["mp", [-1, -2], []], [".<>1", [], ["$b1", "$b2"]], ["mp", [-1, 1], []], ["a1", [], ["$b1>$b2", "$a1>$b1"]], ["mp", [-1, -2], []], ["c.d1", [-5, -9], []], ["c.d1", [-1, -2], []], [".i", [], ["$a2>$b2"]], [".<>1", [], ["$a1", "$a2"]], ["mp", [-1, 0], []], [".<>2", [], ["$b1", "$b2"]], ["mp", [-1, 1], []], ["a1", [], ["$b2>$b1", "$a2>$b2"]], ["mp", [-1, -2], []], ["a1", [], ["$a1>$a2", "$a2>$b2"]], ["mp", [-1, -6], []], ["c.d1", [-1, -9], []], ["c.d1", [-1, -4], []], [".<>0", [-12, -1], []]]],
        // ".<>r~": ["$0<>$1⊢~$0<>~$1", "内置宏", [[".<>2", [], ["$0", "$1"]], [".<>1", [], ["$0", "$1"]], ["mp", [-1, 0], []], ["mp", [-3, 0], []], [".dne", [], ["$0"]], [".dni", [], ["$1"]], [".d1", [-2, -4], []], [".d1", [-1, -2], []], ["a3", [], ["~$0", "~$1"]], ["mp", [-1, -2], []], [".dne", [], ["$1"]], [".dni", [], ["$0"]], [".d1", [-2, -9], []], [".d1", [-1, -2], []], ["a3", [], ["~$1", "~$0"]], ["mp", [-1, -2], []], [".<>0", [-1, -7], []]]],
        // ".<>r<>": ["$a1<>$a2,$b1<>$b2⊢($a1<>$b1)<>($a2<>$b2)", "内置宏", [[".<>4", [0], []], [".<>4", [1], []], [".i", [], ["$a1<>$b1"]], ["a1", [], ["$a2<>$a1", "$a1<>$b1"]], ["a1", [], ["$b1<>$b2", "$a1<>$b1"]], ["mp", [-1, 1], []], ["mp", [-3, -6], []], ["c.<>5", [-1, -5], []], ["c.<>5", [-1, -3], []], [".i", [], ["$a2<>$b2"]], ["a1", [], ["$a1<>$a2", "$a2<>$b2"]], ["a1", [], ["$b2<>$b1", "$a2<>$b2"]], ["mp", [-2, 0], []], ["mp", [-2, -12], []], ["c.<>5", [-2, -5], []], ["c.<>5", [-1, -2], []], [".<>0", [-8, -1], []]]],
        // ".<>r&": ["$a1<>$a2,$b1<>$b2⊢($a1&$b1)<>($a2&$b2)", "内置宏", [["d&", [], ["$a1", "$b1"]], [".<>r~", [1], []], [".<>r>", [0, -1], []], [".<>r~", [-1], []], [".<>5", [-4, -1], []], ["d&", [], ["$a2", "$b2"]], [".<>4", [-1], []], [".<>5", [-3, -1], []]]],
        // ".<>r|": ["$a1<>$a2,$b1<>$b2⊢($a1|$b1)<>($a2|$b2)", "内置宏", [["d|", [], ["$a1", "$b1"]], ["d|", [], ["$a2", "$b2"]], [".<>r~", [0], []], [".<>r>", [-1, 1], []], [".<>4", [-3], []], [".<>5", [-5, -2], []], [".<>5", [-1, -2], []]]],
        // ".<>rV": ["⊢(V$2:($0<>$1))>((V$2:$0)<>(V$2:$1))", "内置宏", [["v.<>1", [], ["$2", "$0", "$1"]], ["v.<>2", [], ["$2", "$0", "$1"]], ["<a5", [-2], []], ["<a5", [-2], []], ["c<a5", [-2], []], ["c<a5", [-2], []], ["c.<>0", [-2, -1], []]]],
        // ".<>rE": ["~(V$2:~$0)<>~(V$2:~$1)⊢(E$2:$0)<>(E$2:$1)", "内置宏", [["dE", [], ["$2", "$0"]], ["dE", [], ["$2", "$1"]], [".<>4", [-1], []], [".<>5", [-3, 0], []], [".<>5", [-1, -2], []]]],
        // ".a31": ["⊢($0>$1)<>(~$1>~$0)", "内置宏", [[".i", [], ["$0>$1"]], [".dne", [], ["$0"]], [".dni", [], ["$1"]], ["<a1", [-2], ["$0>$1"]], ["<a1", [-2], ["$0>$1"]], ["c.d1", [-2, -5], []], ["c.d1", [-1, -2], []], ["a3", [], ["~$0", "~$1"]], [".d1", [-2, -1], []], ["a3", [], ["$1", "$0"]], [".<>0", [-2, -1], []]]],
        // ".a32": ["⊢(~$0>$1)<>(~$1>$0)", "内置宏", [[".i", [], ["~$0>$1"]], [".dni", [], ["$1"]], ["<a1", [-1], ["~$0>$1"]], ["c.d1", [-3, -1], []], ["a3", [], ["$0", "~$1"]], [".d1", [-2, -1], []], [".i", [], ["~$1>$0"]], [".dni", [], ["$0"]], ["<a1", [-1], ["~$1>$0"]], ["c.d1", [-3, -1], []], ["a3", [], ["$1", "~$0"]], [".d1", [-2, -1], []], [".<>0", [-7, -1], []]]],
        // ".~EV~": ["⊢~(E$0:$1)<>(V$0:~$1)", "内置宏", [["dE", [], ["$0", "$1"]], [".<>r~", [-1], []], [".dn", [], ["(V$0:~$1)"]], [".<>4", [-1], []], [".<>5", [-3, -1], []]]],
        // ".dEE": ["⊢(E$2:(E$0:$1))<>~(V$2:(V$0:~$1))", "内置宏", [["v.~EV~", [], ["$2", "$0", "$1"]], ["<.<>rV", [-1], []], [".<>r~", [-1], []], ["dE", [], ["$2", "(E$0:$1)"]], [".<>5", [-1, -2], []]]],
        // ".VVe": ["(V$1:(V$2:$3))⊢$3", "内置宏", [["a4", [], ["$1", "(V$2:$3)", "$1"]], ["a4", [], ["$2", "$3", "$2"]], ["mp", [-2, 0], []], ["mp", [-2, -1], []]]],
        // ".VV": ["⊢(V$1:(V$2:$3))<>(V$2:(V$1:$3))", "内置宏", [[">uu.VVe", [], ["$1", "$2", "$3", "$2", "$1"]], [">uu.VVe", [], ["$2", "$1", "$3", "$1", "$2"]], [".<>0", [-2, -1], []]]],
        // ".EE": ["⊢(E$0:(E$2:$1))<>(E$2:(E$0:$1))", "内置宏", [[".VV", [], ["$2", "$0", "~$1"]], [".dEE", [], ["$2", "$0", "$1"]], [".<>r~", [-2], []], [".dEE", [], ["$2", "$0", "$1"]], [".dEE", [], ["$0", "$2", "$1"]], [".<>4", [-3], []], [".<>4", [-3], []], [".<>5", [-3, -2], []], [".<>5", [-1, -2], []]]],
        // ".EV": ["⊢(E$x:(V$y:$0))>(V$y:(E$x:$0))", "内置宏", [["vva4", [], ["$y", "$x", "$y", "$0", "$y"]], ["vv.a31", [], ["$y", "$x", "(V$y:$0)", "$0"]], ["vv.<>1", [], ["$y", "$x", "(V$y:$0)>$0", "~$0>~(V$y:$0)"]], ["vvmp", [-1, -2], []], ["vvmp", [-1, -4], []], ["v<a5", [-1], []], ["v.a31", [], ["$y", "(V$x:~$0)", "(V$x:~(V$y:$0))"]], ["v<.<>1", [-1], []], ["vmp", [-1, -3], []], ["<a5", [-1], []], ["a6", [], ["~(V$x:~(V$y:$0))", "$y"]], [".d1", [-1, -2], []], ["dE", [], ["$x", "(V$y:$0)"]], ["vdE", [], ["$y", "$x", "$0"]], ["<.<>rV", [-1], []], [".<>r>", [-3, -1], []], ["<.<>2", [-1], []], ["mp", [-1, -6], []]]],
        // ".>TF": ["$0,~$1⊢~($0>$1)", "内置宏", [[".m1", [0, 1], []], [".dni", [], ["$1"]], ["<a1", [-1], ["$0>$1"]], [".i", [], ["$0>$1"]], ["c.d1", [-1, -2], []], [".a31", [], ["$0>$1", "$0>~~$1"]], ["<.<>1", [-1], []], ["mp", [-1, -3], []], ["mp", [-1, -8], []]]],
        // ".>FU": ["~$0⊢$0>$1", "内置宏", [["<a1", [0], ["~$1"]], ["<a3", [-1], []]]],
        // ".a3TF": ["$0>$1,~$0>$1⊢$1", "内置宏", [[".a31", [], ["$0", "$1"]], ["<.<>1", [-1], []], ["mp", [-1, 0], []], [".d1", [-1, 1], []], ["a1", [], ["~$1", "~$1>$1"]], ["c.i", [], ["~$1", "~$1>$1"]], ["ccmp", [-1, -2], []], [".a31", [], ["~$1>$1", "$1"]], ["<.<>1", [-1], []], [".d1", [-3, -1], []], [".i", [], ["~$1"]], ["a2", [], ["~$1", "~$1", "~(~$1>$1)"]], ["mp", [-1, -3], []], ["mp", [-1, -3], []], ["<a3", [-1], []], ["mp", [-1, -12], []]]],
        // ".<>TT": ["$0,$1⊢$0<>$1", "内置宏", [["<a1", [1], ["$0"]], ["<a1", [0], ["$1"]], [".<>0", [-2, -1], []]]],
        // ".<>FF": ["~$0,~$1⊢$0<>$1", "内置宏", [["<a1", [1], ["~$0"]], ["<a1", [0], ["~$1"]], ["<a3", [-2], []], ["<a3", [-2], []], [".<>0", [-1, -2], []]]],
        // ".<>TF": ["$0,~$1⊢~($0<>$1)", "内置宏", [[".>TF", [0, 1], []], ["d<>1", [], ["$0", "$1"]], [".dne", [], ["$0<>$1"]], [".d1", [-1, -2], []], ["<a3", [-1], []], ["<a1", [-5], ["$1>$0"]], [".dne", [], ["$1>$0"]], [".d1", [-1, -2], []], ["<a3", [-1], []], ["mp", [-5, -1], []]]],
        // ".<>FT": ["~$0,$1⊢~($0<>$1)", "内置宏", [[".<>TF", [1, 0], []], [">.<>4", [], ["$0", "$1"]], [".a31", [], ["$0<>$1", "$1<>$0"]], ["<.<>1", [-1], []], ["mp", [-1, -3], []], ["mp", [-1, -5], []]]],
        // ".|TU": ["$0⊢$0|$1", "内置宏", [["d|", [], ["$0", "$1"]], [">.m0", [0], ["$1"]], ["<.<>2", [-2], []], ["mp", [-1, -2], []]]],
        // ".|UT": ["$1⊢$0|$1", "内置宏", [["d|", [], ["$0", "$1"]], ["<a1", [0], ["~$0"]], ["<.<>2", [-2], []], ["mp", [-1, -2], []]]],
        // ".|FF": ["~$0,~$1⊢~($0|$1)", "内置宏", [["d|", [], ["$0", "$1"]], [".>TF", [0, 1], []], ["<.<>1", [-2], []], [".a31", [], ["$0|$1", "~$0>$1"]], ["<.<>1", [-1], []], ["mp", [-1, -3], []], ["mp", [-1, -5], []]]],
        // ".&TT": ["$0,$1⊢$0&$1", "内置宏", [[".m1", [0, 1], []], ["d&", [], ["$0", "$1"]], ["<.<>2", [-1], []], ["mp", [-1, -3], []]]],
        // ".&FU": ["~$0⊢~($0&$1)", "内置宏", [[".m2", [], ["$0", "~$1"]], [".a32", [], ["$0>~$1", "$0"]], ["<.<>1", [-1], []], ["mp", [-1, -3], []], ["mp", [-1, 0], []], ["d&", [], ["$0", "$1"]], ["<.<>1", [-1], []], [".dne", [], ["$0&$1"]], [".d1", [-1, -2], []], ["<a3", [-1], []], ["mp", [-1, -6], []]]],
        // ".&UF": ["~$1⊢~($0&$1)", "内置宏", [[".m3", [], ["$0", "~$1"]], ["<a3", [-1], []], ["mp", [-1, 0], []], ["d&", [], ["$0", "$1"]], ["<.<>1", [-1], []], [".dne", [], ["$0&$1"]], [".d1", [-1, -2], []], ["<a3", [-1], []], ["mp", [-1, -6], []]]]
    };
    const intMacros = {
        "cmp": ["$2>($0>$1),$2>$0⊢$2>$1", "元规则生成*", [["a2", [], ["$2", "$0", "$1"]], ["mp", [-1, 0], []], ["mp", [-1, 1], []]]],
        "vmp": ["(V$2:($0>$1)),(V$2:$0)⊢(V$2:$1)", "元规则生成*", [["a5", [], ["$2", "$0", "$1"]], ["mp", [-1, 0], []], ["mp", [-1, 1], []]]],
        "ump": ["#nf($0,$2)>#nf($1,$2),#nf($0,$2)⊢(V$2:#nf($1,$2))", "元规则生成*", [["mp", [0, 1], []], ["a6", [], ["$1", "$2"]], ["mp", [-1, -2], []]]],
    };
    const consts = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "{}"];
    const fns = ["Union", "Pow", "S"];
    const sp = new SavesParser();
    sp.deserializeArr(fs, [consts, fns, sysAxioms, null]);
    if (creative)
        return sp.deserializeArr(fs, [[], [], intMacros, Object.keys(sysAxioms)]);
    return sp.deserializeArr(fs, [[], [], intMacros, ["mp", "a1", "a2"]]);
}
//# sourceMappingURL=initial.js.map