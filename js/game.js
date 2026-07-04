import { ASTMgr } from "./fs/astmgr.js";
import { FSGui } from "./fs/gui.js";
import { Rotor } from "./hy/algebra.js";
import { HyperGui } from "./hy/gui.js";
import { TileBlockType } from "./hy/maploader.js";
import { calcMaxReachOrd, cmp, printOrd } from "./hy/ordinal.js";
import { langMgr, TR } from "./lang.js";
import { GameSaveLoad } from "./saveload.js";
import { Assist } from "./tt/assist.js";
import { TTGui } from "./tt/gui.js";
function parseDeductriumAmout(str) {
    let coeff;
    if (str.endsWith("µg"))
        coeff = 1;
    else if (str.endsWith("mg"))
        coeff = 1e3;
    else if (str.endsWith("kg"))
        coeff = 1e9;
    else if (str.endsWith("g"))
        coeff = 1e6;
    else if (str.endsWith("T"))
        coeff = 1e12;
    return Number(str.replaceAll(/[a-zA-Zµ]+/g, "")) * coeff;
}
export function stringifyDeductriumAmout(n) {
    const absn = Math.abs(n);
    if (absn > 1e12) {
        return n / 1e12 + "T";
    }
    if (absn > 1e9) {
        return n / 1e9 + "kg";
    }
    if (absn > 1e6) {
        return n / 1e6 + "g";
    }
    if (absn > 1e3) {
        return n / 1e3 + "mg";
    }
    return n + "µg";
}
export class Game {
    fsGui;
    hyperGui;
    ttGui;
    rewards = [];
    deductriums = 0; //ug
    destructedGates = 0;
    parcours = 1;
    consumed = 0;
    maxOrd = [];
    nextOrd = [1];
    ordBase = 15;
    creative = false;
    achievementsTable = {
        "aa": "我推出我", "delgate": "收费站拆除", ".i": "你推出你，他推出他（⊢$0>$0）", "progL": "解锁了成就",
        "hyp": "If I were..", "mdt": "会跑的“⊢”（演绎元定理）", "neg": "敢于说不", ".dne": "负负得正", "exfalso1": "否定爆炸", "exfalso2": "否定爆炸",
        "iff": "我推出你，你推出我（<>）", "andor": "逻辑门（与/或）", "pierce": "皮尔士定律((p>q)>p)>p", "lem": "排中律是真的！(p|~p)", "contra": "没毛病！~( p & ~p )", "mcpt": "命题逻辑自动推理",
        "1st": "一阶逻辑", "nf": "约束与自由", "rp": "丢掉量词，尽情替换！", "a7": "众生平等", "mvt": "概括一切（概括元定理）",
        ".prop": "命题逻辑大礼包", "mifft": "替换一切（互推替换元定理）", ".1st": "一阶逻辑大礼包", "terr1": "割让量词的领土", "terr2": "割让量词的领土",
        "mnt": "准备改名换姓", "elV1": "量词连连消消乐", "elV2": "量词连连消消乐", "elV3": "量词连连消消乐",
        "peano": "皮亚诺公理", "1+1": "1+1=2", "2x2": "2*2=4", "commu+": "加法交换律", "xdistr": "乘法分配率", "3<4": "3小于4",
        "5R6": "5不整除6", "dPrime": "解锁素数", "prm7": "7是素数", "ex!": "任何数都有阶乘", "infprm": "质数有无穷个",
        "aExt": "ZFC集合论", ".<i": "我包含我", "ext<": "我包含我", "empty": "千里之行，始于空集", ".zfc": "ZFC简化大礼包", "UUII": "交交并并",
        "a@a": "我给且只给所有不自己理发的人理发", "vwo": "一切皆可良序", "delAl": "不可数",
        "d()": "确定坐标，精确制导", "dX": "笛卡尔：积，故我在", "dSd0": "皮亚诺，你被解雇啦！", "dZ": "正正负负(Z)",
        "type": "类型论", "ttrue": "真理之门", "ttsimplFn": "简化依赖函数", "ttactic1": "证明助手上线！", "ttEq": "相等类型", "AllTrue": "True的值都是true",
        "ttindnat": "自然数的归纳法", "tt1+1": "1+1=2类型论版", "ttindeq": "相等的归纳法", "0+x": "代入方程即可", "x+x": "代入方程即可", "1neq2": "1就是1，2就是2（not (eq 1 2)）", "tt5R7": "数论达人(5不整除7)",
        "S1S1": "顺时针一圈逆时针一圈，还是回到原点", "eqvid": "我等价我", "ttua": "泛等公理（ua）", "looprfl": "圆圈跟圆点不同伦（loop不是rfl）", "ttpierce": "原来皮尔士跟他们是一伙的", "lemlie": "排中律是个谎言！？",
        "ttEven": "又是偶数", "ttList": "cons cons cons nil", "ttZ": "类型论版整数", ":=factorial2": "双阶乘！！", "tteven0": "Even 0只有even0", "ttWnat": "W自然数", "ttPathElim": "路径消消乐", "ttPoint": "零维的点", "ttisContr": "零维的点",
        "ttSetNat": "无数个点", "tteq2027": "无数个点", "ttdrawS1": "徒手画圆(Sus Bool=S1)", "ttS2": "吹气球(S2)", "pi1S1": "π₁(S¹)=Z", "hopf1": "Hopf纤维丛", "hopf2": "Hopf纤维丛",
        "ttfnext": "外延公理(fnext)", "ttNoFnext": "我不要外延公理了", "Bool=Bool=Bool": "Bool=Bool=Bool", "isequivP": "isProp(是双射)",
        "infhotel": "来了无穷位客人住旅馆", "permMaster": "排列大师"
    };
    constructor() {
        const gamemode = window.location.search === "?creative" ? "creative" : "survival";
        langMgr.init();
        if (gamemode === "creative") {
            this.creative = true;
        }
        this.fsGui = new FSGui(document.getElementById("prop-list"), document.getElementById("deduct-list"), document.getElementById("meta-list"), document.getElementById("sysfn-list"), document.getElementById("action-input"), document.getElementById("hint"), document.getElementById("display-p-layer"), document.querySelectorAll(".cmd-btns button"), this.creative, true);
        this.ttGui = new TTGui(this.creative, true);
        document.getElementById("panel").classList.remove("hide");
        this.hyperGui = new HyperGui();
        document.querySelectorAll("#panel>button").forEach((btn, idx) => {
            btn.onclick = () => {
                document.querySelectorAll("#panel>div").forEach(a => a.classList.remove("show"));
                document.getElementById("panel-" + idx).classList.add("show");
                if (idx === 0) {
                    this.hyperGui.onresize();
                    this.hyperGui.active = true;
                }
                else {
                    this.hyperGui.active = false;
                }
            };
        });
        const astmgr = new ASTMgr;
        this.hyperGui.world.onPassGate = (name, tile, hash) => {
            const gateTest = () => {
                if (tile.name?.[0] === "O") {
                    // todo: check genOrdMap
                    const ord = tile.name.slice(1).split(",").map(e => Number(e));
                    this.hyperGui.world.onPassOrd(hash, ord);
                    // this.hyperGui.world.currentOrd = ord;
                    // return true; // smaller or eq, okay
                    if (cmp(ord, this.maxOrd) <= 0) {
                        this.hyperGui.world.currentOrd = ord;
                        return true; // smaller or eq current, okay
                    }
                    if (cmp(ord, this.nextOrd) <= 0) {
                        if (cmp(ord, [1, 2, 3]) >= 0)
                            this.finishAchievement("ω^ω");
                        if (cmp(ord, [1, 2, 3, 4, 5]) >= 0)
                            this.finishAchievement("ω^ω^ω^ω");
                        this.maxOrd = ord;
                        this.nextOrd = calcMaxReachOrd(ord, this.ordBase, this.rewards.includes("stepw"));
                        this.updateProgressParam();
                        this.hyperGui.world.currentOrd = ord;
                        return true; // smaller or eq next, okay
                    }
                }
                else if (tile.type === 4)
                    return true;
                if (tile.name === "preord") {
                    return this.parcours >= 256;
                }
                if (tile.name === "I1I2I3") {
                    return (this.rewards.includes("I1") && this.rewards.includes("I2") && this.rewards.includes("I3"));
                }
                if (tile.name === "mct2mdt") {
                    const needed = 20;
                    if (this.deductriums < needed)
                        return false;
                    if (!this.rewards.includes("mct"))
                        return false;
                    this.consumed += needed;
                    this.addDeductriums(-needed);
                    return true;
                }
                if (tile.text.endsWith("#p")) {
                    // if with hyps, fail
                    const ast = this.fsGui.cmd.astparser.parse(tile.text.replaceAll("||", "|").replaceAll("\n#p", "").replaceAll("\n", ""));
                    if (this.rewards.includes("copygateD"))
                        this.fsGui.showWaitingAst(ast);
                    if (!this.fsGui.formalSystem.propositions[0]?.from)
                        return false;
                    return this.fsGui.getProps().findIndex(v => astmgr.equal(v.value, ast)) !== -1;
                }
                if (tile.text.endsWith("#d")) {
                    const ast = this.fsGui.cmd.astparser.parse(tile.text.replaceAll("\n#d", "").replaceAll("\n", ""));
                    if (this.rewards.includes("copygateD"))
                        this.fsGui.showWaitingAst(ast);
                    return Object.values(this.fsGui.formalSystem.deductions).findIndex(v => astmgr.equal(v.value, ast) && v.from.endsWith("*")) !== -1;
                }
                if (tile.text.endsWith("#t")) {
                    const target = tile.text.replaceAll("\n#t", "").replaceAll("\n", "");
                    const solved = this.ttGui.queryType(target);
                    if (!solved && this.ttGui.enablecopygate) {
                        this.ttGui.setLastGateTarget(target);
                    }
                    return solved;
                }
                if (tile.text.endsWith("#t:=")) {
                    const solved = this.ttGui.queryDefPuzzle(tile.name.slice(2));
                    return solved;
                }
                if (tile.name?.startsWith("JJZP-")) {
                    if (this.rewards.includes("JJZI")) {
                        return true;
                    }
                    return (this.deductriums < 4 && !this.rewards.includes("delgate"));
                }
                let reg;
                if ((reg = tile.text.match(/^通过此门需消耗推理素(.+)$/)) && reg[1]) {
                    const needed = parseDeductriumAmout(reg[1]);
                    if (this.deductriums < needed) {
                        // if the player is stucked due to lack of money, but without unlocking progress layer, give him/her a restart button
                        if (needed < 8 && document.getElementById("progress-btn").classList.contains("hide") && !document.getElementById("deduct-btn").classList.contains("hide")) {
                            document.querySelector(".restart").classList.remove("hide");
                        }
                        return false;
                    }
                    if (this.deductriums < needed * 2) {
                        this.hyperGui.blur();
                        if (!confirm(TR("进入此门将消耗") + reg[1] + TR("推理素，您只有") + stringifyDeductriumAmout(this.deductriums) + TR("推理素，确认要继续吗？") + (!this.rewards.includes("delgate") ? TR("注意，退出后重新进入门会重复扣钱！") : "")))
                            return false;
                        setTimeout(() => {
                            this.hyperGui.world.localCamMat = new Rotor();
                            this.hyperGui.needUpdate = true;
                        }, 1);
                    }
                    this.consumed += needed;
                    this.addDeductriums(-needed);
                    return true;
                }
                if (tile.text.endsWith("#imm")) {
                    if (Object.keys(this.fsGui.formalSystem.deductions).find(e => e.startsWith("a") && e.endsWith("x"))) {
                        return false;
                    }
                    return true;
                }
                return false;
            };
            if (!gateTest())
                return false;
            const achievement = this.achievementsTable[tile.name ?? tile.text];
            if (achievement)
                this.finishAchievement(achievement);
            if (tile.text.endsWith("#imm"))
                return true;
            if (this.rewards.includes("delgate") && !this.rewards.includes("hash") && tile.type !== 4) {
                tile.text += "\n （此门已拆除）";
                tile.type = 0;
                this.destructedGates++;
                this.updateProgressParam();
                this.rewards.push(name);
            }
            return true;
        };
        this.hyperGui.world.onStepToAnotherTile = () => {
            this.parcours++;
            this.updateProgressParam();
        };
        this.hyperGui.world.onGetReward = (hash, tile, isLoading) => {
            let text;
            if (!tile)
                return; // prevent crash progress
            if (tile.type === TileBlockType.Gate) {
                tile.text += "\n （此门已拆除）";
                if (tile.name && !this.rewards.includes(tile.name))
                    this.rewards.push(tile.name);
                else if (hash && !this.rewards.includes(hash))
                    this.rewards.push(hash);
                return;
            }
            if (tile.name === "zh-en" && !isLoading) {
                langMgr.setLang(langMgr.lang === "en" ? "zh" : "en");
                window.location.reload();
            }
            if (tile.name) {
                if (!this.rewards.includes(tile.name))
                    this.rewards.push(tile.name);
            }
            else {
                if (!this.rewards.includes(hash))
                    this.rewards.push(hash);
            }
            const achievement = this.achievementsTable[tile.name];
            if (achievement)
                this.finishAchievement(achievement, isLoading);
            if (tile.name?.startsWith("JJZ")) {
                const text = langMgr.lang === "en" ? langMgr.dataEnInCanvas[tile.text] ?? tile.text : tile.text;
                if (tile.name.startsWith("JJZO")) {
                    this.rewards = this.rewards.filter(e => e !== "JJZI");
                    this.hyperGui.world.setTileByName(tile.name.replace("JJZO", "JJZ"), "获取5µg推理素", TileBlockType.Reward);
                }
                ;
                if (tile.name.startsWith("JJZI"))
                    this.rewards.push("JJZI");
                if (!tile.name.startsWith("JJZ-")) {
                    return setTimeout(() => {
                        tile.text = text;
                        tile.type = TileBlockType.Reward;
                    }, 1);
                }
            }
            switch (tile.name) {
                case "dL": return document.getElementById("deduct-btn").classList.remove("hide");
                case "progL":
                    document.querySelector(".restart").classList.add("hide");
                    return document.getElementById("progress-btn").classList.remove("hide");
                case "delgate": return;
                case "macro":
                    this.fsGui.unlockedMacro = true;
                    return document.getElementById("macro-btns").classList.remove("hide");
                case "hyp":
                    this.fsGui.unlockedHyp = true;
                    return document.getElementById("hyp-btn").classList.remove("hide");
                case "mkdir":
                    this.fsGui.unlockedFolder = true;
                    return document.getElementById("dir-btn").classList.remove("hide");
                case "renameD":
                    this.fsGui.unlockedRename = true;
                    return document.getElementById("rename-btn").classList.remove("hide");
                case "neg":
                    this.fsGui.addToDeductions("a3", "a2");
                    return;
                case "cmpss":
                    this.hyperGui.world.navigateDraw = true;
                    return;
                case "sysrule":
                    this.fsGui.unlockedSysRulePanel = true;
                    this.fsGui.updateSysFnList();
                    return;
                case "del-pn":
                    const tilePn = this.hyperGui.world.getBlock(".pn");
                    tilePn.text += "\n （此门已拆除）";
                    tilePn.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return;
                case "del-ttAleph":
                    const tileLi = this.hyperGui.world.getBlock("ttpAleph");
                    tileLi.text += "\n （此门已拆除）";
                    tileLi.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return;
                case "del-W":
                    const tileW = this.hyperGui.world.getBlock("W");
                    tileW.text += "\n （此门已拆除）";
                    tileW.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return;
                case "omega":
                    const tileOmega = this.hyperGui.world.getBlock("w");
                    tileOmega.text += "\n （此门已拆除）";
                    tileOmega.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return;
                case "delAl":
                    const tileAleph = this.hyperGui.world.getBlock("Aleph");
                    tileAleph.text += "\n （此门已拆除）";
                    tileAleph.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return;
                case "delAlw":
                    const tileAlephw = this.hyperGui.world.getBlock("AlephW");
                    tileAlephw.text += "\n （此门已拆除）";
                    tileAlephw.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return;
                case "base-1":
                case "base-2":
                case "base-3":
                case "base-4":
                case "base-5":
                case "base-6":
                case "base-7":
                case "base-8":
                case "base-9":
                case "base-10":
                    if (this.ordBase > 5) {
                        this.ordBase--;
                        this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                        this.updateProgressParam();
                    }
                    break;
                case "base5":
                    this.ordBase = 4;
                    this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                    this.updateProgressParam();
                    break;
                case "base4":
                    this.ordBase = 3;
                    this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                    this.updateProgressParam();
                    break;
                case "base3":
                    this.ordBase = 2;
                    this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                    this.updateProgressParam();
                    break;
                case "base2":
                    this.ordBase = 1;
                    this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                    this.updateProgressParam();
                    break;
                case "w^2":
                case "ww2":
                case "w^3":
                case "w4234":
                    const newOrd = {
                        "w^2": [1, 2, 2],
                        "w^3": [1, 2, 2, 2],
                        "w4234": [1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2],
                        "ww2": [1, 2, 3, 2, 3],
                    }[tile.name];
                    if (cmp(newOrd, this.maxOrd) > 0) {
                        this.maxOrd = newOrd;
                        this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                        this.updateProgressParam();
                    }
                    return;
                case "del<>":
                    const tileIFF = this.hyperGui.world.getBlock("port-iff");
                    tileIFF.text += "\n （此门已拆除）";
                    tileIFF.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return;
                case "delK":
                    const tileK = this.hyperGui.world.getBlock("K");
                    tileK.text += "\n （此门已拆除）";
                    tileK.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return;
                case "delL":
                    const tileL = this.hyperGui.world.getBlock("L");
                    tileL.text += "\n （此门已拆除）";
                    tileL.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return;
                case ".prop":
                    [
                        '.i', '.t', '.ne', '.ni', '.cs', '.a30', '.a31', '.a32', '.m', '.mn', '.m1', '.m2', '.m&', '.m&1', '.m&2',
                        '.<>', '.<>1', '.<>2', '.<>i', '.<>s', '.<>t', '.<>&', '.<>r>', '.<>rn', '.<>r<>', '.<>r&', '.<>r|',
                        '.&', '.&1', '.&2', '.&n1', '.&n2', '.&s', '.&a', '.&m1', '.&m2',
                        '.|i', '.|1', '.|2', '.|n', '.|n1', '.|n2', '.|s', '.|a', '.|m',
                        '.n|&', '.n&|', '.nn|&', '.nn&|', '.|nn&', '.&nn|',
                        '.n', '.a3<>', '.a31<>', '.a32<>', '.>TF', '.>FU', '.>|', '.<>TT', '.<>FF', '.<>TF', '.<>FT',
                    ].forEach(s => this.fsGui.addToDeductions(s));
                    return;
                case "kit+*":
                    [
                        ".=Se", ".=Si", ".=S", ".=r+", ".=r*", ".0+", ".S+", ".+@N", ".pred", ".+s", ".+a", ".+e", ".+=0", ".0*", ".*@N", ".S*", ".*s", ".*+d", ".+*d", ".*a", ".*=0", ".*n=0", ".*e",
                    ].forEach(s => this.fsGui.addToDeductions(s));
                    return;
                case ".1st":
                    [
                        ".nEVn", ".nVEn", ".nVVn", ".nEn", ".Ve", ".Vs", ".V&1", ".V&2", ".V&", ".Ee", ".Ei", ".Eirp", ".Erp", ".Es", ".EV", ".E|1", ".E|2", ".E|",
                        ".Vnf", ".Vnf>", ".V>nf", ".Vnf|", ".V|nf", ".Vnf&", ".V&nf", ".Enf", ".Enf>", ".E>nf", ".Enf|", ".E|nf", ".Enf&", ".E&nf",
                        ".Emp", ".Vcn", ".Ecn", ".Vcn<>", ".Ecn<>",
                        ".=s", ".=t", ".=r=", ".=r@",
                    ].forEach(s => this.fsGui.addToDeductions(s));
                    this.fsGui.addToDeductions(".<>rV", ".<>r|");
                    this.fsGui.addToDeductions(".<>rE", ".<>rV");
                    return;
                case "copygateD":
                    document.getElementById("copygateD-wrapper").classList.remove("hide");
                    return;
                case "1st":
                    this.fsGui.addToDeductions("a4", "a3");
                    this.fsGui.addToDeductions("a5", "a4");
                    this.fsGui.addToDeductions("a6", "a5");
                    return this.unlockMetarule("q");
                case "iff":
                    this.fsGui.addToDeductions("d<>1");
                    this.fsGui.addToDeductions("d<>2");
                    return;
                case "a7":
                    this.fsGui.addToDeductions("a7", "a6");
                    return;
                case "a8":
                    this.fsGui.addToDeductions("a8", "a7");
                    return;
                case "dE":
                    this.fsGui.addToDeductions("dE", "a6");
                    return;
                case "dE!":
                    this.fsGui.addToDeductions("dE!", "dE");
                    return;
                case "d{}":
                    this.fsGui.addToDeductions("d{}");
                    return;
                case "d{.}":
                    this.fsGui.addToDeductions("d{.}");
                    return;
                case "d{..}":
                    this.fsGui.addToDeductions("d{..}");
                    return;
                case "d{@|}":
                    this.fsGui.addToDeductions("d{@|}");
                    return;
                case "d{|@}":
                    this.fsGui.addToDeductions("d{|@}");
                    return;
                case "dX":
                    this.fsGui.addToDeductions("dX");
                    return;
                case "d()pr":
                    this.fsGui.addToDeductions("d()pr");
                    return;
                case "d<=":
                    this.fsGui.addToDeductions("d<=");
                    this.fsGui.addToDeductions("d>=");
                    return;
                case "dsub":
                    this.fsGui.addToDeductions("d\\");
                    return;
                case "ddiv":
                    this.fsGui.addToDeductions("d/|");
                    return;
                case "dfZ":
                    this.fsGui.addToDeductions("dfZ");
                    return;
                case "dZ":
                    this.fsGui.addToDeductions("dZ");
                    return;
                case "dZ+":
                    this.fsGui.addToDeductions("dZ+");
                    return;
                case "dPow":
                    this.fsGui.addToDeductions("dPow");
                    return;
                case "dZ*":
                    this.fsGui.addToDeductions("dZ*");
                    return;
                case "dZ<=":
                    this.fsGui.addToDeductions("dZ<=");
                    return;
                case "d<>":
                    this.fsGui.addToDeductions("d<>");
                    return;
                case "d<":
                    this.fsGui.addToDeductions("d<");
                    return;
                case "dw":
                    this.fsGui.addToDeductions("domega");
                    return;
                case "dSd0":
                    this.fsGui.addToDeductions("d0");
                    this.fsGui.addToDeductions("dS");
                    this.fsGui.addToDeductions("dN");
                    return;
                case "dOrder":
                    this.fsGui.addToDeductions("dOrder");
                    this.fsGui.addToDeductions("dWOrder");
                    return;
                case "dRel":
                    this.fsGui.addToDeductions("dRel");
                    return;
                case "dEquiv":
                    this.fsGui.addToDeductions("dEquiv");
                    return;
                case "andor":
                    this.fsGui.addToDeductions("d&");
                    this.fsGui.addToDeductions("d|");
                    return;
                case "aExt":
                    this.fsGui.addToDeductions("aExt");
                    if (this.rewards.includes(".zfc")) {
                        this.fsGui.addToDeductions(".aext");
                    }
                    this.checkAllZFC(isLoading);
                    return;
                case "aPair":
                    this.fsGui.addToDeductions("aPair");
                    if (this.rewards.includes(".zfc")) {
                        this.fsGui.addToDeductions(".apair");
                    }
                    this.checkAllZFC(isLoading);
                    return;
                case "aReg":
                    this.fsGui.addToDeductions("aReg");
                    if (this.rewards.includes(".zfc")) {
                        this.fsGui.addToDeductions(".areg");
                    }
                    this.checkAllZFC(isLoading);
                    return;
                case "aSep":
                    this.fsGui.addToDeductions("aSep");
                    if (this.rewards.includes(".zfc")) {
                        this.fsGui.addToDeductions(".asep");
                    }
                    this.checkAllZFC(isLoading);
                    return;
                case "aUnion":
                    this.fsGui.addToDeductions("aUnion");
                    if (this.rewards.includes(".zfc")) {
                        this.fsGui.addToDeductions(".aunion");
                    }
                    this.checkAllZFC(isLoading);
                    return;
                case "aPow":
                    this.fsGui.addToDeductions("aPow");
                    if (this.rewards.includes(".zfc")) {
                        this.fsGui.addToDeductions(".apow");
                    }
                    this.checkAllZFC(isLoading);
                    return;
                case "aRepl":
                    this.fsGui.addToDeductions("aRepl");
                    if (this.rewards.includes(".zfc")) {
                        this.fsGui.addToDeductions(".arepl");
                    }
                    this.checkAllZFC(isLoading);
                    return;
                case "aInf":
                    this.fsGui.addToDeductions("aInf");
                    if (this.rewards.includes(".zfc")) {
                        this.fsGui.addToDeductions(".ainf");
                    }
                    this.checkAllZFC(isLoading);
                    return;
                case "aChoice":
                    this.fsGui.addToDeductions("aChoice");
                    if (this.rewards.includes(".zfc")) {
                        this.fsGui.addToDeductions(".achoice");
                    }
                    this.checkAllZFC(isLoading);
                    return;
                case ".zfc":
                    if (this.fsGui.deductions.includes("aExt"))
                        this.fsGui.addToDeductions(".aext", "aExt");
                    if (this.fsGui.deductions.includes("aPair"))
                        this.fsGui.addToDeductions(".apair", "aPair");
                    if (this.fsGui.deductions.includes("aReg"))
                        this.fsGui.addToDeductions(".areg", "aReg");
                    if (this.fsGui.deductions.includes("aSep"))
                        this.fsGui.addToDeductions(".asep", "aSep");
                    if (this.fsGui.deductions.includes("aUnion"))
                        this.fsGui.addToDeductions(".aunion", "aUnion");
                    if (this.fsGui.deductions.includes("aPow"))
                        this.fsGui.addToDeductions(".apow", "aPow");
                    if (this.fsGui.deductions.includes("aRepl"))
                        this.fsGui.addToDeductions(".arepl", "aRepl");
                    if (this.fsGui.deductions.includes("aInf"))
                        this.fsGui.addToDeductions(".ainf", "aInf");
                    if (this.fsGui.deductions.includes("aChoice"))
                        this.fsGui.addToDeductions(".achoice", "aChoice");
                    return;
                case "mct": return this.unlockMetarule("cdt");
                case "mdt": return this.unlockMetarule("dt");
                case "mcpt":
                    this.unlockMetarule("cdt");
                    this.unlockMetarule("idt");
                    return this.unlockMetarule("cpt");
                case "mprd": return this.unlockMetarule("prd");
                case "mc": return this.unlockMetarule("c");
                case "mf": return this.unlockMetarule("f");
                case "mcmt": return this.unlockMetarule("cmt");
                case "midt": return this.unlockMetarule("idt");
                case "mifft": return this.unlockMetarule("ifft");
                case "mnt":
                    const tileRP = this.hyperGui.world.getBlock("port-rp");
                    tileRP.text += "\n （此门已拆除）";
                    tileRP.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return;
                case "ifft-EU":
                    this.fsGui.enableMIFFT_RP = true;
                    return;
                case "met":
                    this.unlockMetarule("et");
                case "mvt":
                    this.unlockMetarule("cvt");
                    this.unlockMetarule("vt");
                    return;
                case "mcvt":
                    const tileV = this.hyperGui.world.getBlock("V");
                    tileV.text += "\n （此门已拆除）";
                    tileV.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
                    return this.unlockMetarule("cvt");
                case "highlightd": return this.hyperGui.world.highLightGetD = true;
                case "peano":
                    for (let i = 1; i <= 5; i++)
                        this.fsGui.addToDeductions("apn" + i);
                    for (let i = 1; i <= 10; i++)
                        this.fsGui.addToDeductions("d" + i);
                    return;
                case "add-mul":
                    this.fsGui.addToDeductions("d+1", "d10");
                    this.fsGui.addToDeductions("d+2", "d+1");
                    this.fsGui.addToDeductions("d*1", "d+2");
                    this.fsGui.addToDeductions("d*2", "d*1");
                    return;
                case "dU":
                    this.fsGui.addToDeductions("dUnion");
                    return this.fsGui.addToDeductions("dU");
                case "dI":
                    return this.fsGui.addToDeductions("dI");
                case "d()":
                    return this.fsGui.addToDeductions("d()");
                case "d()pr":
                    return this.fsGui.addToDeductions("d()pr");
                case ".filter":
                    return this.fsGui.addToDeductions(".filter");
                case "dPrime":
                    this.fsGui.addToDeductions("dPrime", "d*2");
                    return;
                case "natop":
                    return this.fsGui.formalSystem.fastmetarules += "#";
                case "dZn":
                    return this.fsGui.formalSystem.fastmetarules += "z";
                case "dZop":
                    return this.fsGui.formalSystem.fastmetarules += "Z";
                case "apn5-err-out":
                    this.fsGui.cmd.addWrongDeduction("apn5x");
                    text = langMgr.lang === "en" ? langMgr.dataEnInCanvas[tile.text] ?? tile.text : tile.text;
                    return setTimeout(() => {
                        tile.text = text;
                        tile.type = TileBlockType.Reward;
                    }, 1);
                case "asep-err-out":
                    this.fsGui.cmd.addWrongDeduction("asepx");
                    text = langMgr.lang === "en" ? langMgr.dataEnInCanvas[tile.text] ?? tile.text : tile.text;
                    return setTimeout(() => {
                        tile.text = text;
                        tile.type = TileBlockType.Reward;
                    }, 1);
                case "omit-fn":
                    document.getElementById("wrap-simpl-sysfn").classList.remove("hide");
                    this.fsGui.onchangeOmitNF();
                    return;
                case "italic-item":
                    document.getElementById("wrap-italic-item").classList.remove("hide");
                    this.fsGui.onchangeOmitNF();
                    return;
                case "type": return document.getElementById("type-btn").classList.remove("hide");
                case "ttsimplFn":
                    this.ttGui.disableSimpleFn = false;
                    document.getElementById("displayPi-label").classList.remove("hide");
                    return this.ttGui.updateAfterUnlock();
                case "ttsimplEq":
                    this.ttGui.disableSimpleEq = false;
                    this.ttGui.unlock("eq.=");
                    return this.ttGui.updateAfterUnlock();
                case "ttnotFn": return this.ttGui.unlock("False.not", true);
                case "ttEq":
                    this.ttGui.unlock("eq");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttactic1":
                    document.getElementById("tactic-div").classList.remove("hide");
                    this.ttGui.unlockedTactics.add("expand");
                    this.ttGui.unlockedTactics.add("intro");
                    this.ttGui.unlockedTactics.add("exact");
                    this.ttGui.unlockedTactics.add("apply");
                    return;
                case "ttNat":
                    this.ttGui.unlock("nat");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttBool":
                    this.ttGui.unlock("Bool");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttrfl":
                    this.ttGui.unlock("eq.rfl", true);
                    document.getElementById("tactic-div").classList.remove("hide");
                    this.ttGui.unlockedTactics.add("rfl");
                    return;
                case "ttindTrue":
                    this.ttGui.unlock("True.ind");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttindFalse":
                    this.ttGui.unlock("False.ind");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttindBool":
                    this.ttGui.unlock("Bool.ind");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttindnat":
                    this.ttGui.unlock("nat.ind");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttProd":
                    this.ttGui.unlock("Prod");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttSum":
                    this.ttGui.unlock("Sum");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttindProd":
                    this.ttGui.unlock("Prod.ind");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttindSum":
                    this.ttGui.unlock("Sum.ind");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttindeq":
                    this.ttGui.unlock("eq.ind");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttpr":
                    this.ttGui.unlock("Prod.pr0");
                    this.ttGui.unlock("Prod.pr1");
                    this.ttGui.unlock("Prod.prd1");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttinveq":
                    this.ttGui.unlock("eq.inv");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttcompeq":
                    this.ttGui.unlock("eq.*");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttransC":
                    this.ttGui.unlock("eq.transconst");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttpred":
                    this.ttGui.unlock("nat.pred", true);
                    return;
                case "ttdbl":
                    this.ttGui.unlock("nat.double", true);
                    return;
                case "ttadd":
                    this.ttGui.unlock("nat.add", true);
                    return;
                case "ttmul":
                    this.ttGui.unlock("nat.mul", true);
                    return;
                case "ttpow":
                    this.ttGui.unlock("nat.pow", true);
                    return;
                case "tt!":
                    this.ttGui.unlock("nat.!", true);
                    return;
                case "ttleZ":
                    this.ttGui.unlock("Z.le");
                    return;
                case "ttabsZ":
                    this.ttGui.unlock("Z.abs");
                    return;
                case "ttcode_S1":
                    this.ttGui.unlock("S1.code");
                    return;
                case "ttranseq":
                    this.ttGui.unlock("eq.transeq");
                    return;
                case "ttord":
                    this.ttGui.unlock("Ord");
                    this.ttGui.unlock("(Ord)");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttap":
                    this.ttGui.disableSimpleEq = false;
                    this.ttGui.unlock("eq.=");
                    this.ttGui.unlock("eq.ap");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttap2":
                    this.ttGui.unlock("eq.apd");
                    this.ttGui.unlock("eq.trans");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "tteqprop1":
                    this.ttGui.unlock("eq.rightrfl");
                    this.ttGui.unlock("eq.invinv");
                    this.ttGui.unlock("eq.rightinv");
                    this.ttGui.unlock("eq.leftinv");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttransleft":
                    this.ttGui.unlock("eq.transleft");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttransleftright":
                    this.ttGui.unlock("eq.rightrfl");
                    this.ttGui.unlock("eq.transleftright");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttransright":
                    this.ttGui.unlock("eq.rightrfl");
                    this.ttGui.unlock("eq.transright");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttS1":
                    this.ttGui.unlock("S1");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttindS1":
                    this.ttGui.unlock("S1.ind");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttrecS1":
                    this.ttGui.unlock("S1.rec");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttaploop":
                    this.ttGui.unlock("S1.ap_loop");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "tteqv":
                    this.ttGui.unlock("eqv");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttua":
                    this.ttGui.unlock("eqv.id2eqv");
                    this.ttGui.unlock("eqv.refl");
                    this.ttGui.unlock("ua");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttfnext":
                    this.ttGui.unlock("fnext");
                    this.ttGui.unlock("eq.happly");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttLiftU":
                    this.ttGui.unlock("LiftU");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttpseudoeqv":
                    this.ttGui.unlock("naiveqv");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttI":
                    this.ttGui.unlock("I");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttZ":
                    this.ttGui.unlock("Z");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttW":
                    this.ttGui.unlock("W");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttisProp":
                    this.ttGui.unlock("Prop");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttisSet":
                    this.ttGui.unlock("Set");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttisContr":
                    this.ttGui.unlock("Contr");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttTrunc":
                    this.ttGui.unlock("Trunc");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttnat2Z":
                    this.ttGui.unlock("Z.nat2");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttnegZ":
                    this.ttGui.unlock("Z.neg");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttsuccZ":
                    this.ttGui.unlock("Z.succ");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttpredZ":
                    this.ttGui.unlock("Z.pred");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "pred_succZ":
                    this.ttGui.unlock("Z.predsucc");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "succ_predZ":
                    this.ttGui.unlock("Z.succpred");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttaddZ":
                    this.ttGui.unlock("Z.add");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttmulZ":
                    this.ttGui.unlock("Z.mul");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttloop^":
                    this.ttGui.unlock("S1.loop_pow");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttSus":
                    this.ttGui.unlock("Sus");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttS2":
                    this.ttGui.unlock("S2");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttS3":
                    this.ttGui.unlock("S3");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttindS2":
                    this.ttGui.unlock("S2.ind");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttEven":
                    this.ttGui.unlock("Even");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttList":
                    this.ttGui.unlock("List");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttAleph":
                    this.ttGui.unlock("Aleph");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttOption":
                    this.ttGui.unlock("Option");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttrans2":
                    this.ttGui.unlock("eq.trans2");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttapd2":
                    this.ttGui.unlock("eq.apd2");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttpo":
                    this.ttGui.unlock("Pushout");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttJoin":
                    this.ttGui.unlock("Pushout.Join");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttWedge":
                    this.ttGui.unlock("Pushout.Wedge");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttNW":
                    this.ttGui.unlock("W.nat");
                    this.ttGui.updateAfterUnlock();
                    return;
                case "ttlazy":
                    this.ttGui.enablecopygate = true;
                    return;
                case "ttacticFnext":
                    this.ttGui.unlockedTactics.add("fnext");
                    return;
                case "ttsup":
                    this.ttGui.unlockedTactics.add("sup");
                    return;
                case "ttsimpl":
                    this.ttGui.unlockedTactics.add("simpl");
                    return;
                case "ttdestruct":
                    this.ttGui.unlockedTactics.add("destruct");
                    return;
                case "ttacticeq":
                    this.ttGui.unlockedTactics.add("eq");
                    return;
                case "ttelimeq":
                    Assist.disableDestructEq = false;
                    return;
                case "ttelimcond":
                    Assist.disableDestructConds = false;
                    return;
                case "ttapply2":
                    Assist.disableMultipleApply = false;
                    return;
                case "ttrw":
                    this.ttGui.unlockedTactics.add("rw");
                    this.ttGui.unlockedTactics.add("rwb");
                    return;
                case "ttacticEx":
                    this.ttGui.unlockedTactics.add("case");
                    this.ttGui.unlockedTactics.add("ex");
                    return;
                case "tthyp":
                    this.ttGui.unlockedTactics.add("hyp");
                    return;
                case "ttacticLR":
                    this.ttGui.unlockedTactics.add("left");
                    this.ttGui.unlockedTactics.add("right");
                    return;
                case "disableua":
                    text = langMgr.lang === "en" ? langMgr.dataEnInCanvas[tile.text] ?? tile.text : tile.text;
                    this.ttGui.disableAxiom("ua", "ua_id2eqv", "id2eqv_ua");
                    return setTimeout(() => {
                        tile.text = text;
                        tile.type = TileBlockType.Reward;
                    }, 1);
                case "enableua":
                    text = langMgr.lang === "en" ? langMgr.dataEnInCanvas[tile.text] ?? tile.text : tile.text;
                    this.ttGui.enableAxiom("ua", "ua_id2eqv", "id2eqv_ua");
                    return setTimeout(() => {
                        tile.text = text;
                        tile.type = TileBlockType.Reward;
                    }, 1);
                case "disablefnext":
                    text = langMgr.lang === "en" ? langMgr.dataEnInCanvas[tile.text] ?? tile.text : tile.text;
                    this.ttGui.disableAxiom("fnext", "fnext_happly", "happly_fnext");
                    return setTimeout(() => {
                        tile.text = text;
                        tile.type = TileBlockType.Reward;
                    }, 1);
                case "enablefnext":
                    text = langMgr.lang === "en" ? langMgr.dataEnInCanvas[tile.text] ?? tile.text : tile.text;
                    this.ttGui.disableAxiom("fnext", "fnext_happly", "happly_fnext");
                    this.ttGui.enableAxiom("fnext", "fnext_happly", "happly_fnext");
                    return setTimeout(() => {
                        tile.text = text;
                        tile.type = TileBlockType.Reward;
                    }, 1);
                case "disableI":
                    text = langMgr.lang === "en" ? langMgr.dataEnInCanvas[tile.text] ?? tile.text : tile.text;
                    this.ttGui.disableAxiom("I", "0I", "1I", "ind_I", "rec_I", "segI", "apd_segI", "ap_segI");
                    return setTimeout(() => {
                        tile.text = text;
                        tile.type = TileBlockType.Reward;
                    }, 1);
                case "enableI":
                    text = langMgr.lang === "en" ? langMgr.dataEnInCanvas[tile.text] ?? tile.text : tile.text;
                    this.ttGui.disableAxiom("fnext", "fnext_happly", "happly_fnext");
                    this.ttGui.enableAxiom("I", "0I", "1I", "ind_I", "rec_I", "segI", "apd_segI", "ap_segI");
                    return setTimeout(() => {
                        tile.text = text;
                        tile.type = TileBlockType.Reward;
                    }, 1);
            }
            let reg;
            if ((reg = tile.name?.match(/^tt(.+)$/)) && reg[1]) {
                return this.ttGui.unlock(reg[1]);
            }
            if ((reg = tile.text.match(/^获取(.+)推理素$/)) && reg[1] && !isLoading) {
                this.addDeductriums(parseDeductriumAmout(reg[1]));
            }
        };
        const progressBtns = Array.from(document.querySelectorAll(".progress-btns button"));
        const txtarea = document.getElementById("progress-txtarea");
        const gameSaveLoad = new GameSaveLoad(gamemode);
        let loadFile = false;
        progressBtns[0].addEventListener("click", () => gameSaveLoad.save(this, txtarea));
        progressBtns[1].addEventListener("click", () => {
            const title = document.getElementById("gamemode").innerText;
            document.getElementById("gamemode").innerText = "[...Loading...]";
            // to update title [...Loading...]
            setTimeout(() => {
                if (!loadFile && !confirm(TR("请粘贴进度代码至保存加载按钮下方的文本框内。粘贴好了请点确定，还未粘贴请先点取消\n注意：加载新进度后，当前游戏进度会丢失！"))) {
                    document.getElementById("gamemode").innerText = title;
                    return;
                }
                loadFile = false;
                const str = txtarea.value;
                if (!str.trim()) {
                    alert(TR("进度代码为空！"));
                }
                else {
                    this.fsGui.skipRendering = true;
                    gameSaveLoad.load(this, str);
                    window.location.href = window.location.href || "?";
                }
                document.getElementById("gamemode").innerText = title;
            }, 20);
        });
        progressBtns[2].addEventListener("click", () => {
            // 跟Btns[0]相同，但保存到文件
            const str = gameSaveLoad.save(this);
            const blob = new Blob([str], { type: "text/plain" });
            const url = URL.createObjectURL(blob);
            const a = document.createElement("a");
            a.href = url;
            a.download = `deductrium_progress${new Date().toISOString()}.txt`;
            a.click();
            URL.revokeObjectURL(url);
        });
        document.querySelector(".progress-btns input[type='file']").addEventListener("change", (e) => {
            // 跟Btns[1]相同，但从文件加载
            loadFile = true;
            const file = e.target.files[0];
            const reader = new FileReader();
            reader.onload = (ev) => {
                const str = ev.target.result;
                txtarea.value = str;
                progressBtns[1].click();
            };
            reader.readAsText(file);
        });
        progressBtns[3].addEventListener("click", () => gameSaveLoad.reset());
        document.querySelector(".restart").addEventListener("click", () => gameSaveLoad.reset());
        progressBtns[4].addEventListener("click", () => { langMgr.setLang(langMgr.lang === "en" ? "zh" : "en"); window.location.reload(); });
        const saves = localStorage.getItem(gameSaveLoad.storageKey);
        // autosave while updated within a time interval
        this.hyperGui.world.onStateChange = this.ttGui.onStateChange = this.fsGui.onStateChange = () => gameSaveLoad.stateChange(this);
        if (saves)
            gameSaveLoad.load(this, saves);
        document.getElementById("loading").classList.add("hide");
        this.fsGui.skipRendering = false;
        this.ttGui.skipRendering = false;
        this.fsGui.onchangeOmitNF();
        const displayPi = document.getElementById("displayPi");
        displayPi.addEventListener("change", e => {
            this.ttGui.displayPi = !displayPi.checked;
            this.ttGui.updateAfterUnlock();
            if (!this.ttGui.displayPi)
                this.rewards.push("[set]NotDisplayPi");
            if (this.ttGui.displayPi && this.rewards.includes("[set]NotDisplayPi")) {
                this.rewards = this.rewards.filter(e => e !== "[set]NotDisplayPi");
            }
        });
        this.ttGui.displayPi = !this.rewards.includes("[set]NotDisplayPi");
        displayPi.checked = !this.ttGui.displayPi;
        this.ttGui.updateAfterUnlock();
        langMgr.setLang(langMgr.lang);
        this.hyperGui.needUpdate = true;
    }
    checkAllZFC(mute) {
        let r = this.fsGui.deductions.includes("aUnion");
        r &&= this.fsGui.deductions.includes("aPair");
        r &&= this.fsGui.deductions.includes("aInf");
        r &&= this.fsGui.deductions.includes("aPow");
        r &&= this.fsGui.deductions.includes("aSep");
        r &&= this.fsGui.deductions.includes("aExt");
        r &&= this.fsGui.deductions.includes("aRepl");
        r &&= this.fsGui.deductions.includes("aReg");
        r &&= this.fsGui.deductions.includes("aChoice");
        if (r)
            this.finishAchievement("集齐所有ZFC公理", mute);
    }
    addDeductriums(amount) {
        this.deductriums += amount;
        this.showHint(TR("推理素") + (amount >= 0 ? "+" : "") + stringifyDeductriumAmout(amount) + "<br>" + TR("共") + stringifyDeductriumAmout(this.deductriums));
        if (amount < 0)
            this.finishAchievement("第一次消费");
        if (amount > 0)
            this.finishAchievement("吃素啦");
        const totalObtained = this.deductriums + this.consumed;
        if (totalObtained >= 40)
            this.finishAchievement("素食主义者（累计获40µg推理素）");
        if (totalObtained >= 1000)
            this.finishAchievement("加大剂量（累计获1mg推理素）");
        if (totalObtained >= 1e6)
            this.finishAchievement("致死剂量（累计获1g推理素）");
        if (totalObtained >= 50.1e9)
            this.finishAchievement("临界质量（累计获50.1kg推理素）");
    }
    updateProgressParam() {
        document.getElementById("deductrium-amount").innerText = stringifyDeductriumAmout(this.deductriums);
        document.getElementById("deductrium-consumed").innerText = stringifyDeductriumAmout(this.consumed);
        document.getElementById("parcours-tiles").innerText = this.parcours.toString();
        document.getElementById("destructed-gates").innerText = this.destructedGates.toString();
        document.getElementById("max-ord").innerText = printOrd(this.maxOrd);
        document.getElementById("ord-base").innerText = (this.ordBase + 1).toString();
        document.getElementById("next-ord").innerText = cmp(this.nextOrd, [1, 2, 3, 4, 5]) > 0 ? "？？" : printOrd(this.nextOrd);
        document.getElementById("next-ord-stepw").innerText = this.rewards.includes("stepw") ? TR("、后继指数提升") : "";
    }
    showHint(text) {
        const dom = document.createElement("div");
        document.body.appendChild(dom);
        dom.innerHTML = text;
        dom.classList.add("hintbar");
        setTimeout(() => {
            document.body.removeChild(dom);
        }, 5000);
    }
    finishAchievement(a, mute) {
        if (this.rewards.includes("[ach]" + a))
            return;
        for (const d of document.querySelectorAll(".achievement div")) {
            // if (d.innerText === a) {
            if (d.getAttribute("data-tr") === a) {
                d.classList.add("achieved");
                d.parentElement.classList.remove("locked");
                break;
            }
        }
        if (!mute)
            this.showHint("<br><br><br><div style='border:solid;border-radius:0.3em; padding:0.3em'>" + TR("获得成就：") + "<br>" + TR(a) + "</div>");
        this.rewards.push("[ach]" + a);
    }
    unlockMetarule(name) {
        if (this.fsGui.metarules.includes(name))
            return;
        this.fsGui.metarules.push(name);
        this.fsGui.formalSystem.fastmetarules += {
            "cdt": "c",
            "dt": ">",
            "idt": "<",
            "cvt": "v",
            "vt": "u",
            "et": "e",
            "cmt": ":",
            "q": "q",
        }[name] || "";
        this.fsGui.updateMetaRuleList(true);
        document.getElementById("metarule-subpanel").classList.remove("hide");
    }
}
new Game;
//# sourceMappingURL=game.js.map