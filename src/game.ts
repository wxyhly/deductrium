import { ASTMgr } from "./fs/astmgr.js";
import { FSGui } from "./fs/gui.js";
import { HyperGui } from "./hy/gui.js"
import { TileBlock, TileBlockType } from "./hy/maploader.js";
import { calcMaxReachOrd, cmp, printOrd } from "./hy/ordinal.js";
import { langMgr, TR } from "./lang.js";
import { GameSaveLoad } from "./saveload.js";
import { TTGui } from "./tt/gui.js";
function parseDeductriumAmout(str: string) {
    let coeff: number;
    if (str.endsWith("µg")) coeff = 1;
    else if (str.endsWith("mg")) coeff = 1e3;
    else if (str.endsWith("kg")) coeff = 1e9;
    else if (str.endsWith("g")) coeff = 1e6;
    else if (str.endsWith("T")) coeff = 1e12;
    return Number(str.replaceAll(/[a-zA-Zµ]+/g, "")) * coeff;
}
export function stringifyDeductriumAmout(n: number) {
    const absn = Math.abs(n);
    if (absn > 1e12) {
        return n / 1e12 + "T";
    } if (absn > 1e9) {
        return n / 1e9 + "kg";
    } if (absn > 1e6) {
        return n / 1e6 + "g";
    } if (absn > 1e3) {
        return n / 1e3 + "mg";
    }
    return n + "µg"
}
export class Game {
    fsGui: FSGui;
    hyperGui: HyperGui;
    ttGui: TTGui;
    rewards: string[] = [];
    deductriums: number = 0; //ug
    destructedGates: number = 0;
    parcours: number = 1;
    consumed: number = 0;
    maxOrd: number[] = [];
    nextOrd: number[] = [1];
    ordBase = 15;
    creative = false;
    achievementsTable = {
        "aa": "我推出我", "delgate": "收费站拆除", ".i": "你推出你，他推出他（⊢$0>$0）", "progL": "解锁了成就",
        "hyp": "If I were..", "mdt": "会跑的“⊢”（演绎元定理）", "neg": "敢于说不", ".dne": "负负得正", "exfalso1": "否定爆炸", "exfalso2": "否定爆炸",
        "iff": "我推出你，你推出我（<>）", "andor": "逻辑门（与/或）", "pierce": "皮尔士定律((p>q)>p)>p", "lem": "排中律是真的！(p|~p)", "contra": "没毛病！~( p & ~p )", "mcpt": "命题逻辑自动推理",
        "1st": "一阶逻辑", "nf": "约束与自由", "rp": "丢掉量词，尽情替换！", "a7": "众生平等", "mvt": "概括一切（概括元定理）",
        ".prop": "命题逻辑大礼包", "mifft": "替换一切（互推替换元定理）", ".1st": "一阶逻辑大礼包", "terr1": "割让量词的领土", "terr2": "割让量词的领土",
        "mnt": "改名换姓（换名元定理）", "elV1": "量词连连消消乐", "elV2": "量词连连消消乐", "elV3": "量词连连消消乐",
        "peano": "皮亚诺公理", "1+1": "1+1=2", "2x2": "2*2=4", "commu+": "加法交换律", "xdistr": "乘法分配率", "3<4": "3小于4",
        "5R6": "5不整除6", "dPrime": "解锁素数", "prm7": "7是素数", "ex!": "任何数都有阶乘", "infprm": "质数有无穷个",
        "aExt": "ZFC集合论", ".<i": "我包含我", "ext<": "我包含我", "empty": "千里之行，始于空集", ".zfc": "ZFC简化大礼包", "UUII": "交交并并",
        "a@a": "我给且只给所有不自己理发的人理发", "vwo": "一切皆可良序", "delAl": "不可数",
        "type": "类型论", "ttrue": "真理之门", "ttsimplFn": "简化依赖函数", "ttactic1": "证明助手上线！", "ttEq": "相等类型", "AllTrue": "True的值都是true",
        "ttindnat": "自然数的归纳法", "tt1+1": "1+1=2类型论版", "ttindeq": "相等的归纳法", "0+x": "代入方程即可", "x+x": "代入方程即可", "1neq2": "1就是1，2就是2（not (eq 1 2)）", "tt5R7": "数论达人(5不整除7)",
        "S1S1": "顺时针一圈逆时针一圈，还是回到原点", "eqvid": "我等价我", "ttua": "泛等公理（ua）", "looprfl": "圆圈跟圆点不同伦（loop不是rfl）", "ttpierce": "原来皮尔士跟他们是一伙的", "lemlie": "排中律是个谎言！？",
    };
    constructor() {
        const gamemode = window.location.search === "?creative" ? "creative" : "survival";
        langMgr.init();
        if (gamemode === "creative") {
            this.creative = true;
        }
        this.fsGui = new FSGui(
            document.getElementById("prop-list") as any,
            document.getElementById("deduct-list") as any,
            document.getElementById("meta-list") as any,
            document.getElementById("action-input") as any,
            document.getElementById("hint") as any,
            document.getElementById("display-p-layer") as any,
            document.querySelectorAll(".cmd-btns button") as any,
            this.creative
        );
        this.ttGui = new TTGui(this.creative);

        document.getElementById("panel").classList.remove("hide");
        this.hyperGui = new HyperGui();

        document.querySelectorAll("#panel>button").forEach((btn, idx) => {
            (btn as HTMLButtonElement).onclick = () => {
                document.querySelectorAll("#panel>div").forEach(a => a.classList.remove("show"));
                document.getElementById("panel-" + idx).classList.add("show");
                if (idx === 0) {
                    this.hyperGui.onresize();
                    this.hyperGui.active = true;
                } else { this.hyperGui.active = false; }
            }
        });
        const astmgr = new ASTMgr;
        this.hyperGui.world.onPassGate = (name: string, tile: TileBlock, hash: string) => {
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
                        if (cmp(ord, [1, 2, 3]) >= 0) this.finishAchievement("ω^ω");
                        if (cmp(ord, [1, 2, 3, 4, 5]) >= 0) this.finishAchievement("ω^ω^ω^ω");
                        this.maxOrd = ord;
                        this.nextOrd = calcMaxReachOrd(ord, this.ordBase, this.rewards.includes("stepw"));
                        this.updateProgressParam();
                        this.hyperGui.world.currentOrd = ord;
                        return true; // smaller or eq next, okay
                    }
                } else if (tile.type === 4) return true;
                if (tile.name === "preord") {
                    return this.parcours >= 256;
                }
                if (tile.name === "I1I2I3") {
                    return (this.rewards.includes("I1") && this.rewards.includes("I2") && this.rewards.includes("I3"));
                }
                if (tile.name === "mct2mdt") {
                    const needed = 20;
                    if (this.deductriums < needed) return false;
                    if (!this.rewards.includes("mct")) return false;
                    this.consumed += needed;
                    this.addDeductriums(-needed);
                    return true;
                }
                if (tile.text.endsWith("#p")) {
                    // if with hyps, fail
                    // if (!this.fsGui.formalSystem.propositions[0]?.from) return false;
                    const ast = this.fsGui.cmd.astparser.parse(tile.text.replaceAll("\n#p", "").replaceAll("\n", ""));
                    return this.fsGui.getProps().findIndex(v => astmgr.equal(v.value, ast)) !== -1;
                }
                if (tile.text.endsWith("#d")) {
                    const ast = this.fsGui.cmd.astparser.parse(tile.text.replaceAll("\n#d", "").replaceAll("\n", ""));
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
                let reg: RegExpMatchArray;
                if ((reg = tile.text.match(/^通过此门需消耗推理素(.+)$/)) && reg[1]) {
                    const needed = parseDeductriumAmout(reg[1]);
                    if (this.deductriums < needed) return false;
                    this.consumed += needed;
                    this.addDeductriums(-needed);
                    return true;
                }
                return false;
            }
            if (!gateTest()) return false;
            const achievement = this.achievementsTable[tile.name ?? tile.text];
            if (achievement) this.finishAchievement(achievement);
            if (this.rewards.includes("delgate") && !this.rewards.includes("hash") && tile.type !== 4) {
                tile.text += "\n （此门已拆除）"; tile.type = 0;
                this.destructedGates++;
                this.updateProgressParam();
                this.rewards.push(name);
            }
            return true;
        }
        this.hyperGui.world.onStepToAnotherTile = () => {
            this.parcours++;
            this.updateProgressParam();
        }
        this.hyperGui.world.onGetReward = (hash: string, tile: TileBlock, isLoading?: boolean) => {
            if (tile.type === TileBlockType.Gate) {
                tile.text += "\n （此门已拆除）";
                if (tile.name && !this.rewards.includes(tile.name)) this.rewards.push(tile.name);
                else if (hash && !this.rewards.includes(hash)) this.rewards.push(hash);
                return;
            }
            if (tile.name === "zh-en" && !isLoading) {
                langMgr.setLang(langMgr.lang === "en" ? "zh" : "en");
                window.location.reload();
            }
            if (tile.name) { if (!this.rewards.includes(tile.name)) this.rewards.push(tile.name); }
            else { if (!this.rewards.includes(hash)) this.rewards.push(hash); }
            const achievement = this.achievementsTable[tile.name];
            if (achievement) this.finishAchievement(achievement, isLoading);
            switch (tile.name) {
                case "dL": return document.getElementById("deduct-btn").classList.remove("hide");
                case "progL": return document.getElementById("progress-btn").classList.remove("hide");
                case "delgate": return;
                case "macro": return document.getElementById("macro-btns").classList.remove("hide");
                case "hyp": return document.getElementById("hyp-btn").classList.remove("hide");
                case "neg": this.fsGui.addToDeductions("a3", "a2"); return;
                case "cmpss": this.hyperGui.world.navigateDraw = true; return;
                case "omega":
                    const tileOmega = this.hyperGui.world.getBlock("w");
                    tileOmega.text += "\n （此门已拆除）"; tileOmega.type = 0;
                    this.destructedGates++; this.updateProgressParam(); return;
                case "delAl":
                    const tileAleph = this.hyperGui.world.getBlock("Aleph");
                    tileAleph.text += "\n （此门已拆除）"; tileAleph.type = 0;
                    this.destructedGates++; this.updateProgressParam(); return;
                case "base-1": case "base-2": case "base-3": case "base-4": case "base-5":
                case "base-6": case "base-7": case "base-8": case "base-9": case "base-10":
                    if (this.ordBase > 5) {
                        this.ordBase--;
                        this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                        this.updateProgressParam();
                    }
                    break;
                case "base5":
                    this.ordBase = 4;
                    this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                    this.updateProgressParam(); break;
                case "base4":
                    this.ordBase = 3;
                    this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                    this.updateProgressParam(); break;
                case "base3":
                    this.ordBase = 2;
                    this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                    this.updateProgressParam(); break;
                case "base2":
                    this.ordBase = 1;
                    this.nextOrd = calcMaxReachOrd(this.maxOrd, this.ordBase, this.rewards.includes("stepw"));
                    this.updateProgressParam(); break;
                case "w^2": case "ww2": case "w^3": case "w4234":
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
                    tileIFF.text += "\n （此门已拆除）"; tileIFF.type = 0;
                    this.destructedGates++; this.updateProgressParam(); return;
                case "delK":
                    const tileK = this.hyperGui.world.getBlock("K");
                    tileK.text += "\n （此门已拆除）"; tileK.type = 0;
                    this.destructedGates++; this.updateProgressParam(); return;
                case "delL":
                    const tileL = this.hyperGui.world.getBlock("L");
                    tileL.text += "\n （此门已拆除）"; tileL.type = 0;
                    this.destructedGates++; this.updateProgressParam(); return;
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
                case ".1st":
                    [
                        ".nEVn", ".nVEn", ".nVVn", ".nEn", ".Ve", ".Vs", ".V&1", ".V&2", ".V&", ".Ee", ".Ei", ".Es", ".EV", ".E|1", ".E|2", ".E|",
                        ".Vnf", ".Vnf>", ".V>nf", ".Vnf|", ".V|nf", ".Vnf&", ".V&nf", ".Enf", ".Enf>", ".E>nf", ".Enf|", ".E|nf", ".Enf&", ".E&nf",
                        ".=s", ".=t", ".=r=", ".=r@"
                    ].forEach(s => this.fsGui.addToDeductions(s));
                    this.fsGui.addToDeductions(".<>rV", ".<>r|");
                    this.fsGui.addToDeductions(".<>rE", ".<>rV");
                    return;
                case "1st":
                    this.fsGui.addToDeductions("a4", "a3");
                    this.fsGui.addToDeductions("a5", "a4");
                    this.fsGui.addToDeductions("a6", "a5");
                    return this.unlockMetarule("q");
                case "iff": this.fsGui.addToDeductions("d<>1"); this.fsGui.addToDeductions("d<>2"); return;
                case "a7": this.fsGui.addToDeductions("a7", "a6"); return;
                case "a8": this.fsGui.addToDeductions("a8", "a7"); return;
                case "dE": this.fsGui.addToDeductions("dE", "a6"); return;
                case "dE!": this.fsGui.addToDeductions("dE!", "dE"); return;
                case "d{}": this.fsGui.addToDeductions("d{}"); return;
                case "d{.}": this.fsGui.addToDeductions("d{.}"); return;
                case "d{..}": this.fsGui.addToDeductions("d{..}"); return;
                case "d<>": this.fsGui.addToDeductions("d<>"); return;
                case "d<": this.fsGui.addToDeductions("d<"); return;
                case "dw": this.fsGui.addToDeductions("domega"); return;
                case "dSd0": this.fsGui.addToDeductions("dS"); this.fsGui.addToDeductions("d0"); return;
                case "dOrder": this.fsGui.addToDeductions("dOrder"); this.fsGui.addToDeductions("dWOrder"); return;
                case "dEquiv": this.fsGui.addToDeductions("dEquiv"); return;
                case "andor": this.fsGui.addToDeductions("d&"); this.fsGui.addToDeductions("d|"); return;
                case "aExt": this.fsGui.addToDeductions("aExt"); if (this.rewards.includes(".zfc")) { this.fsGui.addToDeductions(".aext"); } this.checkAllZFC(isLoading); return;
                case "aPair": this.fsGui.addToDeductions("aPair"); if (this.rewards.includes(".zfc")) { this.fsGui.addToDeductions(".apair"); } this.checkAllZFC(isLoading); return;
                case "aReg": this.fsGui.addToDeductions("aReg"); if (this.rewards.includes(".zfc")) { this.fsGui.addToDeductions(".areg"); } this.checkAllZFC(isLoading); return;
                case "aSep": this.fsGui.addToDeductions("aSep"); if (this.rewards.includes(".zfc")) { this.fsGui.addToDeductions(".asep"); } this.checkAllZFC(isLoading); return;
                case "aUnion": this.fsGui.addToDeductions("aUnion"); if (this.rewards.includes(".zfc")) { this.fsGui.addToDeductions(".aunion"); } this.checkAllZFC(isLoading); return;
                case "aPow": this.fsGui.addToDeductions("aPow"); if (this.rewards.includes(".zfc")) { this.fsGui.addToDeductions(".apow"); } this.checkAllZFC(isLoading); return;
                case "aRepl": this.fsGui.addToDeductions("aRepl"); if (this.rewards.includes(".zfc")) { this.fsGui.addToDeductions(".arepl"); } this.checkAllZFC(isLoading); return;
                case "aInf": this.fsGui.addToDeductions("aInf"); if (this.rewards.includes(".zfc")) { this.fsGui.addToDeductions(".ainf"); } this.checkAllZFC(isLoading); return;
                case "aChoice": this.fsGui.addToDeductions("aChoice"); if (this.rewards.includes(".zfc")) { this.fsGui.addToDeductions(".achoice"); } this.checkAllZFC(isLoading); return;
                case ".zfc":
                    if (this.fsGui.deductions.includes("aExt")) this.fsGui.addToDeductions(".aext", "aExt");
                    if (this.fsGui.deductions.includes("aPair")) this.fsGui.addToDeductions(".apair", "aPair");
                    if (this.fsGui.deductions.includes("aReg")) this.fsGui.addToDeductions(".areg", "aReg");
                    if (this.fsGui.deductions.includes("aSep")) this.fsGui.addToDeductions(".asep", "aSep");
                    if (this.fsGui.deductions.includes("aUnion")) this.fsGui.addToDeductions(".aunion", "aUnion");
                    if (this.fsGui.deductions.includes("aPow")) this.fsGui.addToDeductions(".apow", "aPow");
                    if (this.fsGui.deductions.includes("aRepl")) this.fsGui.addToDeductions(".arepl", "aRepl");
                    if (this.fsGui.deductions.includes("aInf")) this.fsGui.addToDeductions(".ainf", "aInf");
                    if (this.fsGui.deductions.includes("aChoice")) this.fsGui.addToDeductions(".achoice", "aChoice");
                    return;
                case "mct": return this.unlockMetarule("cdt");
                case "mdt": return this.unlockMetarule("dt");
                case "mcpt": return this.unlockMetarule("cpt");
                case "mcmt": return this.unlockMetarule("cmt");
                case "midt": return this.unlockMetarule("idt");
                case "mifft": return this.unlockMetarule("ifft");
                case "mnt": return this.unlockMetarule("nt");
                case "mvt":
                    if (!this.fsGui.metarules.includes("cvt")) {
                        this.unlockMetarule("cvt");
                    }
                    this.unlockMetarule("vt");
                    return;
                case "mcvt": const tileV = this.hyperGui.world.getBlock("V");
                    tileV.text += "\n （此门已拆除）"; tileV.type = 0;
                    this.destructedGates++; this.updateProgressParam();
                    return this.unlockMetarule("cvt");
                case "highlightd": return this.hyperGui.world.highLightGetD = true;

                case "peano":
                    for (let i = 1; i <= 3; i++) this.fsGui.addToDeductions("apn" + i);
                    for (let i = 1; i <= 10; i++) this.fsGui.addToDeductions("d" + i);
                    return;

                case "type": return document.getElementById("type-btn").classList.remove("hide");
                case "ttsimplFn": this.ttGui.disableSimpleFn = false; return this.ttGui.getInhabitatArray()[0].onblur({} as any);
                case "ttnotFn": return this.ttGui.unlock("(False)0", true);
                case "ttEq": for (let i = 0; i < 7; i++)this.ttGui.unlock("eq" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttactic1":
                    this.ttGui.unlockedTactics.add("expand");
                    this.ttGui.unlockedTactics.add("intro");
                    this.ttGui.unlockedTactics.add("apply"); return;
                case "ttNat": this.ttGui.unlock("nat0"); this.ttGui.unlock("nat1"); this.ttGui.unlock("nat2"); this.ttGui.updateAfterUnlock(); return;
                case "ttBool": this.ttGui.unlock("Bool0"); this.ttGui.unlock("Bool1"); this.ttGui.unlock("Bool2"); this.ttGui.updateAfterUnlock(); return;
                case "ttrfl": this.ttGui.unlock("eq7", true); this.ttGui.unlockedTactics.add("rfl"); return;
                case "ttindTrue": for (let i = 2; i < 6; i++)this.ttGui.unlock("True" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttindFalse": for (let i = 1; i < 4; i++)this.ttGui.unlock("False" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttindBool": for (let i = 3; i < 8; i++)this.ttGui.unlock("Bool" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttindnat": for (let i = 3; i < 8; i++)this.ttGui.unlock("nat" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttProd": for (let i = 0; i < 9; i++)this.ttGui.unlock("Prod" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttSum": for (let i = 0; i < 9; i++)this.ttGui.unlock("Sum" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttindProd": for (let i = 9; i < 13; i++)this.ttGui.unlock("Prod" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttindSum": for (let i = 9; i < 14; i++)this.ttGui.unlock("Sum" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttindeq": for (let i = 7; i < 13; i++)this.ttGui.unlock("eq" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttpr": for (let i = 0; i < 6; i++)this.ttGui.unlock("(Prod)" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttinveq": this.ttGui.unlock("(eq)6"); this.ttGui.unlock("(eq)7"); this.ttGui.updateAfterUnlock(); return;
                case "ttcompeq": this.ttGui.unlock("(eq)8"); this.ttGui.unlock("(eq)9"); this.ttGui.updateAfterUnlock(); return;
                case "ttpred": this.ttGui.unlock("(nat)0", true); return;
                case "ttdbl": this.ttGui.unlock("(nat)1", true); return;
                case "ttadd": this.ttGui.unlock("(nat)2", true); return;
                case "ttmul": this.ttGui.unlock("(nat)3", true); return;
                case "ttord": for (let i = 0; i < 10; i++)this.ttGui.unlock("Ord" + i); for (let i = 0; i < 4; i++)this.ttGui.unlock("(Ord)" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttap": for (let i = 0; i < 6; i++)this.ttGui.unlock("(eq)" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttS1": for (let i = 0; i < 4; i++)this.ttGui.unlock("S1" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttindS1": for (let i = 0; i < 7; i++)this.ttGui.unlock("S1" + i); this.ttGui.updateAfterUnlock(); return;
                case "tteqv": for (let i = 0; i < 3; i++)this.ttGui.unlock("eqv" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttua": for (let i = 0; i < 10; i++)this.ttGui.unlock("eqv" + i); this.ttGui.updateAfterUnlock(); return;
                case "ttlazy": this.ttGui.enablecopygate = true; return;
                case "ttsimpl":
                    this.ttGui.unlockedTactics.add("simpl"); return;
                case "ttdestruct":
                    this.ttGui.unlockedTactics.add("destruct"); return;
                case "ttrw":
                    this.ttGui.unlockedTactics.add("rw");
                    this.ttGui.unlockedTactics.add("rwb"); return;
                case "ttacticEx":
                    this.ttGui.unlockedTactics.add("case");
                    this.ttGui.unlockedTactics.add("ex"); return;
                case "ttacticLR":
                    this.ttGui.unlockedTactics.add("left");
                    this.ttGui.unlockedTactics.add("right"); return;
            }
            let reg: RegExpMatchArray;
            if ((reg = tile.name?.match(/^tt(.+)$/)) && reg[1]) {
                return this.ttGui.unlock(reg[1]);
            }

            if ((reg = tile.text.match(/^获取(.+)推理素$/)) && reg[1] && !isLoading) {
                this.addDeductriums(parseDeductriumAmout(reg[1]));
            }


        }
        const progressBtns = Array.from(document.querySelectorAll<HTMLButtonElement>(".progress-btns button"));
        const txtarea = document.getElementById("progress-txtarea") as HTMLTextAreaElement;

        const gameSaveLoad = new GameSaveLoad(gamemode);

        progressBtns[0].addEventListener("click", () => gameSaveLoad.save(this, txtarea));
        progressBtns[1].addEventListener("click", () => {
            const str = prompt(TR("请粘贴进度代码："));
            if (!str.trim()) { alert(TR("进度代码为空！")); } else {
                gameSaveLoad.load(this, str);
                window.location.href = window.location.href || "?";
            }
        });
        progressBtns[2].addEventListener("click", () => gameSaveLoad.reset());
        progressBtns[3].addEventListener("click", () => {langMgr.setLang(langMgr.lang==="en"?"zh":"en");window.location.reload()});

        const saves = localStorage.getItem(gameSaveLoad.storageKey);
        // autosave while updated within a time interval
        this.hyperGui.world.onStateChange = this.ttGui.onStateChange = this.fsGui.onStateChange = () => gameSaveLoad.stateChange(this);

        if (saves) gameSaveLoad.load(this, saves);
        document.getElementById("loading").classList.add("hide");
        langMgr.setLang(langMgr.lang);
        this.hyperGui.needUpdate = true;
    }
    checkAllZFC(mute: boolean) {
        let r = this.fsGui.deductions.includes("aUnion");
        r &&= this.fsGui.deductions.includes("aPair");
        r &&= this.fsGui.deductions.includes("aInf");
        r &&= this.fsGui.deductions.includes("aPow");
        r &&= this.fsGui.deductions.includes("aSep");
        r &&= this.fsGui.deductions.includes("aExt");
        r &&= this.fsGui.deductions.includes("aRepl");
        r &&= this.fsGui.deductions.includes("aReg");
        r &&= this.fsGui.deductions.includes("aChoice");
        if (r) this.finishAchievement("集齐所有ZFC公理", mute);
    }
    addDeductriums(amount: number) {
        this.deductriums += amount;
        this.showHint(TR("推理素") + (amount >= 0 ? "+" : "") + stringifyDeductriumAmout(amount) + "<br>" + TR("共") + stringifyDeductriumAmout(this.deductriums));
        if (amount < 0) this.finishAchievement("第一次消费");
        if (amount > 0) this.finishAchievement("吃素啦");
        const totalObtained = this.deductriums + this.consumed;
        if (totalObtained >= 40) this.finishAchievement("素食主义者（累计获40µg推理素）");
        if (totalObtained >= 1000) this.finishAchievement("加大剂量（累计获1mg推理素）");
        if (totalObtained >= 1e6) this.finishAchievement("致死剂量（累计获1g推理素）");
        if (totalObtained >= 50.1e9) this.finishAchievement("临界质量（累计获50.1kg推理素）");
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
    showHint(text: string) {
        const dom = document.createElement("div");
        document.body.appendChild(dom);
        dom.innerHTML = text;
        dom.classList.add("hintbar");
        setTimeout(() => {
            document.body.removeChild(dom);
        }, 5000);
    }
    finishAchievement(a: string, mute?: boolean) {
        if (this.rewards.includes("[ach]" + a)) return;
        for (const d of document.querySelectorAll(".achievement div") as any as Array<HTMLDivElement>) {
            // if (d.innerText === a) {
            if (d.getAttribute("data-tr") === a) {
                d.classList.add("achieved");
                d.parentElement.classList.remove("locked");
                break;
            }
        }
        if (!mute) this.showHint("<br><br><br><div style='border:solid;border-radius:0.3em; padding:0.3em'>" + TR("获得成就：") + "<br>" + TR(a) + "</div>");
        this.rewards.push("[ach]" + a);
    }
    unlockMetarule(name: string) {
        this.fsGui.metarules.push(name);
        this.fsGui.formalSystem.fastmetarules += {
            "cdt": "c",
            "dt": ">",
            "idt": "<",
            "cvt": "v",
            "vt": "u",
            "cmt": ":",
            "q": "q",
        }[name] || "";
        this.fsGui.updateMetaRuleList(true);
        document.getElementById("metarule-subpanel").classList.remove("hide");
    }
}

new Game;