import { ASTMgr } from "./fs/astmgr.js";
import { FSGui } from "./fs/gui.js";
import { HyperGui } from "./hy/gui.js";
import { TileBlockType } from "./hy/maploader.js";
import { GameSaveLoad } from "./saveload.js";
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
    constructor() {
        this.fsGui = new FSGui(document.getElementById("prop-list"), document.getElementById("deduct-list"), document.getElementById("meta-list"), document.getElementById("action-input"), document.getElementById("hint"), document.getElementById("display-p-layer"), document.querySelectorAll(".cmd-btns button"));
        document.querySelectorAll("#panel>button").forEach((btn, idx) => {
            btn.onclick = () => {
                document.querySelectorAll("#panel>div").forEach(a => a.classList.remove("show"));
                document.getElementById("panel-" + idx).classList.add("show");
            };
        });
        this.ttGui = new TTGui;
        this.hyperGui = new HyperGui();
        const astmgr = new ASTMgr;
        this.hyperGui.world.onPassGate = (hash, tile) => {
            const gateTest = () => {
                if (tile.text.endsWith("#p")) {
                    // if with hyps, fail
                    if (!this.fsGui.formalSystem.propositions[0]?.from)
                        return false;
                    const ast = this.fsGui.cmd.astparser.parse(tile.text.replaceAll("\n#p", "").replaceAll("\n", ""));
                    return this.fsGui.formalSystem.propositions.findIndex(v => astmgr.equal(v.value, ast)) !== -1;
                }
                if (tile.text.endsWith("#d")) {
                    const ast = this.fsGui.cmd.astparser.parse(tile.text.replaceAll("\n#d", "").replaceAll("\n", ""));
                    return Object.values(this.fsGui.formalSystem.deductions).findIndex(v => astmgr.equal(v.value, ast) && v.from.endsWith("*")) !== -1;
                }
                if (tile.text.endsWith("#t")) {
                    return this.ttGui.queryType(tile.text.replaceAll("\n#t", "").replaceAll("\n", ""));
                }
                let reg;
                if ((reg = tile.text.match(/^通过此门需消耗推理素(.+)$/)) && reg[1]) {
                    const needed = parseDeductriumAmout(reg[1]);
                    if (this.deductriums < needed)
                        return false;
                    this.consumed += needed;
                    this.addDeductriums(-needed);
                    return true;
                }
                return false;
            };
            if (!gateTest())
                return true;
            if (this.rewards.includes("delgate") && !this.rewards.includes("hash")) {
                tile.text += "\n（此门已拆除）";
                tile.type = 0;
                this.destructedGates++;
                this.updateProgressParam();
                this.rewards.push(hash);
            }
            return true;
        };
        this.hyperGui.world.onStepToAnotherTile = () => {
            this.parcours++;
            this.updateProgressParam();
        };
        this.hyperGui.world.onGetReward = (hash, tile, isLoading) => {
            if (tile.type === TileBlockType.Gate) {
                tile.text += "\n（此门已拆除）";
                return;
            }
            if (tile.name) {
                if (!this.rewards.includes(tile.name))
                    this.rewards.push(tile.name);
            }
            else {
                if (!this.rewards.includes(hash))
                    this.rewards.push(hash);
            }
            switch (tile.name) {
                case "dL": return document.getElementById("deduct-btn").classList.remove("hide");
                case "progL": return document.getElementById("progress-btn").classList.remove("hide");
                case "delgate": return;
                case "macro": return document.getElementById("macro-btns").classList.remove("hide");
                case "hyp": return document.getElementById("hyp-btn").classList.remove("hide");
                case "neg":
                    this.fsGui.addToDeductions("a3", "a2");
                    return;
                case "del<>":
                    const tileIFF = this.hyperGui.world.getBlock("port-iff");
                    tileIFF.text += "\n（此门已拆除）";
                    tileIFF.type = 0;
                    this.destructedGates++;
                    this.updateProgressParam();
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
                case "d<>":
                    this.fsGui.addToDeductions("d<>");
                    return;
                case "d<":
                    this.fsGui.addToDeductions("d<");
                    return;
                case "andor":
                    this.fsGui.addToDeductions("d&");
                    this.fsGui.addToDeductions("d|");
                    return;
                case "aExt":
                    this.fsGui.addToDeductions("aExt");
                    return;
                case "aPair":
                    this.fsGui.addToDeductions("aPair");
                    return;
                case "aReg":
                    this.fsGui.addToDeductions("aReg");
                    return;
                case "mct": return this.unlockMetarule("cdt");
                case "mdt": return this.unlockMetarule("dt");
                case "mcpt": return this.unlockMetarule("cpt");
                case "mifft": return this.unlockMetarule("ifft");
                case "highlightd": return this.hyperGui.world.highLightGetD = true;
                case "type": return document.getElementById("type-btn").classList.remove("hide");
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
        const gameSaveLoad = new GameSaveLoad();
        progressBtns[0].addEventListener("click", () => gameSaveLoad.save(this, txtarea));
        progressBtns[1].addEventListener("click", () => {
            const str = prompt("请粘贴进度代码：");
            if (!str.trim()) {
                alert("进度代码为空！");
            }
            else {
                gameSaveLoad.load(this, str);
                window.location.href = "?";
            }
        });
        progressBtns[2].addEventListener("click", () => gameSaveLoad.reset());
        const saves = localStorage.getItem("deductrium-save");
        // autosave while updated within a time interval
        this.hyperGui.world.onStateChange = this.ttGui.onStateChange = this.fsGui.onStateChange = () => gameSaveLoad.stateChange(this);
        if (saves)
            gameSaveLoad.load(this, saves);
    }
    addDeductriums(amount) {
        this.deductriums += amount;
        this.showHint("推理素" + (amount >= 0 ? "+" : "") + stringifyDeductriumAmout(amount) + "\n共" + stringifyDeductriumAmout(this.deductriums));
    }
    updateProgressParam() {
        document.getElementById("deductrium-amount").innerText = stringifyDeductriumAmout(this.deductriums);
        document.getElementById("deductrium-consumed").innerText = stringifyDeductriumAmout(this.consumed);
        document.getElementById("parcours-tiles").innerText = this.parcours.toString();
        document.getElementById("destructed-gates").innerText = this.destructedGates.toString();
    }
    showHint(text) {
        const dom = document.createElement("div");
        document.body.appendChild(dom);
        dom.innerText = text;
        dom.classList.add("hintbar");
        setTimeout(() => {
            document.body.removeChild(dom);
        }, 5000);
    }
    unlockMetarule(name) {
        this.fsGui.metarules.push(name);
        this.fsGui.updateMetaRuleList(true);
        document.getElementById("metarule-subpanel").classList.remove("hide");
    }
}
new Game;
//# sourceMappingURL=game.js.map