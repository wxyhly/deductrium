import { ASTMgr } from "./fs/astmgr.js";
import { FSGui } from "./fs/gui.js";
import { HyperGui } from "./hy/gui.js";
class Game {
    fsGui;
    hyperGui;
    constructor() {
        this.fsGui = new FSGui(document.getElementById("prop-list"), document.getElementById("deduct-list"), document.getElementById("meta-list"), document.getElementById("action-input"), document.getElementById("hint"), document.getElementById("display-p-layer"), document.getElementById("cmd-btns"));
        document.querySelectorAll("#panel>button").forEach((btn, idx) => {
            btn.onclick = () => {
                document.querySelectorAll("#panel>div").forEach(a => a.classList.remove("show"));
                document.getElementById("panel-" + idx).classList.add("show");
            };
        });
        this.hyperGui = new HyperGui();
        const astmgr = new ASTMgr;
        this.hyperGui.world.onPassGate = (hash, tile) => {
            if (tile.text.endsWith("#p")) {
                // if with hyps, fail
                if (!this.fsGui.formalSystem.propositions[0]?.from)
                    return false;
                const ast = this.fsGui.cmd.astparser.parse(tile.text.replaceAll("\n#p", "").replaceAll("\n", ""));
                return this.fsGui.formalSystem.propositions.findIndex(v => astmgr.equal(v.value, ast)) !== -1;
            }
            return false;
        };
        this.hyperGui.world.onGetReward = (hash, tile) => {
            switch (tile.name) {
                case "unlock-deduct": document.getElementById("deduct-btn").classList.remove("hide");
            }
        };
    }
}
new Game;
//# sourceMappingURL=game.js.map