import { ASTMgr } from "./fs/astmgr.js";
import { FSGui } from "./fs/gui.js";
import { HyperGui } from "./hy/gui.js"
import { TileBlock } from "./hy/maploader.js";
class Game {
    fsGui: FSGui;
    hyperGui: HyperGui;
    constructor() {
        this.fsGui = new FSGui(
            document.getElementById("prop-list") as any,
            document.getElementById("deduct-list") as any,
            document.getElementById("meta-list") as any,
            document.getElementById("action-input") as any,
            document.getElementById("hint") as any,
            document.getElementById("display-p-layer") as any,
            document.getElementById("cmd-btns") as any,
        );
        document.querySelectorAll("#panel>button").forEach((btn, idx) => {
            (btn as HTMLButtonElement).onclick = () => {
                document.querySelectorAll("#panel>div").forEach(a => a.classList.remove("show"));
                document.getElementById("panel-" + idx).classList.add("show");
            }
        });
        this.hyperGui = new HyperGui();
        const astmgr = new ASTMgr;
        this.hyperGui.world.onPassGate = (hash: string, tile: TileBlock) => {
            if (tile.text.endsWith("#p")) {
                // if with hyps, fail
                if (!this.fsGui.formalSystem.propositions[0]?.from) return false;
                const ast = this.fsGui.cmd.astparser.parse(tile.text.replaceAll("\n#p", "").replaceAll("\n", ""));
                return this.fsGui.formalSystem.propositions.findIndex(v => astmgr.equal(v.value, ast)) !== -1;
            }
            return false;
        }
        this.hyperGui.world.onGetReward = (hash: string, tile: TileBlock) => {

            switch (tile.name) {
                case "unlock-deduct": document.getElementById("deduct-btn").classList.remove("hide");
            }
        }
    }
}
new Game;