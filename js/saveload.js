import { SavesParser as FsSavesParser } from "./fs/savesparser.js";
import { SavesParser as HySavesParser } from "./hy/savesparser.js";
import { SavesParser as TtSavesParser } from "./tt/savesparser.js";
const splittor = "-(=)-";
export class GameSaveLoad {
    stateChangeTimer = false;
    timeOut = 3000;
    stateChange(game) {
        if (this.stateChangeTimer === false) {
            this.stateChangeTimer = setTimeout(() => {
                this.save(game);
                this.stateChangeTimer = false;
            }, this.timeOut);
        }
    }
    load(game, str, skipRollback) {
        const rollback = this.save(game);
        try {
            const [globaldata, hydata, fsdata, ttdata] = str.split(splittor);
            this.deserialize(game, globaldata);
            new HySavesParser().deserialize(game.hyperGui.world, hydata);
            game.hyperGui.needUpdate = true;
            new FsSavesParser().deserialize(game.fsGui, fsdata);
            new TtSavesParser().deserialize(game.ttGui, ttdata);
            localStorage.setItem("deductrium-save", str);
        }
        catch (e) {
            if (!skipRollback) {
                alert("进度代码格式错误：" + e);
                this.load(game, rollback, true);
            }
            else {
                console.error(e);
            }
        }
    }
    save(game, dom) {
        const fsdata = new FsSavesParser().serialize(game.fsGui);
        const hydata = new HySavesParser().serialize(game.hyperGui.world);
        const ttdata = new TtSavesParser().serialize(game.ttGui);
        const globaldata = this.serialize(game);
        const data = [globaldata, hydata, fsdata, ttdata].join(splittor);
        localStorage.setItem("deductrium-save", data);
        if (!dom)
            return data;
        dom.value = data;
        dom.focus();
    }
    reset() {
        if (confirm("确定要放弃所有游戏进度吗？")) {
            localStorage.removeItem("deductrium-save");
            window.location.href = "?";
        }
    }
    serialize(game) {
        return JSON.stringify([game.rewards, game.deductriums, game.consumed, game.destructedGates, game.parcours]);
    }
    deserialize(game, data) {
        let rewards;
        let deductriums;
        let consumed;
        let destructedGates;
        let parcours;
        [rewards, deductriums, consumed, destructedGates, parcours] = JSON.parse(data);
        for (const r of rewards) {
            game.hyperGui.world.hitReward(game.hyperGui.world.getBlock(r), r, true);
        }
        // caution: rewards can modify deductriums
        game.deductriums = deductriums;
        game.consumed = consumed;
        game.destructedGates = destructedGates;
        game.parcours = parcours;
        game.updateProgressParam();
    }
}
//# sourceMappingURL=saveload.js.map