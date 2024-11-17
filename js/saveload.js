import { SavesParser as FsSavesParser } from "./fs/savesparser.js";
import { calcMaxReachOrd } from "./hy/ordinal.js";
import { SavesParser as HySavesParser } from "./hy/savesparser.js";
import { SavesParser as TtSavesParser } from "./tt/savesparser.js";
const splittor = "-(=)-";
const dict = {
    ',"aE0","aPair","aPow","aUnion","areg","arepl","asep","ainf",': "a#`",
    '"0","1","2","3","4","5","6","7","8","9","10"': "b#`",
    '"Union","Pow","S"': "c#`",
    ',"apn1","apn2","apn3","d1","d2","d3","d4","d5","d6","d7","d8","d9",': "d#`",
    '","2,2,4,2,': '@`',
    '3,3,3,3,': '3`',
    '2,2,2,2,2,2,': '6`',
    '1,1,1,1,1,1,': '1`',
    '素食主义者（累计获40µg推理素）': '#4`',
    '你推出你，他推出他（⊢$0>$0）': '#2`',
    '会跑的“⊢”（演绎元定理）': '#3`',
    '第一次消费': '#1`',
    '[["progL","[ach]解锁了成就",': 'ch`',
    '","[ach]': '2`',
    '","录制*",[["': '*`',
    ',["mp",[': 'm`',
    '],[]]]],"': '[`',
    '",[],["': '{`',
    '","a': 'a`',
    '","d': 'd`',
};
const replaceArr1 = Object.entries(dict);
const replaceArr2 = replaceArr1.slice(0).reverse();
export class GameSaveLoad {
    storageKey = "deductrium-save";
    constructor(gamemode) {
        if (gamemode === "creative") {
            this.storageKey = "deductrium-creative-save";
            document.getElementById("gamemode").innerText = "[创造模式]";
            const panels = document.querySelectorAll("#panel>button");
            panels[0].classList.add("hide");
            panels[1].classList.remove("hide");
            panels[2].classList.remove("hide");
            panels[3].classList.remove("hide");
            panels[3].click();
        }
    }
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
            const [globaldata, hydata, fsdata, ttdata] = this.deserializeStr(str).split(splittor);
            this.deserialize(game, globaldata);
            new HySavesParser().deserialize(game.hyperGui.world, hydata);
            game.hyperGui.needUpdate = true;
            new FsSavesParser(game.creative).deserialize(game.fsGui, fsdata);
            new TtSavesParser().deserialize(game.ttGui, ttdata);
            localStorage.setItem(this.storageKey, str);
        }
        catch (e) {
            if (!skipRollback) {
                alert("进度代码格式错误：" + e);
                console.warn("进度代码格式错误：");
                console.warn(str);
                console.warn("进度已回滚。");
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
        const data = this.serializeStr([globaldata, hydata, fsdata, ttdata].join(splittor));
        localStorage.setItem(this.storageKey, data);
        if (!dom)
            return data;
        dom.value = data;
        dom.focus();
    }
    reset() {
        if (confirm("确定要放弃所有游戏进度吗？")) {
            localStorage.removeItem(this.storageKey);
            window.location.href = window.location.href || "?";
        }
    }
    serialize(game) {
        return JSON.stringify([
            game.rewards, game.deductriums, game.consumed,
            game.destructedGates, game.parcours, game.maxOrd, game.ordBase
        ]);
    }
    deserialize(game, data) {
        let rewards;
        let deductriums;
        let consumed;
        let destructedGates;
        let maxOrd, ordBase;
        [
            rewards, deductriums, consumed, destructedGates,
            game.parcours, maxOrd, ordBase
        ] = JSON.parse(data);
        for (const r of rewards) {
            if (r.startsWith("[ach]")) {
                game.finishAchievement(r.slice(5), true);
            }
            else {
                game.hyperGui.world.hitReward(game.hyperGui.world.getBlock(r), r, true);
            }
        }
        // caution: rewards can modify deductriums, maxOrds and ordBases
        game.deductriums = deductriums;
        game.consumed = consumed;
        game.destructedGates = destructedGates;
        game.maxOrd = maxOrd;
        game.ordBase = ordBase;
        game.nextOrd = calcMaxReachOrd(game.maxOrd, game.ordBase, game.rewards.includes("stepw"));
        game.updateProgressParam();
    }
    serializeStr(json) {
        for (const [a, b] of replaceArr1) {
            json = json.replaceAll(a, b);
        }
        let randomFunction = new Rnd(this.storageKey === "deductrium-save" ? json.length : (json.length - 1));
        console.log(json);
        const l78z = Shuffle.shuffleArray(Array.from(json), randomFunction);
        return l78z.join("");
    }
    deserializeStr(str) {
        let randomFunction = new Rnd(this.storageKey === "deductrium-save" ? str.length : (str.length - 1));
        str = Shuffle.shuffleArrayReverse(Array.from(str), randomFunction);
        for (const [a, b] of replaceArr2) {
            str = str.replaceAll(b, a);
        }
        return str;
    }
}
class Rnd {
    x;
    constructor(x) { this.x = x; }
    next() {
        this.x = ((this.x + 0x19da44d9) + (this.x << 8)) >>> 0;
        this.x = (this.x ^ (this.x >>> 4)) >>> 0;
        this.x = ((this.x * 0xb5502e5) + (this.x >>> 0)) >>> 0;
        return (this.x >>> 0) / 0x100000000;
    }
}
class Shuffle {
    static shuffleArray(array, randomFunction) {
        for (let i = array.length - 1; i > 0; i--) {
            const j = Math.floor(randomFunction.next() * (i + 1));
            [array[i], array[j]] = [array[j], array[i]];
        }
        return array;
    }
    static shuffleArrayReverse(array, randomFunction) {
        const nums = new Array(array.length).fill(0).map((_, i) => i);
        Shuffle.shuffleArray(nums, randomFunction);
        const res = new Array(array.length);
        for (const [i, j] of nums.entries()) {
            res[j] = array[i];
        }
        return res.join("");
    }
}
//# sourceMappingURL=saveload.js.map