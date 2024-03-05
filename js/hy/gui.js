import { HWorld } from "./hworld.js";
export class HyperGui {
    canvas = document.getElementById("hyper");
    world = new HWorld(this.canvas);
    moveSpeed = 0.005;
    needUpdate = false;
    keyDowns;
    constructor() {
        window.onresize = () => { this.onresize(); };
        this.onresize();
        this.keyDowns = new Set;
        this.canvas.addEventListener("mousemove", ev => {
            if (!(ev.buttons & 1))
                return;
            this.world.moveCam(-ev.movementX / 1000, ev.movementY / 1000);
            this.needUpdate = true;
        });
        document.addEventListener("keydown", ev => {
            this.keyDowns.add(ev.code);
        });
        document.addEventListener("keyup", ev => {
            this.keyDowns.delete(ev.code);
        });
        document.addEventListener("blur", ev => {
            this.keyDowns.clear();
        });
        this.canvas.addEventListener("mousedown", ev => {
            if (ev.button !== 2)
                return;
            ev.preventDefault();
            ev.stopPropagation();
            // this.world.texts.push([this.guiDraw.currentTile, this.guiDraw.camMat.conj().apply(new Hvec), "oma"]);
            this.needUpdate = true;
        });
        this.canvas.addEventListener("contextmenu", ev => {
            ev.preventDefault();
            ev.stopPropagation();
            return false;
        });
        this.mainLoop();
    }
    onresize() {
        this.canvas.width = this.canvas.clientWidth;
        this.canvas.height = this.canvas.clientHeight;
        this.world.onLoop();
    }
    mainLoop() {
        if (this.keyDowns.has("KeyW")) {
            this.world.moveCam(0, this.moveSpeed);
            this.needUpdate = true;
        }
        if (this.keyDowns.has("KeyS")) {
            this.world.moveCam(0, -this.moveSpeed);
            this.needUpdate = true;
        }
        if (this.keyDowns.has("KeyA")) {
            this.world.moveCam(-this.moveSpeed, 0);
            this.needUpdate = true;
        }
        if (this.keyDowns.has("KeyD")) {
            this.world.moveCam(this.moveSpeed, 0);
            this.needUpdate = true;
        }
        if (this.needUpdate) {
            this.world.onLoop();
            this.needUpdate = false;
        }
        window.requestAnimationFrame(() => { this.mainLoop(); });
    }
}
//# sourceMappingURL=gui.js.map