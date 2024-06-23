import { HWorld } from "./hworld.js";
export class HyperGui {
    canvas = document.getElementById("hyper");
    world = new HWorld(this.canvas);
    moveSpeed = 0.1;
    needUpdate = false;
    keyDowns;
    prevTime = new Date().getTime();
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
        this.mainLoop(1 / 60);
    }
    onresize() {
        this.canvas.width = this.canvas.clientWidth;
        this.canvas.height = this.canvas.clientHeight;
        this.world.onLoop();
    }
    mainLoop(deltaTime) {
        if (this.keyDowns.has("KeyW")) {
            this.world.moveCam(0, this.moveSpeed * deltaTime);
            this.needUpdate = true;
        }
        if (this.keyDowns.has("KeyS")) {
            this.world.moveCam(0, -this.moveSpeed * deltaTime);
            this.needUpdate = true;
        }
        if (this.keyDowns.has("KeyA")) {
            this.world.moveCam(-this.moveSpeed * deltaTime, 0);
            this.needUpdate = true;
        }
        if (this.keyDowns.has("KeyD")) {
            this.world.moveCam(this.moveSpeed * deltaTime, 0);
            this.needUpdate = true;
        }
        if (this.needUpdate) {
            this.world.onLoop();
            this.needUpdate = false;
        }
        const newDt = (new Date().getTime() - this.prevTime) / 1000;
        window.requestAnimationFrame(() => { this.mainLoop(Math.min(newDt, 0.1)); });
    }
}
//# sourceMappingURL=gui.js.map