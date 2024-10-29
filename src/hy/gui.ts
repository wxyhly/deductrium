import { HWorld } from "./hworld.js";
export class HyperGui {
    canvas = document.getElementById("hyper") as HTMLCanvasElement;
    world = new HWorld(this.canvas);
    moveSpeed = 0.5;
    touchSpeed = 0.1;
    needUpdate = false;
    keyDowns: Set<string>;
    prevTime = new Date().getTime();
    touchDx = 0; touchDy = 0;
    active = true;
    constructor() {
        window.onresize = () => { this.onresize(); }
        this.onresize();
        this.keyDowns = new Set<string>;
        this.canvas.addEventListener("mousemove", ev => {
            if (!(ev.buttons & 1)) return;
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
        })
        this.canvas.addEventListener("mousedown", ev => {
            if (ev.button !== 2) return;
            ev.preventDefault();
            ev.stopPropagation();
            // this.world.texts.push([this.guiDraw.currentTile, this.guiDraw.camMat.conj().apply(new Hvec), "oma"]);
            this.needUpdate = true;
        });
        let touchStartX = 0; let touchStartY = 0;
        this.canvas.addEventListener("touchstart", ev => {
            ev.preventDefault();
            ev.stopPropagation();
            touchStartX = ev.targetTouches[0].clientX;
            touchStartY = ev.targetTouches[0].clientY;
        });
        this.canvas.addEventListener("touchmove", ev => {
            ev.preventDefault();
            ev.stopPropagation();
            this.touchDx = ev.targetTouches[0].clientX - touchStartX;
            this.touchDy = ev.targetTouches[0].clientY - touchStartY;
        });
        this.canvas.addEventListener("contextmenu", ev => {
            ev.preventDefault();
            ev.stopPropagation();
            return false;
        });
        this.mainLoop(1 / 60);
    }
    onresize() {
        if (!this.canvas.clientHeight || !this.canvas.clientWidth) return;
        this.canvas.width = this.canvas.clientWidth * window.devicePixelRatio;
        this.canvas.height = this.canvas.clientHeight * window.devicePixelRatio;
        this.world.onLoop();
    }
    mainLoop(deltaTime: number) {
        if (this.active) {
            if (this.touchDx || this.touchDy) {
                this.world.moveCam(this.touchSpeed * this.touchDx / this.canvas.width, -this.touchSpeed * this.touchDy / this.canvas.width);
                this.touchDx = 0;
                this.touchDy = 0;
                this.needUpdate = true;
            }
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
        }
        const newDt = (new Date().getTime() - this.prevTime) / 1000;
        window.requestAnimationFrame(() => { this.mainLoop(Math.min(newDt, 0.3)); });
        this.prevTime = new Date().getTime();
    }
}