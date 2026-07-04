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
    outside = false;
    touchStartX = 0; touchStartY = 0;
    blur(){
        this.keyDowns.clear();
    }
    constructor() {
        window.onresize = () => { this.onresize(); }
        this.onresize();
        this.keyDowns = new Set<string>;
        this.canvas.addEventListener("mousemove", ev => {
            if (!(ev.buttons & 1)) return;
            if (this.outside) {
                const startX = ev.offsetX - ev.movementX;
                const startY = ev.offsetY - ev.movementY;
                const centerX = this.canvas.width / 2 / window.devicePixelRatio;
                const centerY = this.canvas.height / 2 / window.devicePixelRatio;
                this.world.rotate(Math.atan2(startY - centerY, startX - centerX) - Math.atan2(ev.offsetY - centerY, ev.offsetX - centerX));
            } else this.world.moveCam(-ev.movementX / 1000, ev.movementY / 1000);
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
            // if (ev.button !== 2) return;
            ev.preventDefault();
            ev.stopPropagation();

            this.outside = this.world.localDraw.hitTestPoincareDisk(ev.offsetX, ev.offsetY);

            this.needUpdate = true;
        });
        this.canvas.addEventListener("touchstart", ev => {
            ev.preventDefault();
            ev.stopPropagation();
            this.touchStartX = ev.targetTouches[0].clientX;
            this.touchStartY = ev.targetTouches[0].clientY;
            this.outside = this.world.localDraw.hitTestPoincareDisk(
                ev.targetTouches[0].clientX - this.canvas.getBoundingClientRect().left,
                ev.targetTouches[0].clientY - this.canvas.getBoundingClientRect().top
            );
        });
        const prettyPrintInput = document.querySelector("#panel-0 input") as HTMLInputElement;
        prettyPrintInput.onfocus = () => prettyPrintInput.blur();
        prettyPrintInput.addEventListener('change', (e) => {
            this.world.prettyPrint = !prettyPrintInput.checked;
            this.needUpdate = true;
        })
        this.canvas.addEventListener("touchmove", ev => {
            ev.preventDefault();
            ev.stopPropagation();
            this.touchDx = ev.targetTouches[0].clientX - this.touchStartX;
            this.touchDy = ev.targetTouches[0].clientY - this.touchStartY;
            if (this.outside) { this.touchStartX = ev.targetTouches[0].clientX; this.touchStartY = ev.targetTouches[0].clientY; }
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
                if (this.outside) {
                    const centerX = this.canvas.width / 2 / window.devicePixelRatio;
                    const centerY = this.canvas.height / 2 / window.devicePixelRatio;
                    const startX = this.touchStartX - this.canvas.getBoundingClientRect().left;
                    const startY = this.touchStartY - this.canvas.getBoundingClientRect().top;
                    const endX = startX + this.touchDx;
                    const endY = startY + this.touchDy;
                    this.world.rotate(Math.atan2(startY - centerY, startX - centerX) - Math.atan2(endY - centerY, endX - centerX));
                }
                else
                    this.world.moveCam(this.touchSpeed * this.touchDx / this.canvas.width, -this.touchSpeed * this.touchDy / this.canvas.width);
                this.touchDx = 0;
                this.touchDy = 0;
                this.needUpdate = true;
            }
            if (this.keyDowns.has("KeyW") || this.keyDowns.has("ArrowUp")) {
                this.world.moveCam(0, this.moveSpeed * deltaTime);
                this.needUpdate = true;
            }
            if (this.keyDowns.has("KeyS") || this.keyDowns.has("ArrowDown")) {
                this.world.moveCam(0, -this.moveSpeed * deltaTime);
                this.needUpdate = true;
            }
            if (this.keyDowns.has("KeyA") || this.keyDowns.has("ArrowLeft")) {
                this.world.moveCam(-this.moveSpeed * deltaTime, 0);
                this.needUpdate = true;
            }
            if (this.keyDowns.has("KeyD") || this.keyDowns.has("ArrowRight")) {
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