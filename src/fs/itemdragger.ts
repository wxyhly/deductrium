
export class ListDragger {
    list: HTMLElement;
    constructor(list: HTMLElement) {
        this.list = list;
    }
    cols = 8;
    srcName: string = null;
    dstName: string = null;
    dragging = false;
    onExecute: (src: string, dst: string) => void = () => { };
    startY = 0;
    attachIdxListener(dom?: HTMLElement) {
        const cb = (idx: HTMLElement) => {
            idx.onmousedown = null;
            idx.onmousedown = (ev) => {
                ev.preventDefault();
                this.startDrag(idx, ev as MouseEvent);
            };
            idx.ontouchstart = (te) => {
                const touch = te.touches[0];
                const startX = touch.clientX;
                const startY = touch.clientY;
                let longPressTimer: number | null = null;
                let moved = false;
                longPressTimer = window.setTimeout(() => {
                    if (!moved) {
                        this.startDrag(idx, { clientX: startX, clientY: startY } as MouseEvent);
                    }
                }, 300);

                const cancel = () => {
                    if (longPressTimer) {
                        clearTimeout(longPressTimer);
                        longPressTimer = null;
                    }
                    document.removeEventListener("touchmove", moveCheck);
                    document.removeEventListener("touchend", cancel);
                    document.removeEventListener("touchcancel", cancel);
                };

                const moveCheck = (ev: TouchEvent) => {
                    const t = ev.touches[0];
                    const dx = t.clientX - startX;
                    const dy = t.clientY - startY;
                    if (Math.abs(dx) > 5 || Math.abs(dy) > 5) {
                        moved = true;
                        cancel();
                    }
                };

                document.addEventListener("touchmove", moveCheck);
                document.addEventListener("touchend", cancel);
                document.addEventListener("touchcancel", cancel);
            };
        };
        if (!dom) {
            this.list.querySelectorAll<HTMLElement>('.idx').forEach(cb);
        } else {
            cb(dom);
        }
    }
    update() {
        this.attachIdxListener();
    }

    startDrag(idxEl: HTMLElement, ev: MouseEvent) {
        const allChildren = Array.from(this.list.children) as HTMLElement[];
        const childIndex = allChildren.indexOf(idxEl);
        if (childIndex === -1) return;

        const rowStart = Math.floor(childIndex / this.cols) * this.cols;
        for (let i = 0; i < this.cols; i++) {
            const el = allChildren[rowStart + i] as HTMLElement | undefined;
            if (!el) continue;
            el.classList.add("dragging");
        }
        this.dragging = true;
        this.startY = ev.clientY;
        this.srcName = idxEl.innerText;

        document.addEventListener('mousemove', this.onMove.bind(this));
        document.addEventListener('mouseup', this.onUp.bind(this));
        document.addEventListener('touchmove', this.onTouchMove.bind(this), { passive: false });
        document.addEventListener('touchend', this.onTouchEnd.bind(this));
    }

    onTouchMove(e: TouchEvent) {
        if (!this.dragging) return;
        e.preventDefault();
        const t = e.touches[0];
        this.onMove({ clientX: t.clientX, clientY: t.clientY } as unknown as MouseEvent);
    }
    onTouchEnd() {
        this.onUp();
    }

    onMove(e: MouseEvent) {
        if (!this.dragging) return;

        const children = Array.from(this.list.children) as HTMLElement[];
        const rowCount = Math.ceil(children.length / this.cols);

        let inserted = false;
        this.list.querySelectorAll(".idx").forEach(e => {
            e.classList.remove("dragging-bottom");
            e.classList.remove("dragging-top");
        });
        for (let r = 0; r < rowCount; r++) {
            const firstIndex = r * this.cols;
            const firstChild = children[firstIndex];
            if (!firstChild) continue;
            const rect = firstChild.getBoundingClientRect();
            const midY = rect.top + rect.height / 2;
            if (e.clientY < midY) {
                this.dstName = firstChild.innerText;
                firstChild.classList.add("dragging-top");
                inserted = true;
                break;
            }
        }
        if (!inserted) {
            this.dstName = " ";
            children[(rowCount - 1) * this.cols].classList.add("dragging-bottom");
        }
    }

    onUp() {
        if (!this.dragging) return;
        this.dragging = false;
        this.list.querySelectorAll("div").forEach(e => {
            e.classList.remove("dragging-bottom");
            e.classList.remove("dragging-top");
            e.classList.remove("dragging");
        });
        this.onExecute(this.srcName, this.dstName);
        this.srcName = null;
        document.removeEventListener('mousemove', this.onMove);
        document.removeEventListener('mouseup', this.onUp);
        document.removeEventListener('touchmove', this.onTouchMove);
        document.removeEventListener('touchend', this.onTouchEnd);

    }
}