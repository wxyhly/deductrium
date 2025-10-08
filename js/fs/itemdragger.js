export class ListDragger {
    list;
    constructor(list) {
        this.list = list;
    }
    cols = 8;
    srcName = null;
    dstName = null;
    dragging = false;
    onExecute = () => { };
    startY = 0;
    attachIdxListener(dom) {
        const cb = (idx) => {
            idx.onmousedown = null;
            idx.onmousedown = (ev) => {
                ev.preventDefault();
                this.startDrag(idx, ev);
            };
            idx.ontouchstart = (te) => {
                const touch = te.touches[0];
                te.preventDefault();
                this.startDrag(idx, { clientX: touch.clientX, clientY: touch.clientY });
            };
        };
        if (!dom) {
            this.list.querySelectorAll('.idx').forEach(cb);
        }
        else {
            cb(dom);
        }
    }
    update() {
        this.attachIdxListener();
    }
    startDrag(idxEl, ev) {
        const allChildren = Array.from(this.list.children);
        const childIndex = allChildren.indexOf(idxEl);
        if (childIndex === -1)
            return;
        const rowStart = Math.floor(childIndex / this.cols) * this.cols;
        for (let i = 0; i < this.cols; i++) {
            const el = allChildren[rowStart + i];
            if (!el)
                continue;
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
    onTouchMove(e) {
        if (!this.dragging)
            return;
        e.preventDefault();
        const t = e.touches[0];
        this.onMove({ clientX: t.clientX, clientY: t.clientY });
    }
    onTouchEnd() {
        this.onUp();
    }
    onMove(e) {
        if (!this.dragging)
            return;
        const children = Array.from(this.list.children);
        const rowCount = Math.ceil(children.length / this.cols);
        let inserted = false;
        this.list.querySelectorAll(".idx").forEach(e => {
            e.classList.remove("dragging-bottom");
            e.classList.remove("dragging-top");
        });
        for (let r = 0; r < rowCount; r++) {
            const firstIndex = r * this.cols;
            const firstChild = children[firstIndex];
            if (!firstChild)
                continue;
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
        if (!this.dragging)
            return;
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
//# sourceMappingURL=itemdragger.js.map