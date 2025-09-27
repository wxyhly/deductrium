// genOrd([1, 2, 3, 4, 3, 2, 2, 1, 2,3,4,2,3,4]);
// printOrd([1, 2, 3, 3, 2, 2, 1, 2, 3, 2, 2,3]);
// console.log(printOrd([1, 2, 3, 2, 3]));
// console.log(printOrd([1, 2, 3, 2, 2]));
// console.log(printOrd(calcMaxReachOrd([1, 2, 3, 1, 1], 2)));
// console.log(printOrd([1, 2, 3, 2, 2, 1, 2, 2]));
export function genOrd(nums) {
    const len = nums.length;
    const last = nums[len - 1];
    let max = last + 1;
    while (max > 1) {
        nums.push(max);
        let r;
        let badRoot = max;
        let checked = false;
        while (badRoot >= 1) {
            for (let x = len; x >= 0; x--) {
                if (nums[x] === badRoot) {
                    r = x; //r = bad root pos
                    break;
                }
            }
            // if (r === 0) {
            //     badRoot--; continue;// badroot2: 1,1,2 => []\[2], check badroot1 needed
            // }
            let r2 = -1;
            let foundBrach = false;
            for (let x = r - 1; x >= 0; x--) {
                if (nums[x] < badRoot) {
                    foundBrach = true;
                    break;
                }
                // if (nums[x] >= badRoot && foundBrach===-1) {
                //     foundBrach = x + 1;
                // }
                if (nums[x] === badRoot) {
                    r2 = x; //r = bad root
                    break;
                }
            }
            if (foundBrach || r2 === -1) {
                badRoot--;
                continue;
            }
            const left = nums.slice(r2, r);
            const right = nums.slice(r);
            if (cmp(left, right) >= 0) {
                badRoot--;
            }
            else {
                max--;
                break;
            }
        }
        nums.pop();
        if (badRoot <= 0 || checked)
            break;
    }
    let res = [1];
    for (let i = 2; i <= max; i++) {
        res.push(i);
    }
    return res;
}
// export function genOrd(nums: number[]) {
//     const last = nums[nums.length - 1];
//     let res = [1];
//     let max = last + 1;
//     const second = nums[nums.length - 2];
//     if (second === last) {
//         let repeatLen = 0;
//         let realSecond = 0;
//         let repeatCount = 0;
//         let foundRepeated = false;
//         // 1 2 3 4 2 2 1 3 2 2 : repeatLen 2 2 => 2, realSecond =>(3) 2 2
//         for (let i = nums.length - 3; i >= 0; i--) {
//             if (!repeatLen) {
//                 // state1: find repeat part
//                 if (nums[i] !== last) {
//                     repeatLen = nums.length - i - 1;
//                     realSecond = nums[i];
//                 }
//             } else {
//                 // state2: match another part
//                 if (nums[i] === last) {
//                     repeatCount++;
//                     if (repeatCount > repeatLen) { max = last; break; }
//                 } else {
//                     if (repeatCount === repeatLen && nums[i] === realSecond) { foundRepeated = true; max = nums[i + repeatLen + 1]; break; }
//                     repeatCount = 0;
//                 }
//             }
//         }
//         if (!foundRepeated) max = last;
//     } else {
//         for (let i = nums.length - 3; i > 0; i--) {
//             if (nums[i] === last && nums[i - 1] === second) {
//                 max = nums[i + 1]; break;
//             }
//         }
//     }
//     for (let i = 2; i <= max; i++) {
//         res.push(i);
//     }
//     return res;
// }
// from googology wiki link
function convert2Ord(a) {
    if (!a.length)
        return "0";
    let out = "";
    a = a.map(e => e - 1);
    a.unshift(-1);
    let i;
    for (i = 1; i < a.length; i++)
        if (a[i] > a[i - 1])
            out += "ω^(";
        else
            out += "0)" + ")".repeat(a[i - 1] - a[i]) + "+ω^(";
    return (out + "0)" + ")".repeat(a[i - 1])).replace(/ω\^\(0\)/g, "1").replace(/\^\(1\)/g, "");
}
export function printOrd(a) {
    let str = convert2Ord(a);
    // function printOrd(a) {
    //     let str = (a);
    let cursor = 0;
    const atom = () => {
        return str[cursor++];
    };
    const item1 = () => {
        let it;
        if (str[cursor] === "ω" || str[cursor] === "1" || str[cursor] === "0") {
            it = atom();
        }
        else if (str[cursor] === "(") {
            cursor++;
            it = item();
            cursor++; // for ")"
        }
        while (str[cursor] === "^") {
            it = [str[cursor++], it, item1()];
        }
        return it;
    };
    const item = () => {
        let count = 1;
        let it = item1();
        let arr = [it];
        while (str[cursor] === "+") {
            count++;
            cursor++;
            arr.push(item1());
        }
        if (count > 1) {
            arr.unshift("+");
            return arr;
        }
        return it;
    };
    let ast = item();
    // console.log(JSON.stringify(ast));
    const eq = (a1, a2) => {
        if (a1 === undefined || a2 === undefined)
            return false;
        if (a1 === a2)
            return true;
        if (a1.length === 3 && a2.length === 3) {
            return a1[0] === a2[0] && eq(a1[1], a2[1]) && eq(a1[2], a2[2]);
        }
        return false;
    };
    const calc = (ast) => {
        if (typeof ast === "string")
            return ast;
        if (ast[0] === "+") {
            let item = null;
            let newTerm = [];
            for (let a of ast) {
                if (a === "+")
                    continue;
                a = calc(a);
                if (item && isFinite(item)) {
                    if (isFinite(a)) {
                        item = Number(item) + Number(a);
                    }
                    else {
                        newTerm.push(item);
                        item = null;
                        continue;
                    }
                }
                if (item && a[0] === "*") {
                    // a + a*b
                    if (eq(item[1], a[1])) {
                        item[2] = Number(item[2]) + Number(a[2]);
                    }
                }
                else if (item && eq(item[1], a)) {
                    item[2]++;
                }
                else if (item && !isFinite(item)) {
                    // if cant merge, push it onto new term, and remove *1 if it have
                    newTerm.push(item[2] === 1 ? item[1] : item);
                    item = a[0] === "*" ? a : ["*", a, 1];
                }
                item ??= isFinite(a) ? a : a[0] === "*" ? a : ["*", a, 1];
            }
            if (item)
                newTerm.push(item[2] === 1 ? item[1] : item);
            if (newTerm.length === 1) {
                return newTerm[0];
            }
            else {
                newTerm.unshift("+");
                return newTerm;
            }
        }
        if (ast[0] === "^") {
            ast[1] = calc(ast[1]);
            ast[2] = calc(ast[2]);
            return ast;
        }
    };
    ast = calc(ast);
    const stringify = (ast) => {
        if (typeof ast !== "object") {
            return ast.toString();
        }
        if (ast[0] === "+") {
            return stringify(ast.slice(1).map(e => stringify(e)).join("+"));
        }
        if (ast[0] === "*") {
            return stringify(ast.slice(1).map(e => stringify(e)).join("*"));
        }
        if (ast[0] === "^") {
            const pow = stringify(ast[2]);
            return stringify(ast[1]) + "^" + (pow.length === 1 || isFinite(pow) ? pow : `(${pow})`);
        }
    };
    return stringify(ast).replaceAll(/\+1\*/g, "+").replaceAll(/^1\*/g, "");
}
const branchTables = [null, [5], [5, 4], [5, 4, 3], [5, 4, 3, 2], [5, 4, 3, 2, 1]];
export function genOrdTiles(blockMap, nameMap, p, tile, ord, depth = 5) {
    depth += ord.length;
    let step = function (t, ord) {
        const hashT = t.join(",");
        if (!blockMap.has(hashT)) {
            const tb = { type: 4, text: printOrd(ord), name: "O" + ord.join(",") };
            blockMap.set(hashT, tb);
            nameMap.set(tb.name, hashT);
            const n = isFinite(tb.text) ? Number(tb.text) : null;
            let prime = true;
            if (n > 127) {
                const max = Math.sqrt(n);
                for (let i = 2; i <= max; i++) {
                    if (n % i === 0) {
                        prime = false;
                        break;
                    }
                }
                if (prime) {
                    const nt = p.getNeighborAndDir(t, (n % 4 === 1) ? 0 : 3, true)[0];
                    blockMap.set(nt.join(","), {
                        type: 0, text: {
                            "139": "我是程序化生成的\n你玩得过我？",
                            "149": "好了，我也不怕\n跟你撕破脸",
                            "157": "走到天荒地老\n谁怕谁",
                            "163": "xxx@163.com",
                            "173": "我懒得理你了",
                            "199": "都要破两百了\n有何感想？",
                            "211": "985不是质数",
                            "223": "但233是质数",
                            "233": "唉，算了\n看你这么无聊\n解锁个类型层\n的序数给你玩玩？",
                            "251": "想得美！\n继续走吧你",
                            "277": "前进！不择手段地前进！",
                            "283": "走走走！",
                            "313": "走走走！！",
                            "347": "请前往序数ω²3+ω4+7\n解锁序数类型",
                            "349": "去那个那么小的序数\n你应该不在话下",
                            "401": "恭喜你，步数破400！",
                            "443": "过截角正五胞体，\n前进四！",
                            "577": "我一直在督促你回家",
                            "911": "空袭预警！\n空袭预警！",
                            "1009": "恭喜你，步数破千！",
                            "8191": "恭喜你，到达了\n第五个梅森素数",
                        }[n] ?? "", name: undefined
                    });
                }
            }
        }
        if (ord.length > depth)
            return;
        const branches = genOrd(ord);
        const branchTable = branchTables[branches.length];
        // const branchTable: (number | number[])[] = [null, [5], [5, 4], [5, 4, 3], [5, 4, 3, 2], [5, 4, 3, 2, 1],[5,4,3,[2,4],[2,3],1]][branches.length];
        if (!branchTable)
            return;
        for (let i of branches) {
            const dir = branchTable[i - 1];
            if (typeof dir !== "number") {
                for (let i = 0; i < dir.length - 1; i++) {
                    const tb = { type: 0, text: "", name: null };
                    t = p.getNeighborAndDir(t, dir[i], true)[0];
                    blockMap.set(t.join(","), tb);
                }
                step(p.getNeighborAndDir(t, dir[dir.length - 1], true)[0], [...ord, i]);
            }
            else {
                step(p.getNeighborAndDir(t, dir, true)[0], [...ord, i]);
            }
        }
    };
    step(tile, ord);
}
export function calcMaxReachOrd(o, base, stepInf) {
    const len = o.length;
    for (let i = 1; i < len; i++) {
        const ord2 = o.slice(0, i);
        for (const n of genOrd(ord2).reverse()) {
            if (n === 1)
                continue;
            ord2.push(n);
            if (cmp(ord2, o) > 0 && cmp(expandOrd(ord2, base), o) <= 0)
                return ord2;
            ord2.pop();
        }
    }
    let ord2 = o.slice(0);
    if (stepInf) {
        while (ord2[ord2.length - 1] === 1)
            ord2.pop();
        if (genOrd(ord2).includes(2))
            ord2.push(2);
        else {
            ord2.push(1, 2);
        }
        ;
    }
    else {
        ord2.push(1);
    }
    return ord2;
}
export function cmp(o1, o2) {
    const len = Math.max(o1.length, o2.length);
    let res = 0; //for 0 == 0
    for (let i = 0; i < len; i++) {
        res = (o1[i] ?? 0) - (o2[i] ?? 0);
        if (res !== 0)
            return res;
    }
    return res;
}
// from https://koteitan.github.io/lecture/prss.html
export function expandOrd(s, base) {
    let len = s.length;
    let c = s[len - 1];
    let e = s.slice(0, len - 1);
    if (c !== 1) {
        let r;
        for (let x = len - 2; x >= 0; x--) {
            if (s[x] < c) {
                r = x; //r = bad root
                break;
            }
        }
        //bad part r～len-1
        for (let i = 0; i < base; i++)
            for (let x = r; x < len - 1; x++) {
                e.push(s[x]);
            }
    }
    return e;
}
;
//# sourceMappingURL=ordinal.js.map