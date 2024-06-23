export class HoTT {
    getFreeVars(ast, res = new Set, scope = []) {
        if (ast.type === "var" && !scope.includes(ast.name)) {
            res.add(ast.name);
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            this.getFreeVars(ast.nodes[0], res, scope);
            this.getFreeVars(ast.nodes[1], res, [ast.name, ...scope]);
        }
        else if (ast.type === "apply") {
            this.getFreeVars(ast.nodes[0], res, scope);
            this.getFreeVars(ast.nodes[1], res, scope);
        }
        return res;
    }
    getNewName() {
    }
    replace(ast, name, dst, fvDst = this.getFreeVars(dst)) {
        if (ast.type === "var") {
            if (ast.name !== name)
                return;
            this.assign(ast, dst);
        }
        else if (ast.type === "apply") {
            this.replace(ast.nodes[0], name, dst, fvDst);
            this.replace(ast.nodes[1], name, dst, fvDst);
        }
        if (ast.type === "L" || ast.type === "P" || ast.type === "S") {
            this.replace(ast.nodes[0], name, dst);
            if (ast.name === name)
                return; // bounded
            const fvSrcBody = this.getFreeVars(ast.nodes[1]);
            if (!fvSrcBody.has(name))
                return; //not bounded, but not found
            if (!fvDst.has(ast.name))
                this.replace(ast.nodes[1], name, dst, fvDst);
            else {
                const newName = getNewName(new Set([...fvSrcBody, ...fvDst]));
                this.replace(ast.nodes[1], name, dst, fvDst);
            }
            return;
        }
        return ast; //todo
    }
    clone(ast) {
        const newast = {
            type: ast.type, name: ast.name
        };
        if (ast.nodes) {
            newast.nodes = ast.nodes.map(p => this.clone(p));
        }
        return newast;
    }
    assign(ast, value) {
        const v = this.clone(value);
        ast.type = v.type;
        ast.name = v.name;
        ast.nodes = v.nodes;
    }
    equal(ast1, ast2) {
        if (ast1 === ast2)
            return true;
        if (ast1.name !== ast2.name)
            return false;
        if (ast1.type !== ast2.type)
            return false;
        if (ast1.nodes?.length !== ast2.nodes?.length)
            return false;
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.equal(ast1.nodes[i], ast2.nodes[i]))
                    return false;
            }
        }
        return true;
    }
    check(ast, context = []) {
        if (ast.type === "var") {
            const jeg = ast.name.match(/^U('*)$/);
            if (jeg) {
                return { type: "var", name: jeg[1] + "'" };
            }
            const varType = context.find(v => v[0] === ast.name);
            if (varType)
                return varType[1];
            throw "未知的变量：" + ast.name;
        }
        if (ast.type === "L") {
            return { type: "P", name: ast.name, nodes: [ast.nodes[0], this.check(ast.nodes[1], [[ast.name, ast.nodes[0]], ...context])] };
        }
        if (ast.type === "P" || ast.type === "S") {
            return { type: "var", name: "U" };
        }
        if (ast.type === "apply") {
            const t1 = this.check(ast.nodes[0], context);
            if (t1.type !== "P")
                throw "非函数尝试作用";
            const t2 = this.check(ast.nodes[1], context);
            if (!this.equal(t2, t1.nodes[0]))
                throw "函数与作用目标类型不匹配";
            return this.replace(t1.nodes[1], ast.name, ast.nodes[1]);
        }
        throw "未知的语法树";
    }
}
//# sourceMappingURL=HoTT.js.map