// import { AST } from "./astmgr.js";
// import { DeductInlineMode, DeductionStep, FormalSystem, Proposition } from "./formalsystem.js";
// export class MetaInln {
//     propscopes: [number, number][] = [];
//     formalSysmtem: FormalSystem;
//     intro(token: "v" | "c" | "e", v: AST) {
//         this.propscopes.push([this.formalSysmtem.propositions.length, NaN]);
//         const _ = { type: "replvar", name: " " };
//         const ast: AST = token === "c" ? { type: "sym", name: ">", nodes: [v, _] } :
//             token === "v" ? { type: "sym", name: "V", nodes: [v, _] } :
//                 { type: "sym", name: "E", nodes: [v, _] };
//         return {
//             value: ast, from: {
//                 deductionIdx: "[ " + token + " ]",
//                 conditionIdxs: [], replaceValues: v ? [v] : []
//             }
//         } as Proposition;
//     }
//     outro(token: "v" | "c" | "e", v: AST) {
//         // todo
//     }
//     getEnv(pid: number = this.formalSysmtem.propositions.length) {
//     }
//     deduct(step: DeductionStep, inlineMode?: DeductInlineMode | ((step: DeductionStep, conclusion: AST) => DeductInlineMode), partialTest?: boolean) {
//         const { conditionIdxs, deductionIdx, replaceValues } = step;
//         if (deductionIdx === "[ v ]") {
//             return this.formalSysmtem.propositions.push(this.intro("v", replaceValues[0]));
//         }
//         if (deductionIdx === "[ c ]") {
//             return this.formalSysmtem.propositions.push(this.intro("c", replaceValues[0]));
//         }
//     }
// }
//# sourceMappingURL=metainln.js.map