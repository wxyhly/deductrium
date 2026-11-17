import assert from 'node:assert/strict';
import test from 'node:test';
import { initFormalSystem } from '../js/fs/initial.js';
import { ASTParser } from '../js/fs/astparser.js';

const parser = new ASTParser();
const parse = text => parser.parse(text);
const create = () => {
    const { fs } = initFormalSystem(true);
    fs.fastmetarules = 'cvuqe><:#zZQR';
    return fs;
};
const define = (fs, name, expression, params = ['x']) =>
    fs.metaNewVerb([parse(name), parse(expression), params.map(parse)], 'test');
const snapshot = fs => JSON.stringify({
    deductions: fs.deductions,
    verbs: [...fs.verbs], fns: [...fs.fns], consts: [...fs.consts],
    propositions: fs.propositions
});
const freeVariableError = error => /自由变量|[Ff]ree variable/.test(String(error));

test('mprd rejects the checkbug(x) <-> x=y exploit without changing state', () => {
    const fs = create();
    fs.deduct({ deductionIdx: 'a7', conditionIdxs: [], replaceValues: [parse('0')] });
    const before = snapshot(fs);
    assert.throws(() => define(fs, 'checkbug', 'x=y'), freeVariableError);
    assert.equal(snapshot(fs), before);
    assert.equal(fs.verbs.has('checkbug'), false);
    assert.equal(fs.generateDeduction('dvcheckbug'), null);
});

test('every free variable must be declared, including one inside another quantifier', () => {
    const fs = create();
    for (const expression of ['y=x', '(x=y)&(x=x)', 'Vz:(z=y)', '(Vy:y=y)&(x=y)']) {
        const before = snapshot(fs);
        assert.throws(() => define(fs, 'checkbug', expression), freeVariableError);
        assert.equal(snapshot(fs), before);
    }
});

test('declaring both parameters keeps equality usable with different arguments', () => {
    const fs = create();
    const name = define(fs, 'eqcheck', 'x=y', ['x', 'y']);
    fs.deduct({ deductionIdx: name, conditionIdxs: [], replaceValues: [] });
    fs.deduct({ deductionIdx: '<a4', conditionIdxs: [0], replaceValues: [parse('1')] });
    fs.deduct({ deductionIdx: '<a4', conditionIdxs: [1], replaceValues: [parse('0')] });
    assert.equal(parser.stringifyTight(fs.propositions[2].value), 'eqcheck(0,1)<>(0=1)');
});

test('bound variables are allowed for universal, existential and unique-existential quantifiers', () => {
    const fs = create();
    for (const [name, expression] of [
        ['allcheck', 'Vy:(x=y)'], ['somecheck', 'Ey:(x=y)'],
        ['uniquecheck', 'E!y:(x=y)'], ['shadowcheck', 'Vy:(Vy:(y=y))'],
        ['unusedcheck', 'Vy:(y=y)']
    ]) assert.equal(define(fs, name, expression), `dv${name}`);
});

test('registered constants and numeral constants need no predicate parameter', () => {
    const fs = create();
    fs.consts.add('fixed');
    for (const [name, expression] of [
        ['zerocheck', 'x=0'], ['onecheck', 'x=1'],
        ['constcheck', 'x=fixed'], ['setcheck', 'x={}']
    ]) assert.equal(define(fs, name, expression), `dv${name}`);
});

test('set builders bind their variable in the body, but not in the domain', () => {
    const fs = create();
    assert.equal(define(fs, 'sepcheck', 'x={y@x|y=y}'), 'dvsepcheck');
    assert.equal(define(fs, 'imagecheck', 'x={y|y@x}'), 'dvimagecheck');
    for (const expression of ['x={y@y|y=y}', 'x={y@x|y=z}', 'x={z|y@x}']) {
        const before = snapshot(fs);
        assert.throws(() => define(fs, 'badset', expression), freeVariableError);
        assert.equal(snapshot(fs), before);
    }
});

test('a failed definition does not reserve its name, and quantified closed definitions stay consistent', () => {
    const fs = create();
    assert.throws(() => define(fs, 'checkbug', 'x=y'), freeVariableError);
    const name = define(fs, 'checkbug', 'Vy:(x=y)');
    fs.deduct({ deductionIdx: `v${name}`, conditionIdxs: [], replaceValues: [parse('z')] });
    assert.equal(parser.stringifyTight(fs.propositions[0].value), '(Vz:(Vx:(checkbug(x)<>(Vy:(x=y)))))');
});

test('substitutions are checked after expansion, without mutating the supplied body', () => {
    const fs = create();
    for (const [name, expression, expanded] of [
        ['replacecheck', '#rp(y=0,y,x)', 'x=0'],
        ['absentcheck', '#rp(x=0,z,y)', 'x=0'],
        ['sidecheck', '#nf(x=x,y)', 'x=x'],
        ['canreplacecheck', '#crp(x=x,y,z)', 'x=x']
    ]) {
        const body = parse(expression);
        const before = JSON.stringify(body);
        const nameOfRule = fs.metaNewVerb([parse(name), body, [parse('x')]], 'test');
        assert.equal(JSON.stringify(body), before);
        assert.equal(parser.stringifyTight(fs.deductions[nameOfRule].conclusion),
            parser.stringifyTight(parse(`Vx:(${name}(x)<>(${expanded}))`)));
    }
    for (const expression of ['#rp(x=0,x,y)', '#nf(x=y,y)', '#vnf(x=y,y,y)']) {
        const before = snapshot(fs);
        assert.throws(() => define(fs, 'badreplace', expression));
        assert.equal(snapshot(fs), before);
    }
});
