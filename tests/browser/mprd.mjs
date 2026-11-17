import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { resolve, extname, sep, isAbsolute } from 'node:path';

const root = resolve(fileURLToPath(new URL('../..', import.meta.url)));
const playwright = process.env.PLAYWRIGHT_MODULE || 'playwright';
const { chromium } = await import(isAbsolute(playwright) ? pathToFileURL(playwright).href : playwright);
const mime = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css' };
const server = createServer(async (req, res) => {
    try {
        const pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
        const path = resolve(root, '.' + (pathname === '/' ? '/index.html' : pathname));
        if (!path.startsWith(root + sep)) throw new Error('Outside test root');
        res.setHeader('Content-Type', mime[extname(path)] || 'application/octet-stream');
        res.end(await readFile(path));
    } catch { res.statusCode = 404; res.end(); }
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const browser = await chromium.launch({ headless: true, channel: 'chrome' });
try {
    for (const viewport of [{ width: 1440, height: 1000 }, { width: 390, height: 844 }]) {
        const context = await browser.newContext({ viewport });
        const page = await context.newPage();
        const errors = [];
        page.on('pageerror', error => errors.push(error.message));
        await page.goto(`http://127.0.0.1:${server.address().port}/?creative`);
        await page.locator('#deduct-btn').click();
        const input = page.locator('#action-input');
        const command = async text => { await input.fill(text); await input.press('Enter'); };
        await command('d a7 0');
        const before = await page.locator('#prop-list').innerText();
        // The real interactive mprd workflow: command, name, parameters, body.
        for (const text of ['mprd', 'checkbug', 'x', 'x=y']) await command(text);
        assert.match(await page.locator('#hint').innerText(), /自由变量|[Ff]ree variable/);
        assert.equal(await page.locator('#prop-list').innerText(), before);
        assert.equal((await page.locator('#deduct-list').innerText()).includes('dvcheckbug'), false);
        // A rejected name remains available for a valid definition.
        for (const text of ['mprd', 'checkbug', 'x,y', 'x=y']) await command(text);
        assert.ok((await page.locator('#deduct-list').innerText()).includes('dvcheckbug'));
        await command('d dvcheckbug');
        assert.ok((await page.locator('#prop-list').innerText()).includes('checkbug'));
        // Expanded substitutions remain usable from the same UI.
        for (const text of ['mprd', 'replacecheck', 'x', '#rp(y=0,y,x)']) await command(text);
        assert.ok((await page.locator('#deduct-list').innerText()).includes('dvreplacecheck'));
        assert.deepEqual(errors, []);
        console.log(JSON.stringify({ viewport, passed: true, errors }));
        await context.close();
    }
} finally {
    await browser.close();
    await new Promise(resolve => server.close(resolve));
}
