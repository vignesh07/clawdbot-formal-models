import fs from 'node:fs';

const p = new URL('../generated/tool-groups.json', import.meta.url);
const json = JSON.parse(fs.readFileSync(p, 'utf8'));

const g = json.groups || {};
const a = g['group:clawdbot'];
const b = g['group:openclaw'];

if (!a || !b) {
  console.error('Expected both group:clawdbot and group:openclaw to exist in generated/tool-groups.json');
  console.error('Present keys:', Object.keys(g).sort().join(', '));
  process.exit(2);
}

const as = JSON.stringify(a);
const bs = JSON.stringify(b);

if (as !== bs) {
  console.error('Tool group alias mismatch: group:clawdbot != group:openclaw');
  console.error('group:clawdbot:', a);
  console.error('group:openclaw:', b);
  process.exit(1);
}

console.log('OK: group:clawdbot and group:openclaw are identical.');
