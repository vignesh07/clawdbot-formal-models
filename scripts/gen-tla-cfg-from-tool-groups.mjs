import fs from 'node:fs';
import path from 'node:path';

const src = path.resolve('generated/tool-groups.json');
const out = path.resolve('generated/tool-groups.cfg');

const data = JSON.parse(fs.readFileSync(src, 'utf8'));
const groups = data.groups || {};
const aliases = data.aliases || {};

function tlaId(s) {
  const cleaned = String(s).replace(/[^A-Za-z0-9_]/g, '_');
  return /^[0-9]/.test(cleaned) ? `k_${cleaned}` : cleaned;
}

function uniq(arr) {
  return Array.from(new Set(arr));
}

function q(s) {
  // TLA+ string literal
  return `"${String(s).replace(/\\/g, '\\\\').replace(/"/g, '\\"')}"`;
}

function setOfStrings(list) {
  const items = uniq(list.map(String)).map(q);
  return `{${items.join(', ')}}`;
}

let outText = '';
outText += '\\* Auto-generated from ../clawdbot/src/agents/tool-policy.ts via generated/tool-groups.json\n';
outText += '\\* Do not edit by hand. Regenerate with: node scripts/extract-tool-groups.mjs && node scripts/gen-tla-cfg-from-tool-groups.mjs\n\n';

// Universe of tool ids as STRINGS (exclude alias sources; include alias targets)
const toolUniverse = new Set();
for (const members of Object.values(groups)) {
  for (const m of members) toolUniverse.add(String(m));
}
for (const target of Object.values(aliases)) {
  toolUniverse.add(String(target));
}

outText += 'CONSTANTS\n';
outText += `  Tools = ${setOfStrings(Array.from(toolUniverse))}\n`;

// Emit group constants as sets of STRINGS
for (const [g, members] of Object.entries(groups)) {
  outText += `  ${tlaId(g)} = ${setOfStrings(members)}\n`;
}

// Convenience binding used by ToolGroupExpansion.tla
const gm = groups["group:memory"] || [];
outText += `  GroupMemory = ${setOfStrings(gm)}\n`;

fs.writeFileSync(out, outText);
console.log(`Wrote ${out}`);
