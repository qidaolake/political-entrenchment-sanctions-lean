// scripts/audit-affine-surface.mjs
//
// Rule 22 standing audit: which declarations outside `Examples/` read `p.δ`?
//
// `δ` is a `Params` field, but nothing in `Params` connects it to `F`. It is
// the rate at which a sanction moves the political state *only* when
// `F = affineF δ`; under a general transition it is inert. So a declaration in
// `Theory/`, `Foundations/` or `Postulates/` that reads `p.δ` is one of:
//
//   (a) affine-restricted, and should say so in its own docstring (Rule 22);
//   (b) general, but reusing `δ` as the name of a chord rate -- legitimate but
//       confusing, and Rule 3 asks such a route to name its own rate; or
//   (c) accidentally affine: a general-looking result that quietly depends on a
//       functional form it never assumed.
//
// (c) is the failure this exists to prevent, and it is invisible to the type
// checker -- such a theorem compiles, is true, and means less than it looks
// like it means.
//
// WHY A BASELINE AND NOT A KEYWORD TEST. The first version failed anything
// whose docstring did not contain "affine". That was wrong in both directions:
// it cleared declarations that merely mention the word, and it flagged
// `movAvgShockedParams_..._of_strong_rally_generalF`, which is genuinely
// general -- it leaves `q.F` unconstrained and *assumes an upper chord at rate
// `q.δ`*, using the field as a rate name rather than as evidence of affineness.
// That case is the sharper form of the problem: one symbol means "nothing at
// all" in one theorem and "the rate a sanction moves the state" in another.
//
// Classifying every current reader is a round of work in itself. This audit
// holds the line instead: the present readers are recorded in
// `scripts/affine-surface-baseline.json`, and the script fails on any reader
// not in that list. The surface cannot grow silently; shrinking it is tracked
// separately, and the script reports when a baseline entry is no longer needed.
//
// Usage:
//   node scripts/audit-affine-surface.mjs                  audit (CI mode)
//   node scripts/audit-affine-surface.mjs --list           also list readers
//   node scripts/audit-affine-surface.mjs --write-baseline re-record baseline
//
// Exit: 0 clean, 1 a new reader appeared, 2 internal error.

import { readFileSync, writeFileSync, readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';

const BS = String.fromCharCode(92);
const NL = String.fromCharCode(10);
const norm = (s) => s.split(BS).join('/');
const LIST = process.argv.includes('--list');
const WRITE = process.argv.includes('--write-baseline');
const BASELINE = 'scripts/affine-surface-baseline.json';

// Blank out comments while preserving line numbers, so docstring prose that
// discusses `p.δ` is never counted as a use of it.
function stripKeepLines(src) {
  const a = src.split('');
  let i = 0, d = 0;
  const n = src.length;
  const blank = (from, to) => {
    for (let k = from; k < to && k < n; k++) if (a[k] !== NL) a[k] = ' ';
  };
  while (i < n) {
    if (src.startsWith('/-', i)) {
      const s = i; d = 1; i += 2;
      while (i < n && d > 0) {
        if (src.startsWith('/-', i)) { d++; i += 2; }
        else if (src.startsWith('-/', i)) { d--; i += 2; }
        else i++;
      }
      blank(s, i); continue;
    }
    if (src.startsWith('--', i)) {
      const s = i; const j = src.indexOf(NL, i); i = j < 0 ? n : j; blank(s, i); continue;
    }
    i++;
  }
  return a.join('');
}

const files = [];
(function walk(p) {
  for (const e of readdirSync(p)) {
    const f = norm(join(p, e));
    if (statSync(f).isDirectory()) walk(f);
    else if (f.endsWith('.lean')) files.push(f);
  }
})('Sanctions');

// A declaration may open with attributes on the same line (`@[simp] theorem ...`). Until
// 2026-10-06 (renovation round BG-0) such a declaration was not recognised, so its text was
// credited to the span of the declaration before it, which is failure mode (c) in reverse:
// `withProfile` was flagged only because the `p.δ` of the `@[simp]` lemma after it fell inside
// its span.
const DECL = /^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+)*(?:theorem|lemma|def|abbrev|instance|structure)\s+([^\s:({[]+)/;
// A receiver-dot projection of the field: `p.δ`, `sp.δ`, `C.δ`. The dot is
// escaped explicitly -- an unescaped `.` here matches any character, which on
// an earlier run counted a local binder `δ` as a field read and inflated the
// count from 21 to 53.
// Receivers are Lean identifiers, so Unicode letters, subscripts and primes
// count (`p₁.δ`, `sp'.δ`); the ASCII-only class missed `p₁.δ` until round BB
// (2026-09-28), hiding two readers in `LockInComparativeStatics.lean`.
const DELTA = new RegExp(
  '(?<![' + BS + 'p{L}' + BS + 'p{N}_' + "'" + '])[' + BS + 'p{L}_][' + BS + 'p{L}' + BS + 'p{N}_' + "'" + ']*' +
  BS + '.δ(?![' + BS + 'p{L}' + BS + 'p{N}_' + "'" + '])', 'u');

const inScope = (f) =>
  f.startsWith('Sanctions/Theory/') ||
  f.startsWith('Sanctions/Foundations/') ||
  f.startsWith('Sanctions/Postulates/');

const readers = [];
for (const f of files) {
  if (!inScope(f)) continue;
  const raw = readFileSync(f, 'utf8');
  const C = stripKeepLines(raw).split(/\r?\n/);
  const decls = [];
  for (let i = 0; i < C.length; i++) {
    const m = C[i].match(DECL);
    if (m) decls.push({ name: m[1], line: i });
  }
  for (let k = 0; k < decls.length; k++) {
    const from = decls[k].line;
    const to = decls[k + 1] ? decls[k + 1].line : C.length;
    if (DELTA.test(C.slice(from, to).join(NL))) {
      readers.push(f.replace('Sanctions/', '') + '  ' + decls[k].name);
    }
  }
}

const found = readers.sort();

if (WRITE) {
  writeFileSync(BASELINE, JSON.stringify(found, null, 2) + NL);
  console.log('baseline written: ' + found.length + ' readers');
  process.exit(0);
}

let baseline;
try {
  baseline = JSON.parse(readFileSync(BASELINE, 'utf8'));
} catch {
  console.error('!! ' + BASELINE + ' missing; regenerate with --write-baseline');
  process.exit(2);
}
const known = new Set(baseline);
const added = found.filter((k) => !known.has(k));
const gone = baseline.filter((k) => !found.includes(k));

console.log('Rule 22 affine-surface audit: readers of the inert `p.δ` outside Examples/');
console.log('  readers found  : ' + found.length);
console.log('  baseline       : ' + known.size);
console.log('  newly added    : ' + added.length);
console.log('  no longer read : ' + gone.length);

if (LIST) {
  console.log('');
  console.log('--- current readers ---');
  for (const k of found) console.log('  ' + k);
}

if (gone.length) {
  console.log('');
  console.log('--- these no longer read `p.δ`; shrink the baseline ---');
  for (const k of gone) console.log('  ' + k);
}

if (added.length) {
  console.log('');
  console.log('--- NEW readers of the inert `δ` ---');
  for (const k of added) console.log('  ' + k);
  console.log('');
  console.log('A declaration outside `Examples/` that reads `p.δ` is either');
  console.log('  * affine-restricted, and must say so in its docstring (Rule 22); or');
  console.log('  * general, and should name its own chord rate rather than reuse `δ`');
  console.log('    (Rule 3, transition-class scope of the economy test).');
  console.log('');
  console.log('If the addition is intended and reviewed, re-run --write-baseline.');
  process.exit(1);
}

console.log('');
console.log('clean: no new reader of the inert `δ` outside Examples/.');
