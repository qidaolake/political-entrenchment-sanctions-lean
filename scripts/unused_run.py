"""Run the unused-binder probe (doc 78 K12; protocol v2, doc 80 M4) over root
lists and write the report.

Usage:
    python scripts/unused_run.py <report.md> <roots-file> [<roots-file> ...]

Each roots file holds one declaration name per line (comments with `#`),
resolved under the probe template's `open` line; duplicates across files are
merged. The probe is written under `tmp/` (git-ignored) with a fresh run
nonce, elaborated with `lake env lean` against the built library — run it
after the round's build, never before — the raw compiler output is saved
beside the report as `<report>.raw.txt`, and, only if every validation
passes, the report is written in Markdown: a provenance header (commit,
dirty-tree flag, toolchain, mathlib revision, the hashes of the template, the
runner and the root lists, the nonce), the candidate rows (explicit binders
that occur neither in the proof body, nor in another binder's type, nor in the
conclusion), the body-only rows, a per-root summary, the skipped roots, and
the instrument's limits.

Fails closed, strictly (the reader's round-K validation package, document 04
§2–3): a nonzero Lean exit; output that does not decode as UTF-8; a missing or
mismatched run nonce; a BEGIN without its kind and telescope length; a
duplicate BEGIN; a BINDER row with too few fields, an out-of-sequence index,
an unknown kind, a non-boolean flag, an empty name or type; an END naming the
wrong root; a record whose BINDER count differs from its telescope length; a
record begun but not ended; a requested root that resolves to no record or to
several; a record count that differs from the number of distinct requested
declarations; a completion marker that is absent, repeated, or does not equal
the number of requested roots. On failure the raw file is kept, a failure
receipt is written as `<report>.FAILED.txt`, the report is not written, and
the exit status is 1. Roots without a value (axioms, opaques) are recorded as
skipped, never as inspected.
"""
import os, sys, subprocess, uuid, pathlib, datetime, hashlib, json, re

KINDS_BINDER = {'explicit', 'implicit', 'instImplicit', 'strictImplicit'}
KINDS_CONST = {'theorem', 'def', 'inductive', 'ctor', 'axiom', 'opaque', 'rec', 'quot'}
TAGS = ('UNUSED-RUN ', 'UNUSED-BEGIN ', 'UNUSED-END ', 'UNUSED-DONE ', 'BINDER ', 'NOVALUE')
# `logInfo` output arrives as bare lines from `lake env lean`; an optional
# `path:line:col: info: ` prefix is tolerated. A tag counts only at the start
# of the (prefix-stripped) line: a tag inside another message is not an event.
INFO = re.compile(r'^(?:(.*?):(\d+):(\d+): info: )?(.*)$')


def protocol_payload(line):
    """The protocol payload of a compiler line, or None if the line is not one."""
    s = line.strip()
    m = INFO.match(s)
    payload = m.group(4).strip() if m else s
    return payload if any(payload.startswith(t) for t in TAGS) else None


def parse_probe_output(out, names, nonce):
    """Strict parse of the probe's compiler output.

    Returns (fails, records, resolved): `fails` is the list of validation
    failures (empty iff the run is acceptable); `records` maps each printed
    root name to {kind, n, binders, novalue, closed}; `resolved` maps each
    requested name to its record's printed name.
    """
    fails = []
    records = {}
    cur = None      # the open record's printed name
    rec = None      # the dict being filled (the record itself, or an alias shadow)
    shadow = False  # True while filling a second record for an already-seen name
    aliases = 0
    run_seen = 0
    done_vals = []
    for raw in out.splitlines():
        payload = protocol_payload(raw)
        if payload is None:
            continue  # another compiler message, not ours
        if payload.startswith('UNUSED-RUN '):
            run_seen += 1
            if payload[len('UNUSED-RUN '):].strip() != nonce:
                fails.append('run nonce mismatch')
            continue
        if payload.startswith('UNUSED-BEGIN '):
            parts = payload[len('UNUSED-BEGIN '):].split()
            if cur is not None:
                fails.append(f'record {cur} began without ending')
                cur = None; rec = None; shadow = False
            if len(parts) != 3 or parts[1] not in KINDS_CONST or not parts[2].isdigit():
                fails.append(f'malformed BEGIN: {payload[:100]}')
                continue
            name, kind, n = parts[0], parts[1], int(parts[2])
            new = {'kind': kind, 'n': n, 'binders': [], 'novalue': False, 'closed': False}
            if name in records:
                # Alias policy: one declaration requested under two qualifications
                # is probed twice; the second record must be identical to the first
                # (checked at its END), never silently overwrite it.
                shadow = True
            else:
                records[name] = new
                shadow = False
            cur = name; rec = new
            continue
        if payload.startswith('UNUSED-DONE '):
            done_vals.append(payload[len('UNUSED-DONE '):].strip())
            if cur is not None:
                fails.append('completion marker inside an open record')
            continue
        if cur is None:
            fails.append(f'record line outside a record: {payload[:80]}')
            continue
        if payload == 'NOVALUE':
            if rec['novalue'] or rec['binders']:
                fails.append(f'{cur}: NOVALUE repeated or after binder rows')
            rec['novalue'] = True
            continue
        if payload.startswith('BINDER '):
            parts = [p.strip() for p in payload[len('BINDER '):].split('|', 7)]
            if len(parts) < 8:
                fails.append(f'{cur}: malformed BINDER row: {payload[:100]}')
                continue
            k, bname, bkind, isP, inBody, inLater, inConcl = parts[:7]
            ty = parts[7]  # the pretty-printed type, verbatim (it may contain `|`)
            if not k.isdigit() or int(k) != len(rec['binders']) + 1:
                fails.append(f'{cur}: binder index {k!r} out of sequence')
            if bkind not in KINDS_BINDER:
                fails.append(f'{cur}: unknown binder kind {bkind!r}')
            flags = {}
            for fname, fval in (('isProp', isP), ('inBody', inBody), ('inLater', inLater),
                                ('inConcl', inConcl)):
                if fval not in ('true', 'false'):
                    fails.append(f'{cur}: binder {k} flag {fname} = {fval!r} is not a boolean')
                flags[fname] = (fval == 'true')
            if not bname:
                fails.append(f'{cur}: binder {k} has no name')
            if not ty:
                fails.append(f'{cur}: binder {k} has no type')
            rec['binders'].append(dict(k=int(k) if k.isdigit() else -1, name=bname, kind=bkind,
                                       type=ty, **flags))
            continue
        if payload.startswith('UNUSED-END '):
            ename = payload[len('UNUSED-END '):].strip()
            if ename != cur:
                fails.append(f'END names {ename!r}, the open record is {cur!r}')
            if rec['novalue']:
                if rec['binders']:
                    fails.append(f'{cur}: NOVALUE record carries binder rows')
            elif len(rec['binders']) != rec['n']:
                fails.append(f'{cur}: {len(rec["binders"])} binder rows for a telescope of {rec["n"]}')
            rec['closed'] = True
            if shadow:
                first = records[cur]
                same = all(first[k] == rec[k] for k in ('kind', 'n', 'novalue', 'binders'))
                if same:
                    aliases += 1
                else:
                    fails.append(f'duplicate record for {cur} differs from the first')
            cur = None; rec = None; shadow = False
            continue
        fails.append(f'unrecognised protocol line: {payload[:80]}')
    if cur is not None:
        fails.append(f'record {cur} truncated at end of output')
    if run_seen != 1:
        fails.append(f'run marker seen {run_seen} times (expected once)')
    resolved = {}
    for nm in names:
        hits = [b for b in records if b == nm or b.endswith('.' + nm)]
        if len(hits) != 1:
            fails.append(f'root {nm!r} resolved to {len(hits)} records')
        else:
            resolved[nm] = hits[0]
    # two root lists may name one declaration under different qualifications;
    # count declarations, not names
    if len(set(resolved.values())) != len(records):
        fails.append(f'{len(records)} records for {len(set(resolved.values()))} distinct declarations')
    if len(records) + aliases != len(names):
        fails.append(f'{len(records)} records plus {aliases} identical aliases for {len(names)} requested names')
    if done_vals != [str(len(names))]:
        fails.append(f'completion marker: expected exactly one UNUSED-DONE {len(names)}, saw {done_vals}')
    return fails, records, resolved


def sha16(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()[:16]


def main(argv):
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    root = pathlib.Path(__file__).resolve().parents[1]
    os.chdir(root)
    if len(argv) < 3:
        print(__doc__); return 1
    report = pathlib.Path(argv[1])
    names = []
    for f in argv[2:]:
        for l in open(f, encoding='utf-8'):
            n = l.split('#')[0].strip()
            if n and n not in names:
                names.append(n)
    if not names:
        print('FAIL: empty root list'); return 1

    def git(*a):
        return subprocess.run(['git', *a], capture_output=True, text=True).stdout.strip()
    head = git('rev-parse', 'HEAD')
    dirty = git('status', '--porcelain') != ''
    toolchain = (root / 'lean-toolchain').read_text(encoding='utf-8').strip()
    manifest = json.loads((root / 'lake-manifest.json').read_text(encoding='utf-8'))
    mathlib = next((p.get('rev', '?') for p in manifest.get('packages', []) if p.get('name') == 'mathlib'), '?')
    template_path = root / 'scripts' / 'unused_probe.lean.template'
    template = template_path.read_text(encoding='utf-8')
    nonce = uuid.uuid4().hex
    probe = (template + '\n' + f'#unusedRun "{nonce}"\n' + '\n'.join(f'#unused {n}' for n in names)
             + f'\n#unusedDone {len(names)}\n')
    tmpdir = root / 'tmp'; tmpdir.mkdir(exist_ok=True)
    tmp = tmpdir / f'_unused_probe_{nonce}.lean'
    tmp.write_text(probe, encoding='utf-8')
    env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get('LEAN_NUM_THREADS', '15'))
    try:
        res = subprocess.run(['lake', 'env', 'lean', str(tmp)], capture_output=True, env=env)
    finally:
        tmp.unlink(missing_ok=True)
    raw_bytes = res.stdout + res.stderr
    out_lossy = raw_bytes.decode('utf-8', errors='replace')
    raw_path = report.with_suffix(report.suffix + '.raw.txt')
    raw_path.write_text(f'UNUSED-HEAD {head}\nUNUSED-DIRTY {int(dirty)}\nUNUSED-TOOLCHAIN {toolchain}\n'
                        f'UNUSED-MATHLIB {mathlib}\nUNUSED-NONCE {nonce}\nUNUSED-REQUESTED {len(names)}\n'
                        + out_lossy, encoding='utf-8')

    fails = []
    if res.returncode != 0:
        fails.append(f'lean exit {res.returncode}')
        fails += [l for l in out_lossy.splitlines() if 'error' in l.lower()][:20]
    try:
        out = raw_bytes.decode('utf-8', errors='strict')
    except UnicodeDecodeError as e:
        fails.append(f'compiler output is not UTF-8: {e}')
        out = out_lossy
    pf, records, resolved = parse_probe_output(out, names, nonce)
    fails += pf

    n_expl = sum(1 for r in records.values() for b in r['binders'] if b['kind'] == 'explicit')
    n_all = sum(len(r['binders']) for r in records.values())
    cands = [(rn, b) for rn, r in records.items() for b in r['binders']
             if b['kind'] == 'explicit' and not (b['inBody'] or b['inLater'] or b['inConcl'])]
    body_only = [(rn, b) for rn, r in records.items() for b in r['binders']
                 if b['kind'] == 'explicit' and b['inBody'] and not (b['inLater'] or b['inConcl'])]
    novalue = [rn for rn, r in records.items() if r['novalue']]
    distinct = len(set(resolved.values()))
    summary = (f'lean exit {res.returncode}; {len(names)} roots requested ({distinct} distinct declarations); '
               f'{len(records)} records; {n_expl} explicit binders; {len(cands)} candidates; '
               f'{len(body_only)} body-only; {len(novalue)} skipped (no value); head {head[:9]}'
               f'{" (dirty tree)" if dirty else ""}')
    print(summary)
    if fails:
        failed = report.with_suffix(report.suffix + '.FAILED.txt')
        failed.write_text(f'{datetime.date.today().isoformat()} {summary}\n' + '\n'.join(fails) + '\n',
                          encoding='utf-8')
        print('FAIL:'); print('\n'.join('  ' + f for f in fails))
        print(f'no report written; receipt at {failed}; raw output at {raw_path}')
        return 1

    today = datetime.date.today().isoformat()
    roots_desc = ', '.join(f'`{pathlib.Path(f).name}` (sha `{sha16(f)}`)' for f in argv[2:])
    L = []
    A = L.append
    A('# Unused-binder audit (Rule 13, doc 78 K12; protocol v2, doc 80 M4)')
    A('')
    A(f'Generated {today} by `scripts/unused_run.py` (sha `{sha16(__file__)}`) from '
      f'`scripts/unused_probe.lean.template` (sha `{sha16(template_path)}`) at commit `{head[:9]}`'
      f'{" (dirty tree)" if dirty else ""} under `{toolchain}`, mathlib `{mathlib[:9]}`; run nonce '
      f'`{nonce}`. Roots: {len(names)} in {roots_desc}; {distinct} distinct declarations; {len(records)} '
      f'records, of which {len(novalue)} skipped (no value). Binders inspected: {n_all}, of which '
      f'{n_expl} explicit. Raw compiler output: `{raw_path.name}`. The probe reads the built library: '
      'this report is evidence about the tree only if the build that produced the `.olean` files is '
      'the one at the commit named here.')
    A('')
    A('**What a row means.** For each explicit binder of a root, the probe applies the compiled proof '
      'term to the binders of the root\'s own type, inlines the auxiliary lemmas the compiler split off '
      'under the root\'s name, and records whether the binder occurs in the proof body, in the type of '
      'another binder, or in the conclusion. A binder with all three flags false is logically removable '
      'from the statement and is listed as a **candidate**; removing one from a headline changes its '
      'elaborated type and is a Rule 3/18 decision, never an automatic edit — the decisive check is a '
      'sibling declaration without the binder that elaborates. A binder that occurs only in '
      'the proof body is used by this proof; whether another proof could avoid it is not measured, and '
      'neither is "implied by another hypothesis of the same theorem".')
    A('')
    A(f'## Candidates: {len(cands)}')
    A('')
    if cands:
        A('| root | k | binder | type |'); A('|---|---|---|---|')
        for rn, b in cands:
            A(f'| `{rn}` | {b["k"]} | `{b["name"]}` | `{b["type"]}` |')
    else:
        A('None: every explicit binder of every probed root occurs in the proof body, in another '
          'binder\'s type, or in the conclusion.')
    A('')
    A(f'## Explicit binders used only in the proof body: {len(body_only)}')
    A('')
    A('These are consumed by the proof and appear neither in another binder\'s type nor in the '
      'conclusion. They are not candidates; they are the hypotheses whose necessity is a mathematical '
      'question, listed so a reader can pick a target for a Rule-11 refutation attempt.')
    A('')
    if body_only:
        A('| root | k | binder | type |'); A('|---|---|---|---|')
        for rn, b in body_only:
            A(f'| `{rn}` | {b["k"]} | `{b["name"]}` | `{b["type"]}` |')
    A('')
    A('## Per-root summary')
    A('')
    A('| root | kind | telescope | binders | explicit | candidates |'); A('|---|---|---|---|---|---|')
    for rn, r in records.items():
        ne = sum(1 for b in r['binders'] if b['kind'] == 'explicit')
        nc = sum(1 for _rn, b in cands if _rn == rn)
        A(f'| `{rn}` | {r["kind"]}{" (skipped: no value)" if r["novalue"] else ""} | {r["n"]} | '
          f'{len(r["binders"])} | {ne} | {nc} |')
    A('')
    A('## Limits')
    A('')
    A('- A value eta-reduced below its type\'s binder count leaves the remaining binders as arguments of '
      'a constant; the probe then counts them as used (conservative).')
    A('- Auxiliary lemmas are inlined four levels deep; a binder that disappears only deeper would be '
      'reported as used (conservative).')
    A('- Structure fields consumed through a structure-typed binder are not itemised here; the field-level '
      'audit is the census (`docs/HYPOTHESIS-CENSUS.md`) and the graph (`docs/CODEGRAPH-EVALUATION-2026-08-20.md`).')
    A('- Roots without a value are skipped, not inspected; they are listed in the per-root summary'
      + (f': {", ".join("`" + n + "`" for n in novalue)}.' if novalue else ' (none in this run).'))
    report.write_text('\n'.join(L) + '\n', encoding='utf-8')
    failed = report.with_suffix(report.suffix + '.FAILED.txt')
    if failed.exists():
        failed.unlink()
    print(f'OK: report written to {report}')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
