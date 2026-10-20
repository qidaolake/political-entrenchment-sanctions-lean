"""Self-test of the unused-binder instrument (doc 80 M4; protocol v2).

Usage:
    python scripts/unused_run_selftest.py

Two parts. (1) The strict parser of scripts/unused_run.py must accept the
valid fixture record and the deliberate NOVALUE skip, and must reject every
malformed shape the reader's round-K validation package (document 04 §2)
showed the round-K runner accepting: no BINDER rows for a nonzero telescope, a
BINDER row with too few fields, a non-boolean flag, a completion marker with
the wrong count (as a prefix), a BEGIN without its kind, a duplicate BEGIN for
one root, an END that does not name its root — plus a nonce mismatch, a
missing run marker, a truncated record, a missing root and a nonzero exit.
(2) The probe template must round-trip on the census fixture: composed after
scripts/unused_probe.lean.template with scripts/census_fixture.lean, run over
the fixture's three theorems, the compiler output must parse with no failure,
three records, and a binder count equal to each telescope length. Exit 0 iff
every check passes; each failed check is printed. Run by Audit-Round.ps1
gate 7.
"""
import os, sys, subprocess, uuid, pathlib, importlib.util
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
root = pathlib.Path(__file__).resolve().parents[1]
os.chdir(root)
spec = importlib.util.spec_from_file_location('unused_run', root / 'scripts' / 'unused_run.py')
ur = importlib.util.module_from_spec(spec); spec.loader.exec_module(ur)

fails = []
def check(cond, msg):
    if not cond: fails.append(msg)

P = ''  # `logInfo` lines arrive bare from `lake env lean`
NONCE = 'fixture-nonce'
VALID = (P + f'UNUSED-RUN {NONCE}\n'
         + P + 'UNUSED-BEGIN Example.root theorem 1\n'
         + P + 'BINDER 1 | h | explicit | true | true | false | false | P\n'
         + P + 'UNUSED-END Example.root\n'
         + P + 'UNUSED-DONE 1\n')
NAMES = ['Example.root']

def parse(text, names=NAMES, nonce=NONCE):
    return ur.parse_probe_output(text, names, nonce)

# ---- (1a) accepted shapes
f, recs, res = parse(VALID)
check(not f, f'valid record rejected: {f}')
check(len(recs) == 1 and recs['Example.root']['n'] == 1 and len(recs['Example.root']['binders']) == 1,
      'valid record parsed wrongly')
prefixed = ''.join('X.lean:1:0: info: ' + l + '\n' for l in VALID.splitlines())
f, recs, _ = parse(prefixed)
check(not f and len(recs) == 1, f'prefixed valid record rejected: {f}')
noise = ('X.lean:1:0: warning: something about UNUSED-END in a message\n  continuation UNUSED-DONE 1\n'
         + VALID)
f, recs, _ = parse(noise)
check(not f and len(recs) == 1, f'a tag inside another message was taken as an event: {f}')
# alias policy: the same declaration requested under two qualifications gives
# two identical records, merged; a differing second record fails
record = (P + 'UNUSED-BEGIN Example.root theorem 1\n'
          + P + 'BINDER 1 | h | explicit | true | true | false | false | P\n'
          + P + 'UNUSED-END Example.root\n')
alias_ok = P + f'UNUSED-RUN {NONCE}\n' + record + record + P + 'UNUSED-DONE 2\n'
f, recs, resv = parse(alias_ok, names=['Example.root', 'root'])
check(not f and len(recs) == 1 and len(resv) == 2, f'identical alias records not merged: {f}')
alias_bad = (P + f'UNUSED-RUN {NONCE}\n' + record
             + record.replace('| true | true |', '| true | false |') + P + 'UNUSED-DONE 2\n')
f, _, _ = parse(alias_bad, names=['Example.root', 'root'])
check(bool(f), 'a differing duplicate record was accepted')
novalue = VALID.replace(P + 'BINDER 1 | h | explicit | true | true | false | false | P\n', P + 'NOVALUE\n')
f, recs, _ = parse(novalue)
check(not f and recs['Example.root']['novalue'] and not recs['Example.root']['binders'],
      f'NOVALUE skip not accepted as a skip: {f}')
# a binder type containing the separator is kept whole
piped = VALID.replace('| P\n', '| a | b\n')
f, recs, _ = parse(piped)
check(not f and recs['Example.root']['binders'][0]['type'] == 'a | b', 'a type containing `|` was split')

# ---- (1b) rejected shapes (the seven of document 04 §2, then five more)
bad = {
    'missing_binders': VALID.replace(P + 'BINDER 1 | h | explicit | true | true | false | false | P\n', ''),
    'malformed_binder': VALID.replace('BINDER 1 | h | explicit | true | true | false | false | P', 'BINDER 1 | truncated'),
    'invalid_bool': VALID.replace('| true | false | false | P', '| typo | false | false | P'),
    'wrong_done_prefix': VALID.replace('UNUSED-DONE 1', 'UNUSED-DONE 10'),
    'missing_kind': VALID.replace('UNUSED-BEGIN Example.root theorem 1', 'UNUSED-BEGIN Example.root 1'),
    'duplicate_overwrite': VALID.replace(P + 'UNUSED-DONE 1\n', '')
        + P + 'UNUSED-BEGIN Example.root theorem 0\n' + P + 'UNUSED-END Example.root\n' + P + 'UNUSED-DONE 1\n',
    'invalid_end': VALID.replace('UNUSED-END Example.root', 'UNUSED-END-NOT-A-TOKEN'),
    'end_wrong_root': VALID.replace('UNUSED-END Example.root', 'UNUSED-END Other.root'),
    'nonce_mismatch': VALID.replace(f'UNUSED-RUN {NONCE}', 'UNUSED-RUN other'),
    'missing_run': VALID.replace(P + f'UNUSED-RUN {NONCE}\n', ''),
    'truncated': VALID.replace(P + 'UNUSED-END Example.root\n', ''),
    'index_out_of_sequence': VALID.replace('BINDER 1 |', 'BINDER 2 |'),
    'unknown_kind': VALID.replace('| explicit |', '| bogus |'),
    'empty_type': VALID.replace('| false | false | P', '| false | false | '),
    'done_twice': VALID + P + 'UNUSED-DONE 1\n',
    'done_inside_record': VALID.replace(P + 'UNUSED-END Example.root\n', P + 'UNUSED-DONE 1\n' + P + 'UNUSED-END Example.root\n'),
    'count_mismatch': VALID.replace('theorem 1', 'theorem 2'),
}
for name, text in bad.items():
    f, _, _ = parse(text)
    check(bool(f), f'malformed fixture accepted: {name}')
f, _, _ = parse(VALID, names=['Missing.root'])
check(bool(f), 'missing root accepted')
f, _, _ = parse(VALID, names=['Example.root', 'Other.root'])
check(bool(f), 'unresolved second root accepted')

# ---- (2) the template round-trips on the census fixture
NS = 'Sanctions.CensusFixture.'
roots = [NS + 'thm1', NS + 'thm2', NS + 'thm3']
template = (root / 'scripts' / 'unused_probe.lean.template').read_text(encoding='utf-8')
fixture = (root / 'scripts' / 'census_fixture.lean').read_text(encoding='utf-8')
nonce = uuid.uuid4().hex
probe = (template + '\n' + fixture + '\n' + f'#unusedRun "{nonce}"\n'
         + '\n'.join(f'#unused {n}' for n in roots) + f'\n#unusedDone {len(roots)}\n')
tmpdir = root / 'tmp'; tmpdir.mkdir(exist_ok=True)
tmp = tmpdir / f'_unused_selftest_{nonce}.lean'
tmp.write_text(probe, encoding='utf-8')
env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get('LEAN_NUM_THREADS', '4'))
try:
    res = subprocess.run(['lake', 'env', 'lean', str(tmp)], capture_output=True, env=env)
finally:
    tmp.unlink(missing_ok=True)
out = (res.stdout + res.stderr).decode('utf-8', 'replace')
check(res.returncode == 0, 'fixture probe did not elaborate: '
      + '\n'.join(l for l in out.splitlines() if 'error' in l)[:2000])
f, recs, resv = ur.parse_probe_output(out, roots, nonce)
check(not f, f'fixture output failed the strict parse: {f}')
check(len(recs) == 3 and len(resv) == 3, f'expected 3 fixture records, parsed {len(recs)}')
for rn, r in recs.items():
    check(r['closed'] and not r['novalue'] and len(r['binders']) == r['n'] and r['n'] > 0,
          f'{rn}: telescope {r["n"]}, binders {len(r["binders"])}, closed {r["closed"]}')
    for i, b in enumerate(r['binders'], 1):
        check(b['k'] == i and b['type'], f'{rn}: binder {i} malformed')

if fails:
    print('FAIL: unused-binder self-test'); print('\n'.join('  ' + x for x in fails)); sys.exit(1)
print(f'OK: unused-binder self-test ({len(bad) + 9} parser checks, {len(recs)} fixture records, '
      f'{sum(len(r["binders"]) for r in recs.values())} fixture binders)')
