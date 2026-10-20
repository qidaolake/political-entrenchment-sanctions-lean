"""Self-test of the hypothesis-census instrument (doc 71 round G, T2).

Usage:
    python scripts/census_selftest.py

Composes scripts/census_probe.lean.template + scripts/census_fixture.lean +
`#census` over the fixture's three theorems, elaborates with `lake env lean`,
parses the records with scripts/census_build.py's parser, and asserts the
behaviours the fixture documents. Also checks that the runner and the builder
fail closed on a bogus root and on a truncated raw file. Exit 0 iff every
check passes; each failed check is printed. Run by Audit-Round.ps1 gate 7.
"""
import os, sys, subprocess, uuid, pathlib, importlib.util
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
root = pathlib.Path(__file__).resolve().parents[1]
os.chdir(root)
spec = importlib.util.spec_from_file_location('census_build', root / 'scripts' / 'census_build.py')
cb = importlib.util.module_from_spec(spec); spec.loader.exec_module(cb)

fails = []
def check(cond, msg):
    if not cond: fails.append(msg)

NS = 'Sanctions.CensusFixture.'
roots = [NS + 'thm1', NS + 'thm2', NS + 'thm3']
template = (root / 'scripts' / 'census_probe.lean.template').read_text(encoding='utf-8')
fixture = (root / 'scripts' / 'census_fixture.lean').read_text(encoding='utf-8')
probe = template + '\n' + fixture + '\n' + '\n'.join(f'#census {n}' for n in roots) + f'\n#censusDone {len(roots)}\n'
tmpdir = root / 'tmp'; tmpdir.mkdir(exist_ok=True)
tmp = tmpdir / f'_census_selftest_{uuid.uuid4().hex}.lean'
tmp.write_text(probe, encoding='utf-8')
env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get('LEAN_NUM_THREADS', '4'))
try:
    res = subprocess.run(['lake', 'env', 'lean', str(tmp)], capture_output=True, env=env)
finally:
    tmp.unlink(missing_ok=True)
out = res.stdout.decode('utf-8', 'replace') + res.stderr.decode('utf-8', 'replace')
if res.returncode != 0:
    print('FAIL: fixture probe did not elaborate'); print('\n'.join(l for l in out.splitlines() if 'error' in l)[:3000]); sys.exit(1)
raw = tmpdir / f'_census_selftest_{uuid.uuid4().hex}.txt'
raw.write_text(f'CENSUS-HEAD selftest\nCENSUS-TOOLCHAIN selftest\nCENSUS-CMD census\nCENSUS-REQUESTED {len(roots)}\n' + out, encoding='utf-8')
try:
    recs, hdr = cb.parse(str(raw))
finally:
    raw.unlink(missing_ok=True)
R = {r['name']: r for r in recs}
check(set(R) == set(roots), f'records {sorted(R)} != roots')

t1 = R[NS + 'thm1']
names = [b['name'] for b in t1['binders']]
check(names == ['a', 'S', 'C', 'h', 'hop', 'hh'], f'thm1 binders {names}')
check(t1['binders'][0]['bi'] == 'implicit' and not t1['binders'][0]['isProp'], 'implicit scalar a not recorded as implicit data')
S = t1['binders'][1]
check(S['struct'] == NS + 'Sub', f'S not expanded as Sub: {S["struct"]}')
qn = [f['qname'] for f in S['fields']]
check(NS + 'Base.q' in qn and NS + 'Base.hq' in qn and NS + 'Sub.hq1' in qn, f'Sub fields {qn}')
check(NS + 'Sub.hq' not in qn, 'inherited hq keyed under Sub instead of Base')
C = t1['binders'][2]
check(C['struct'] == NS + 'Cert', 'C not expanded as Cert')
fD = next((f for f in C['fields'] if f['qname'] == NS + 'Cert.D'), None)
check(fD is not None and fD['struct'] == NS + 'Base', 'Cert.D not marked as a structure field')
sub = [g['qname'] for g in (fD['sub'] if fD else [])]
check(NS + 'Base.q' in sub and NS + 'Base.hq' in sub, f'level-2 fields of Cert.D: {sub}')
fhD = next((f for f in C['fields'] if f['qname'] == NS + 'Cert.hD'), None)
check(fhD is not None and fhD['unfold'] is not None and '0 <' in fhD['unfold'], f'Cert.hD not unfolded: {fhD and fhD["unfold"]}')
fhA = next((f for f in C['fields'] if f['qname'] == NS + 'Cert.hAlias'), None)
check(fhA is not None and fhA['unfold'] is not None, 'Cert.hAlias (reducible alias) not unfolded one step')
h = t1['binders'][3]
check(h['isProp'] and h['unfold'] is not None and '0 < a' in h['unfold'], f'binder h : Pred a not unfolded: {h["unfold"]}')
hop = t1['binders'][4]
check(hop['isProp'] and hop['unfold'] is None, 'opaque predicate was unfolded')
check(t1['binders'][5]['isProp'] and t1['binders'][5]['struct'] is None, 'hh misclassified')

t3 = R[NS + 'thm3']
Dp = t3['binders'][0]
check(Dp['struct'] == NS + 'Deep', 'Dp not expanded as Deep')
fC = next((f for f in Dp['fields'] if f['qname'] == NS + 'Deep.C'), None)
check(fC is not None and fC['struct'] == NS + 'Cert', 'Deep.C not marked structure')
sub3 = [g['qname'] for g in (fC['sub'] if fC else [])]
check(NS + 'Cert.D' in sub3 and NS + 'Cert.hD' in sub3, f'level-2 fields of Deep.C: {sub3}')
fr = [reason for _, reason in Dp['frontier']]
check(any('depth limit' in r and 'Base' in r for r in fr), f'no depth-limit FRONTIER for Deep.C > Cert.D: {fr}')
check(any('not unfolded' in r for r in fr), f'no FRONTIER for the level-2 predicate field: {fr}')

# display keys: alpha-renamed binders are two keys (documented non-invariance)
t2 = R[NS + 'thm2']
k1 = cb.display_key(t1['binders'][3]['type']); k2 = cb.display_key(t2['binders'][2]['type'])
check(k1 != k2, 'display keys of alpha-renamed binders coincide (the documented limitation changed; update the docs)')
# schema identity: Base.hq reached via Sub and via Cert.D is ONE owner-qualified key
allq = [f['qname'] for r in recs for b in r['binders'] for f in b['fields']] + \
       [g['qname'] for r in recs for b in r['binders'] for f in b['fields'] for g in f['sub']]
check(allq.count(NS + 'Base.hq') >= 2 and NS + 'Sub.hq' not in allq, 'inherited-field owner not canonical')

# fail-closed runner: a bogus root must exit 1
bogus = tmpdir / f'_census_selftest_roots_{uuid.uuid4().hex}.txt'
bogus.write_text('Sanctions.CensusFixture.thm1\nSanctions.CensusFixture.no_such_root\n', encoding='utf-8')
rawb = tmpdir / f'_census_selftest_raw_{uuid.uuid4().hex}.txt'
try:
    rr = subprocess.run([sys.executable, 'scripts/census_run.py', str(bogus), str(rawb)], capture_output=True, env=env)
    check(rr.returncode != 0, 'runner accepted a root that does not resolve')
finally:
    bogus.unlink(missing_ok=True); rawb.unlink(missing_ok=True)
# fail-closed builder: a truncated raw file must be refused
trunc = tmpdir / f'_census_selftest_trunc_{uuid.uuid4().hex}.txt'
lines = out.splitlines()
cut = max(i for i, l in enumerate(lines) if l.strip().startswith('CENSUS-END'))
trunc.write_text(f'CENSUS-HEAD selftest\nCENSUS-TOOLCHAIN selftest\nCENSUS-CMD census\nCENSUS-REQUESTED {len(roots)}\n' + '\n'.join(lines[:cut]) + '\n', encoding='utf-8')
try:
    try:
        cb.parse(str(trunc)); check(False, 'builder accepted a truncated raw file')
    except SystemExit:
        pass
finally:
    trunc.unlink(missing_ok=True)

if fails:
    print('CENSUS SELF-TEST FAILED:'); print('\n'.join('  - ' + f for f in fails)); sys.exit(1)
print(f'CENSUS SELF-TEST OK: {len(recs)} fixture roots, every documented behaviour observed.')
