"""Run the hypothesis-census probe over a list of root declarations.

Usage:
    python scripts/census_run.py <roots-file> <raw-output-file> [census|censusPreds]

`roots-file` holds one declaration name per line (comments with `#`), resolved
under the probe template's `open` line. The probe is written under `tmp/`
(git-ignored), elaborated with `lake env lean` against the built library, and
the raw records are saved verbatim to `raw-output-file` behind a header that
records the source commit, the toolchain and the pass kind.

Fails closed (doc 70, C-3): a nonzero Lean exit, a requested root that does
not resolve, a root that began without ending (truncation), a record count
that differs from the number of distinct requested roots, a missing or wrong
`CENSUS-DONE` marker, or a duplicate root in the request all exit 1. The raw
file is still written so the failure can be read.
"""
import os, sys, subprocess, uuid, pathlib
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
root = pathlib.Path(__file__).resolve().parents[1]
os.chdir(root)
roots_file, out_file = sys.argv[1], sys.argv[2]
cmd = sys.argv[3] if len(sys.argv) > 3 else 'census'   # 'census' or 'censusPreds'
if cmd not in ('census', 'censusPreds'):
    print(f'FAIL: unknown pass kind {cmd!r}'); sys.exit(1)
names = [l.split('#')[0].strip() for l in open(roots_file, encoding='utf-8')]
names = [n for n in names if n]
if not names:
    print('FAIL: empty root list'); sys.exit(1)
dups = sorted({n for n in names if names.count(n) > 1})
if dups:
    print('FAIL: duplicate roots requested: ' + ', '.join(dups)); sys.exit(1)

def git(*a):
    return subprocess.run(['git', *a], capture_output=True, text=True).stdout.strip()
head = git('rev-parse', 'HEAD')
toolchain = (root / 'lean-toolchain').read_text(encoding='utf-8').strip()

template = (root / 'scripts' / 'census_probe.lean.template').read_text(encoding='utf-8')
probe = template + '\n' + '\n'.join(f'#{cmd} {n}' for n in names) + f'\n#censusDone {len(names)}\n'
tmpdir = root / 'tmp'; tmpdir.mkdir(exist_ok=True)
tmp = tmpdir / f'_census_probe_{uuid.uuid4().hex}.lean'
tmp.write_text(probe, encoding='utf-8')
env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get('LEAN_NUM_THREADS', '15'))
try:
    res = subprocess.run(['lake', 'env', 'lean', str(tmp)], capture_output=True, env=env)
finally:
    tmp.unlink(missing_ok=True)
out = res.stdout.decode('utf-8', errors='strict') if b'\xef\xbf\xbd' not in res.stdout else None
if out is None:
    print('FAIL: replacement characters in the compiler output (invalid UTF-8)'); sys.exit(1)
out = out + res.stderr.decode('utf-8', errors='replace')
header = (f'CENSUS-HEAD {head}\nCENSUS-TOOLCHAIN {toolchain}\nCENSUS-CMD {cmd}\n'
          f'CENSUS-REQUESTED {len(names)}\n')
pathlib.Path(out_file).write_text(header + out, encoding='utf-8')

# ---- fail-closed checks
fails = []
if res.returncode != 0:
    fails.append(f'lean exit {res.returncode}')
    fails += [l for l in out.splitlines() if 'error' in l.lower()][:20]
beg_tag, end_tag = ('CENSUS-BEGIN ', 'CENSUS-END') if cmd == 'census' else ('PRED-BEGIN ', 'PRED-END')
begun = []; open_rec = None
for line in out.splitlines():
    s = line.strip()
    if s.startswith(beg_tag):
        if open_rec is not None: fails.append(f'record {open_rec} began without ending')
        open_rec = s[len(beg_tag):].strip(); begun.append(open_rec)
    elif s.startswith(end_tag):
        if open_rec is None: fails.append('END without BEGIN')
        open_rec = None
if open_rec is not None: fails.append(f'record {open_rec} truncated at end of output')
if len(begun) != len(names):
    fails.append(f'{len(begun)} records for {len(names)} roots')
if len(set(begun)) != len(begun):
    fails.append('duplicate records: ' + ', '.join(sorted({b for b in begun if begun.count(b) > 1})))
for n in names:
    hits = [b for b in begun if b == n or b.endswith('.' + n)]
    if len(hits) != 1:
        fails.append(f'root {n!r} resolved to {len(hits)} records')
if f'CENSUS-DONE {len(names)}' not in out:
    fails.append('completion marker CENSUS-DONE missing or wrong')
print(f'lean exit {res.returncode}; {len(names)} roots requested; {len(begun)} records; head {head[:9]}; pass {cmd}')
if fails:
    print('FAIL:'); print('\n'.join('  ' + f for f in fails)); sys.exit(1)
print('OK: every requested root produced exactly one complete record.')
