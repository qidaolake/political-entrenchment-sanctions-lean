#!/usr/bin/env python3
"""Independent local verification of an HPC Lean return (CLAUDE.md Rule 26).

    python scripts/hpc-verify-return.py <return.zip> [--json OUT]

Ported on 2026-10-01 from HigherOrderBelief's analysis/hpc-verify-return.py. A scheduler state
is not a Lean status, and neither is the node's own receipt: every check below re-derives its
verdict from the returned raw logs and files. Each check prints one PASS/FAIL line.

  1. RETURN_MANIFEST.csv and RETURN_MANIFEST.json rows verified by size and SHA-256.
  2. Returned source identical, file by file, to the working tree (the job script and helper
     through their in-tree paths; RoundScan.lean regenerated from scripts/hpc-round-scan.txt).
  3. Toolchain: lean_version.log matches lean-toolchain.
  4. Build log recounted: `Build completed successfully (N jobs)`, zero `error:` lines, zero
     `declaration uses 'sorry'`, and every warning matched to scripts/hpc-warning-baseline.txt.
  5. Audit log: ALL GATES GREEN, all seven gate lines, no GATE FAILED line.
  6. Returned regenerated HEADLINE-SNAPSHOT.md compared with the working tree's through the
     gate's own scripts/Compare-Snapshot.ps1 (pwsh 7): verdict must be 'stable'.
  7. Round axiom scan re-derived from the raw log: full coverage, allowed axioms only.
  8. Node receipt: from-empty build, project olean coverage, temp removed, before/after
     snapshot integrity, no node failures.
  9. Map-identifier scan (LEANREPO M4): every identifier of docs/census/map-identifiers.txt names a
     declaration of the built environment.
 10. Kernel replay (LEANREPO M5): `leanchecker -v Sanctions` replayed every project module and
     reported no problem; the fresh replay of the headline closure is reported, never counted as a
     pass unless it completed.
"""
import argparse
import csv
import hashlib
import io
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import zipfile

REPO = pathlib.Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ALIASES = {"build.sh": "scripts/hpc-leanbuild.sh", "hpc_gate_receipt.py": "scripts/hpc_gate_receipt.py"}
GENERATED = {"project/RoundScan.lean", "PACKAGE_MANIFEST.csv", "SOURCE_STATE.json", "vendor/VENDOR.sha256"}


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("return_zip", type=pathlib.Path)
    ap.add_argument("--json", type=pathlib.Path, help="write a machine-readable summary here")
    args = ap.parse_args()
    z = zipfile.ZipFile(args.return_zip)
    names = set(z.namelist())
    ok = True
    summary = {"return_zip": str(args.return_zip), "return_sha256": sha(args.return_zip.read_bytes())}

    def report(line, good=True):
        nonlocal ok
        ok = ok and good
        print(("PASS " if good else "FAIL ") + line, flush=True)

    def text(name):
        return z.read(name).decode("utf-8", "replace") if name in names else ""

    print(f"return archive: {args.return_zip.name}  sha256={summary['return_sha256']}")

    # 1. manifests
    rows = list(csv.DictReader(io.StringIO(text("RETURN_MANIFEST.csv"))))
    bad = [r["path"] for r in rows if r["path"] not in names or
           len(z.read(r["path"])) != int(r["bytes"]) or sha(z.read(r["path"])) != r["sha256"]]
    jrows = json.loads(text("RETURN_MANIFEST.json") or "{}").get("files", [])
    jbad = [r["relative_path"] for r in jrows if r["relative_path"] not in names or
            sha(z.read(r["relative_path"])) != r["sha256"]]
    report(f"manifests: csv {len(rows) - len(bad)}/{len(rows)}, json {len(jrows) - len(jbad)}/{len(jrows)} verified",
           rows and not bad and len(jrows) == len(rows) and not jbad)

    # 2. returned source identity
    src = sorted(n for n in names if n.startswith("submitted-source/"))
    identical = generated = 0
    mismatch = []
    scan_names = [l.strip() for l in (REPO / "scripts/hpc-round-scan.txt").read_text(encoding="utf-8").splitlines()
                  if l.strip() and not l.lstrip().startswith("#")]
    expected_scan = ("import Sanctions\n" + "".join(f"#print axioms {n}\n" for n in scan_names)).encode()
    for n in src:
        rel = n[len("submitted-source/"):]
        data = z.read(n)
        local = REPO / (ALIASES.get(rel) or rel.removeprefix("project/"))
        if rel == "project/RoundScan.lean":
            if data == expected_scan:
                identical += 1
            else:
                mismatch.append(rel)
        elif rel in GENERATED:
            generated += 1
        elif local.is_file() and local.read_bytes() == data:
            identical += 1
        else:
            mismatch.append(rel)
    state = json.loads(text("submitted-source/SOURCE_STATE.json") or "{}")
    summary["source_commit"] = state.get("commit")
    for m in mismatch[:10]:
        print("     SOURCE MISMATCH:", m)
    report(f"returned source: {identical} identical, {generated} generated, {len(mismatch)} mismatched "
           f"(of {len(src)}); package cut from {state.get('branch')} @ {state.get('commit')}",
           src and not mismatch)

    # 3. toolchain
    pin = (REPO / "lean-toolchain").read_text(encoding="utf-8").strip().split(":")[-1].removeprefix("v")
    ver = re.search(r"Lean \(version [^)]*\)", text("lean_version.log"))
    summary["lean_version"] = ver[0] if ver else None
    report(f"toolchain: pin {pin}; runtime {summary['lean_version']}",
           bool(ver) and re.search(r"version " + re.escape(pin) + r"[,)]", ver[0]) is not None)

    # 4. build log
    build = text("build_full.log")
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", build)
    errors = len(re.findall(r"error:", build))
    sorry = len(re.findall(r"declaration uses 'sorry'", build))
    summary["jobs"] = int(jobs[-1]) if jobs else None
    report(f"build: {summary['jobs']} jobs, error-lines={errors}, sorry={sorry}", bool(jobs) and not errors and not sorry)
    # Counted baseline: <count>|<path>|<exact first message line>. A (path, message) key whose
    # count in this log exceeds its baseline entry is new and fails the gate.
    allowed = {}
    for l in (REPO / "scripts/hpc-warning-baseline.txt").read_text(encoding="utf-8").splitlines():
        if l.strip() and not l.lstrip().startswith("#"):
            n, path, msg = l.split("|", 2)
            allowed[(path, msg)] = int(n)
    warns, seen = [], {}
    for m in re.finditer(r"^warning: (?P<path>[^\n:]+):(?P<line>\d+):(?P<col>\d+): (?P<msg>[^\n]*)$", build, re.M):
        path = re.sub(r"^(?:\./)+", "", m["path"])
        key = (path, m["msg"].strip())
        seen[key] = seen.get(key, 0) + 1
        warns.append({"path": path, "line": int(m["line"]), "message": key[1],
                      "baseline": seen[key] <= allowed.get(key, 0)})
    unknown = [w for w in warns if not w["baseline"]]
    cleared = sum(max(0, n - seen.get(k, 0)) for k, n in allowed.items())
    summary["warnings"] = warns
    summary["warnings_cleared_vs_baseline"] = cleared
    for w in unknown:
        print(f"     warning (NEW) {w['path']}:{w['line']}: {w['message'][:100]}")
    report(f"warnings: {len(warns)} total, {len(warns) - len(unknown)} within the reviewed baseline, "
           f"{len(unknown)} new; {cleared} baseline warning(s) no longer present", not unknown)

    # 5. audit
    audit = text("audit.log")
    gates = sorted(set(re.findall(r"\[(\d)/7\]", audit)))
    rows_m = re.findall(r"headline snapshot stable \((\d+) rows", audit)
    replay = re.findall(r"headline replay complete \((\d+)/(\d+) rows", audit)
    census = re.findall(r"census coverage OK \(([^)]*)\)", audit)
    summary["audit"] = {"gates": gates, "snapshot_rows": rows_m[-1] if rows_m else None,
                        "replay": "/".join(replay[-1]) if replay else None,
                        "census": census[-1] if census else None,
                        "lines": [l for l in audit.splitlines() if re.match(r"\s*\[\d/7\]", l)]}
    for l in summary["audit"]["lines"]:
        print("     " + l.strip())
    report(f"audit: gates {''.join(gates)}, snapshot rows {summary['audit']['snapshot_rows']}, "
           f"replay {summary['audit']['replay']}",
           "ALL GATES GREEN." in audit and "GATE FAILED" not in audit and gates == list("1234567"))

    # 6. regenerated snapshot vs working tree, through the gate's own comparison
    regen = z.read("HEADLINE-SNAPSHOT.regenerated.md") if "HEADLINE-SNAPSHOT.regenerated.md" in names else None
    verdict = None
    if regen is not None:
        with tempfile.TemporaryDirectory() as td:
            p = pathlib.Path(td) / "regen.md"
            p.write_bytes(regen)
            # Paths travel by environment: Windows argv quoting collapses a UNC path's leading `\\`.
            env = dict(os.environ, CMP_SCRIPT=str(REPO / "scripts/Compare-Snapshot.ps1"),
                       CMP_BEFORE=str(REPO / "HEADLINE-SNAPSHOT.md"), CMP_AFTER=str(p))
            cmd = (". $env:CMP_SCRIPT; $r = Compare-HeadlineSnapshot (Get-Content -Raw -LiteralPath $env:CMP_BEFORE) "
                   "(Get-Content -Raw -LiteralPath $env:CMP_AFTER); $r.Verdict + '|' + ($r.Moved -join ',')")
            # Process-scoped bypass: the repository sits on a UNC share, which RemoteSigned treats
            # as remote, so dot-sourcing the in-tree comparison is otherwise refused.
            r = subprocess.run(["pwsh", "-NoProfile", "-NonInteractive", "-ExecutionPolicy", "Bypass",
                                "-Command", cmd],
                               capture_output=True, text=True, env=env)
            verdict = r.stdout.strip()
            if r.stderr.strip():
                print("     pwsh stderr:", r.stderr.strip()[:400])
    summary["snapshot_verdict"] = verdict
    report(f"regenerated snapshot vs working tree: {verdict}", bool(verdict) and verdict.startswith("stable|"))

    # 7. round axiom scan, re-derived
    scan_log = text("round_axiom_scan.log")
    actual = {}
    for m in re.finditer(r"^'(.+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", scan_log, re.M):
        actual[m[1]] = sorted(x.strip() for x in (m[2] or "").split(",") if x.strip())
    missing = sorted(set(scan_names) - actual.keys())
    disallowed = {k: v for k, v in actual.items() if not set(v) <= ALLOWED}
    summary["round_axiom_scan"] = {"expected": len(scan_names), "observed": len(actual),
                                   "without_axioms": sum(not v for v in actual.values()),
                                   "missing": missing, "disallowed": disallowed}
    for k in missing[:10]:
        print("     MISSING:", k)
    for k, v in list(disallowed.items())[:10]:
        print("     DISALLOWED:", k, v)
    report(f"round axiom scan: {len(actual)}/{len(scan_names)} declarations, {len(disallowed)} outside "
           f"{sorted(ALLOWED)}", not missing and not disallowed and "error:" not in scan_log)

    # 8. node receipt
    rec = json.loads(text("gate_receipt.json") or "{}")
    summary["node"] = {k: rec.get(k) for k in ("status", "job_id", "node", "start_utc", "build_started_utc",
                                              "build_done_utc", "end_utc", "failures", "notes",
                                              "project_oleans", "expected_project_oleans",
                                              "project_oleans_before", "run_temporary_removed")}
    for k, v in summary["node"].items():
        print(f"     receipt[{k}] = {v}")
    report("node receipt: from-empty, olean coverage, temp removed, snapshot integrity",
           rec.get("status") == "NODE_GATE_PASS" and not rec.get("failures")
           and rec.get("project_oleans_before") == 0 and rec.get("run_temporary_removed") is True
           and rec.get("project_oleans") == rec.get("expected_project_oleans"))

    # 9. map-identifier scan, re-derived
    map_log = text("map_scan.log")
    want = len([l for l in (REPO / "docs/census/map-identifiers.txt").read_text(encoding="utf-8").splitlines()
                if l.strip() and not l.startswith("#")])
    mc = re.search(r"MAP-CHECK identifiers=(\d+) missing=(\d+)", map_log)
    for name in re.findall(r"MAP-MISSING (\S+)", map_log)[:10]:
        print("     MAP-MISSING:", name)
    summary["map_scan"] = {"identifiers": int(mc[1]) if mc else None, "missing": int(mc[2]) if mc else None,
                           "expected": want}
    report(f"map-identifier scan: {summary['map_scan']['identifiers']}/{want} identifiers, "
           f"{summary['map_scan']['missing']} missing",
           bool(mc) and int(mc[1]) == want and int(mc[2]) == 0 and "error:" not in map_log)

    # 10. kernel replay, re-derived from the raw log
    replay_log = text("leanchecker.log")
    replayed = sorted(set(re.findall(r"^replaying (\S+)$", replay_log, re.M)))
    problems = re.findall(r"leanchecker found a problem in (\S+)", replay_log)
    rrec = rec.get("kernel_replay") or {}
    expected_modules = rec.get("expected_project_oleans")
    summary["kernel_replay"] = {"modules_replayed": len(replayed), "expected": expected_modules,
                                "problems": problems, "rc": rrec.get("rc"), "seconds": rrec.get("seconds"),
                                "fresh_pilot": rrec.get("fresh_pilot")}
    report(f"kernel replay: {len(replayed)}/{expected_modules} modules replayed by leanchecker, "
           f"{len(problems)} problem(s), {rrec.get('seconds')} s",
           bool(replayed) and len(replayed) == expected_modules and not problems and rrec.get("rc") == 0)
    fresh = rrec.get("fresh_pilot") or {}
    print(f"     fresh replay pilot (not gating): {fresh.get('status')}, {fresh.get('seconds')} s")

    summary["verdict"] = "FORMAL_PASS" if ok else "FORMAL_FAIL"
    print("OVERALL:", summary["verdict"])
    if args.json:
        args.json.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
