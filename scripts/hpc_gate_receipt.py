#!/usr/bin/env python3
"""Content-bound evidence for the HPC Lean gate (CLAUDE.md Rule 26); standard library only.

Invoked on the compute node by scripts/hpc-leanbuild.sh:

    hpc_gate_receipt.py snapshot --pkg P --work W --out O --label before|after
    hpc_gate_receipt.py finalize --pkg P --work W --out O --build-rc N --audit-rc N ...

Ported on 2026-10-01 from HigherOrderBelief's analysis/hpc_gate_receipt.py and adapted to this
project: the package carries the project under `project/`, the seven-gate audit runs in the same
job (so the one file it rewrites, HEADLINE-SNAPSHOT.md, is exempt from the after-snapshot), the
axiom scan covers the round's new declarations (RoundScan.lean), and warnings are inventoried
rather than failed here -- the local verifier classifies them against the reviewed baseline.

The node status written here is NODE_GATE_PASS / NODE_GATE_FAIL. It is execution and coverage
evidence only; a Lean result (FORMAL_PASS) is decided locally by scripts/hpc-verify-return.py.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import pathlib
import re
import subprocess
import sys
import zipfile

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Rewritten by audit gate 5 (Generate-HeadlineSnapshot.ps1); returned separately.
AUDIT_MUTABLE = {"HEADLINE-SNAPSHOT.md"}
LOGS = ("build_full.log", "audit.log", "round_axiom_scan.log", "cache_get.log",
        "lean_version.log", "toolchain_install.log", "map_scan.log", "leanchecker.log")


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(4 * 1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def identity(path, relative):
    if path.is_symlink() or not path.is_file():
        raise ValueError("not a regular contained file: " + str(path))
    return {"path": relative, "bytes": path.stat().st_size, "sha256": digest(path)}


def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")


def package_rows(pkg):
    rows = list(csv.DictReader((pkg / "PACKAGE_MANIFEST.csv").read_text(encoding="utf-8").splitlines()))
    expected = set()
    for row in rows:
        rel = row["path"]
        path = pkg / rel
        path.resolve().relative_to(pkg.resolve())
        if rel in expected:
            raise ValueError("duplicate package member: " + rel)
        expected.add(rel)
        if identity(path, rel) != {"path": rel, "bytes": int(row["bytes"]), "sha256": row["sha256"]}:
            raise ValueError("package identity mismatch: " + rel)
    actual = {p.relative_to(pkg).as_posix() for p in pkg.rglob("*") if p.is_file()}
    if actual != expected | {"PACKAGE_MANIFEST.csv"}:
        raise ValueError("package inventory mismatch")
    return rows


def lean_code(text):
    """Mask nested Lean comments and quoted strings, preserving line numbers."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        two, ch = text[i:i + 2], text[i]
        if depth:
            if two == "/-":
                depth += 1; out.extend("  "); i += 2; continue
            if two == "-/":
                depth -= 1; out.extend("  "); i += 2; continue
            out.append("\n" if ch == "\n" else " "); i += 1; continue
        if quoted:
            if ch == "\\" and i + 1 < len(text):
                out.extend("  "); i += 2; continue
            if ch == '"':
                quoted = False
            out.append("\n" if ch == "\n" else " "); i += 1; continue
        if two == "/-":
            depth = 1; out.extend("  "); i += 2; continue
        if two == "--":
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            out.extend(" " * (end - i)); i = end; continue
        if ch == '"':
            quoted = True; out.append(" "); i += 1; continue
        out.append(ch); i += 1
    if depth or quoted:
        raise ValueError("unterminated source comment/string")
    return "".join(out)


def axiom_audit(scan_source, output):
    expected = re.findall(r"^#print axioms\s+(\S+)\s*$", scan_source, re.M)
    actual, duplicates = {}, []
    pattern = r"^'(.+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))"
    for match in re.finditer(pattern, output, re.M):
        name = match[1]
        if name in actual:
            duplicates.append(name)
        actual[name] = sorted(x.strip() for x in (match[2] or "").split(",") if x.strip())
    disallowed = {n: sorted(set(a) - ALLOWED_AXIOMS) for n, a in actual.items() if set(a) - ALLOWED_AXIOMS}
    missing, extra = sorted(set(expected) - actual.keys()), sorted(actual.keys() - set(expected))
    return {"expected": len(expected), "observed": len(actual),
            "with_axioms": sum(bool(a) for a in actual.values()),
            "without_axioms": sum(not a for a in actual.values()),
            "missing": missing, "extra": extra, "duplicates": duplicates,
            "disallowed": disallowed, "declarations": actual,
            "passed": bool(expected) and not (missing or extra or duplicates or disallowed)
                      and len(expected) == len(set(expected))}


def warning_inventory(text):
    """Every `warning: <path>:<line>:<col>: <message>` head in a lake log, path normalised."""
    out = []
    for m in re.finditer(r"^warning: (?P<path>[^\n:]+):(?P<line>\d+):(?P<col>\d+): (?P<msg>[^\n]*)$", text, re.M):
        path = re.sub(r"^(?:\./)+", "", m["path"])
        out.append({"path": path, "line": int(m["line"]), "col": int(m["col"]), "message": m["msg"].strip()})
    return out


def source_identity(pkg, work):
    """Every packaged project file is in the work tree byte for byte, and the work tree's Lean
    sources are exactly the packaged ones (no stray module could join the build)."""
    rows = package_rows(pkg)
    inputs = [r for r in rows if r["path"].startswith("project/")
              and r["path"][len("project/"):] not in AUDIT_MUTABLE]
    sources = []
    for row in inputs:
        rel = row["path"][len("project/"):]
        got = identity(work / rel, rel)
        if got != {"path": rel, "bytes": int(row["bytes"]), "sha256": row["sha256"]}:
            raise ValueError("work source differs from submitted package: " + rel)
        sources.append(got)
    # Lean files only: the tree also tracks non-Lean files under Sanctions/ (a README), which the
    # first round-BD run (job 30478518) compared against a *.lean listing and failed on.
    wanted = {r["path"][len("project/"):] for r in inputs
              if r["path"].startswith("project/Sanctions/") and r["path"].endswith(".lean")}
    found = {p.relative_to(work).as_posix() for p in (work / "Sanctions").rglob("*.lean")}
    if wanted != found:
        raise ValueError("work Lean source inventory differs from submitted package: "
                         f"{len(wanted - found)} missing, {len(found - wanted)} extra")
    return sources


def snapshot(pkg, work, out, label):
    sources = source_identity(pkg, work)
    deps = []
    manifest = json.loads((work / "lake-manifest.json").read_text(encoding="utf-8"))
    for dep in manifest["packages"]:
        if dep["type"] != "git":
            raise ValueError("unhandled dependency kind: " + dep["type"])
        path = work / ".lake/packages" / dep["name"]
        head = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True)
        if head != dep["rev"] or dirty:
            raise ValueError("dependency pin/tracked-source mismatch: " + dep["name"])
        deps.append({"name": dep["name"], "rev": head, "tracked_sources_clean": True})
    cache_root = work / ".lake/packages"
    cache = [identity(p, p.relative_to(cache_root).as_posix()) for p in sorted(cache_root.rglob("*.olean"))]
    if len(cache) < 1000:
        raise ValueError("insufficient dependency cache; no from-source fallback")
    result = {"sources": sources, "dependencies": deps, "cache_oleans": cache}
    write_json(out / ("snapshot_" + label + ".json"), result)
    if label == "after" and result != json.loads((out / "snapshot_before.json").read_text(encoding="utf-8")):
        raise ValueError("source, dependency, or dependency-cache identity changed during gate")


def finalize(args):
    pkg, work, out = args.pkg, args.work, args.out
    failures, notes = [], []
    codes = {key: getattr(args, key) for key in ("build_rc", "audit_rc", "scan_rc", "census_rc", "snapshot_rc",
                                                 "map_rc", "replay_rc")}
    failures.extend(key for key, value in codes.items() if value != 0)
    logs = {}
    for name in LOGS:
        path = out / name
        logs[name] = path.read_text(encoding="utf-8", errors="replace") if path.is_file() else ""
        if not path.is_file():
            failures.append("missing " + name)

    build = logs["build_full.log"]
    m = re.findall(r"Build completed successfully \((\d+) jobs\)", build)
    jobs = int(m[-1]) if m else None
    if jobs is None:
        failures.append("no 'Build completed successfully (N jobs)' line")
    error_lines = len(re.findall(r"error:", build))
    sorry = len(re.findall(r"declaration uses 'sorry'", build))
    warnings = warning_inventory(build)
    if error_lines:
        failures.append("error lines in build_full.log")
    if sorry:
        failures.append("declaration uses 'sorry' in build_full.log")
    if re.search(r"warning:.*(?:sorry|axiom|recompil)", build, re.I):
        failures.append("correctness warning in build_full.log")

    audit_text = logs["audit.log"]
    gates = sorted(set(re.findall(r"\[(\d)/7\]", audit_text)))
    rows = re.findall(r"headline snapshot stable \((\d+) rows", audit_text)
    replay = re.findall(r"headline replay complete \((\d+)/(\d+) rows", audit_text)
    audit = {"all_gates_green": "ALL GATES GREEN." in audit_text,
             "gate_failed_lines": re.findall(r"GATE FAILED: [^\n]*", audit_text),
             "gates_reported": gates,
             "snapshot_rows": int(rows[-1]) if rows else None,
             "replay": [int(x) for x in replay[-1]] if replay else None,
             "snapshot_note": re.findall(r"\[5/7\] NOTE: [^\n]*", audit_text)}
    if not audit["all_gates_green"] or audit["gate_failed_lines"] or gates != list("1234567"):
        failures.append("audit gates")

    scan = (work / "RoundScan.lean").read_text(encoding="utf-8")
    axioms = axiom_audit(scan, logs["round_axiom_scan.log"])
    write_json(out / "axiom_audit.json", axioms)
    if not axioms["passed"]:
        failures.append("round axiom scan coverage or allowed-axiom policy")
    if re.search(r"error:", logs["round_axiom_scan.log"]):
        failures.append("errors in round_axiom_scan.log")

    try:
        before = json.loads((out / "snapshot_before.json").read_text(encoding="utf-8"))
        after = json.loads((out / "snapshot_after.json").read_text(encoding="utf-8"))
        if before != after or not before["sources"] or len(before["cache_oleans"]) < 1000:
            failures.append("before/after snapshot integrity")
    except (OSError, ValueError, KeyError):
        failures.append("missing/invalid before/after snapshots")

    # Placeholder scan of the submitted Lean (comments and strings masked). sorry/admit/axiom fail;
    # native_decide is reported (Rule 16b bans it in headline theorems only; gate 3 does not scan it).
    placeholders, native = [], []
    for p in [work / "Sanctions.lean", *sorted((work / "Sanctions").rglob("*.lean"))]:
        code = lean_code(p.read_text(encoding="utf-8"))
        for mm in re.finditer(r"\b(?:sorry|admit|native_decide|axiom)\b", code):
            row = {"path": p.relative_to(work).as_posix(), "line": code.count("\n", 0, mm.start()) + 1,
                   "token": mm[0]}
            (native if mm[0] == "native_decide" else placeholders).append(row)
    if placeholders:
        failures.append("source placeholder/custom-axiom scan")
    if native:
        notes.append("native_decide present outside the kernel-only path (informational): "
                     + ", ".join(sorted({r["path"] for r in native})))

    # Map-identifier scan (LEANREPO M4): the generated probe reports one summary line.
    mm = re.search(r"MAP-CHECK identifiers=(\d+) missing=(\d+)", logs["map_scan.log"])
    expected_ids = len([l for l in (work / "docs/census/map-identifiers.txt").read_text(encoding="utf-8").splitlines()
                        if l.strip() and not l.startswith("#")])
    map_scan = {"identifiers": int(mm[1]) if mm else None, "missing": int(mm[2]) if mm else None,
                "expected_identifiers": expected_ids,
                "missing_names": re.findall(r"MAP-MISSING (\S+)", logs["map_scan.log"])}
    if not mm or map_scan["missing"] != 0 or map_scan["identifiers"] != expected_ids:
        failures.append("map-identifier scan")

    # Kernel replay (LEANREPO M5): leanchecker -v names each module it replays; every project module
    # must be replayed and none may report a problem. The fresh replay is a pilot, never gating.
    replay_log = logs["leanchecker.log"]
    replayed = sorted(set(re.findall(r"^replaying (\S+)$", replay_log, re.M)))
    problems = re.findall(r"leanchecker found a problem in (\S+)", replay_log)
    fresh_log = (out / "leanchecker_fresh.log").read_text(encoding="utf-8", errors="replace") \
        if (out / "leanchecker_fresh.log").is_file() else ""
    fresh_status = ("completed" if args.fresh_rc == 0 else "timed out (not run to completion)"
                    if args.fresh_rc == 124 else "not completed (rc %d)" % args.fresh_rc)
    replay = {"modules_replayed": len(replayed), "problems": problems, "rc": args.replay_rc,
              "seconds": args.replay_seconds, "command": "lake env leanchecker -v Sanctions",
              "fresh_pilot": {"command": "lake env leanchecker -v --fresh Sanctions.Headlines (timeout 5400 s)",
                              "rc": args.fresh_rc, "seconds": args.fresh_seconds, "status": fresh_status,
                              "log_sha256": hashlib.sha256(fresh_log.encode()).hexdigest()},
              "log_sha256": hashlib.sha256(replay_log.encode()).hexdigest()}

    pin = (work / "lean-toolchain").read_text(encoding="utf-8").strip().split(":")[-1].removeprefix("v")
    if not re.search(r"Lean \(version " + re.escape(pin) + r"[,)]", logs["lean_version.log"]):
        failures.append("Lean runtime version does not match pin")
    expected_oleans = len(list((work / "Sanctions").rglob("*.lean"))) + 1
    oleans = len(list((work / ".lake/build/lib/lean").rglob("*.olean")))
    if oleans != expected_oleans:
        failures.append("project olean coverage")
    replay["expected_modules"] = expected_oleans
    if args.replay_rc != 0 or problems or len(replayed) != expected_oleans:
        failures.append("kernel replay coverage or result")
    if args.clean_before != 0 or args.temp_removed != "true":
        failures.append("from-empty build or temporary cleanup evidence")

    runtime = (out / "runtime.log").read_text(encoding="utf-8", errors="replace") if (out / "runtime.log").is_file() else ""
    def field(rx):
        mm = re.search(rx, runtime, re.M)
        return mm[1] if mm else None
    receipt = {"schema": "spcl-lean-build/v1", "scope": "Lean source/build/audit/axiom evidence only",
               "status": "NODE_GATE_PASS" if not failures else "NODE_GATE_FAIL",
               "failures": failures, "notes": notes, "return_codes": codes, "job_id": args.job_id,
               "node": field(r"node=(\S+)"), "start_utc": field(r"start_utc=(\S+)"),
               "build_started_utc": field(r"^BUILD_STARTED job_id=\S+ utc=(\S+)"),
               "build_done_utc": field(r"^BUILD_DONE build_rc=\S+ utc=(\S+)"),
               "end_utc": field(r"^end_utc=(\S+)"),
               "build": {"jobs": jobs, "error_lines": error_lines, "sorry": sorry,
                         "warnings": warnings},
               "audit": audit,
               "map_scan": map_scan, "kernel_replay": replay,
               "round_axiom_scan": {k: axioms[k] for k in ("expected", "observed", "with_axioms",
                                                           "without_axioms", "missing", "extra",
                                                           "disallowed", "passed")},
               "placeholders": placeholders, "native_decide": native,
               "project_oleans": oleans, "expected_project_oleans": expected_oleans,
               "project_oleans_before": args.clean_before, "run_temporary_removed": args.temp_removed == "true",
               "runtime_and_dependency_cache": "persistent; project build cleared; cache SHA256 before/after",
               "submitted_manifest_sha256": digest(pkg / "PACKAGE_MANIFEST.csv")}
    write_json(out / "gate_receipt.json", receipt)

    # Exact gate artifacts. Excludes mutable Slurm stdout/stderr, progress copies and the vendored
    # tool archives (their identity is in PACKAGE_MANIFEST.csv).
    names = {"gate_receipt.json", "axiom_audit.json", "snapshot_before.json", "snapshot_after.json",
             "runtime.log", "snapshot_before.log", "snapshot_after.log",
             "HEADLINE-SNAPSHOT.regenerated.md", "census.log", "raw-headlines.txt",
             "raw-manuscript.txt", "raw-preds.txt", "unused-binders.md",
             "unused-binders.md.raw.txt", "unused-binders.md.FAILED.txt", "leanchecker_fresh.log", *LOGS}
    members = {n: (out / n).read_bytes() for n in sorted(names) if (out / n).is_file()}
    for p in sorted(pkg.rglob("*")):
        rel = p.relative_to(pkg).as_posix()
        if p.is_file() and (not rel.startswith("vendor/") or rel == "vendor/VENDOR.sha256"):
            members["submitted-source/" + rel] = p.read_bytes()
    buf = io.StringIO()
    writer = csv.writer(buf, lineterminator="\n")
    writer.writerow(["path", "bytes", "sha256"])
    files = []
    for name, data in sorted(members.items()):
        sha = hashlib.sha256(data).hexdigest()
        writer.writerow([name, len(data), sha])
        files.append({"relative_path": name, "bytes": len(data), "sha256": sha})
    members["RETURN_MANIFEST.csv"] = buf.getvalue().encode()
    members["RETURN_MANIFEST.json"] = (json.dumps({"file_count": len(files), "files": files}, indent=1)
                                      + "\n").encode()
    with zipfile.ZipFile(out / "return.zip", "w", zipfile.ZIP_DEFLATED) as z:
        for name, data in sorted(members.items()):
            z.writestr(name, data)
    print("return.zip sha256", digest(out / "return.zip"), "bytes", (out / "return.zip").stat().st_size)
    return 0 if not failures else 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["snapshot", "finalize"])
    for name in ("pkg", "work", "out"):
        parser.add_argument("--" + name, type=pathlib.Path, required=True)
    parser.add_argument("--label", choices=["before", "after"])
    for name in ("build-rc", "audit-rc", "scan-rc", "census-rc", "snapshot-rc", "clean-before",
                 "map-rc", "replay-rc", "replay-seconds", "fresh-rc", "fresh-seconds"):
        parser.add_argument("--" + name, type=int, default=99)
    parser.add_argument("--temp-removed", choices=["true", "false"], default="false")
    parser.add_argument("--job-id", default="")
    args = parser.parse_args()
    if args.command == "snapshot":
        snapshot(args.pkg, args.work, args.out, args.label)
        return 0
    return finalize(args)


if __name__ == "__main__":
    sys.exit(main())
