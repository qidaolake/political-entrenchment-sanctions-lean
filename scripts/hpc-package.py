#!/usr/bin/env python3
"""Build the HPC Lean-gate package (CLAUDE.md Rule 26) from the committed tree.

    python scripts/hpc-package.py <run-id> [--out DIR] [--vendor DIR]

Ported on 2026-10-01 from HigherOrderBelief's analysis/hpc-package.py. Emits
`<out>/<run-id>/leanbuild.zip` with the shape the `uconn-hpc-work` companion expects:

    leanbuild/build.sh                the job script (scripts/hpc-leanbuild.sh)
    leanbuild/hpc_gate_receipt.py     the on-node receipt helper
    leanbuild/project/...             every tracked file under PROJECT_SPECS, as checked out
    leanbuild/project/RoundScan.lean  generated: `#print axioms` for scripts/hpc-round-scan.txt
    leanbuild/vendor/...              pwsh, node and elan release archives, digest-pinned
    leanbuild/SOURCE_STATE.json       the commit the package was cut from
    leanbuild/PACKAGE_MANIFEST.csv    every member except itself, with size and SHA-256

and `<out>/<run-id>/activation_args.json` for `activate_package`.

Guards, all fatal:
  * every packaged path is clean against HEAD (no modified or untracked file), so the receipt
    binds to a commit;
  * the three toolchain pins match the recorded baseline (Rule 17);
  * the vendored archives match their pinned digests (each also checked against the
    publisher's checksum when it was downloaded);
  * the job script is LF-only and passes the companion's managed-temporary-storage and
    spool-path admission locally, so that class of failure costs no scheduler round.

Determinism: members sorted, fixed timestamps, no run ID or clock inside the archive. Re-running
on an unchanged tree reproduces the archive byte-for-byte.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys
import zipfile

REPO = pathlib.Path(__file__).resolve().parent.parent
SCRIPT = REPO / "scripts" / "hpc-leanbuild.sh"
HELPER = REPO / "scripts" / "hpc_gate_receipt.py"
SCAN_LIST = REPO / "scripts" / "hpc-round-scan.txt"
PINS = ("lakefile.toml", "lean-toolchain", "lake-manifest.json")
PROJECT_SPECS = ("Sanctions.lean", "Sanctions", "lakefile.toml", "lean-toolchain",
                 "lake-manifest.json", "scripts", "docs/census", "HEADLINE-SNAPSHOT.md",
                 "README.md", "BUILD-STATUS.md")

# SHA-256 of the three pins (working-tree bytes) as of round BD, 2026-10-01. A mismatch means a
# dependency revision moved; that is a Rule-17 event and must be surfaced, never packaged around.
PIN_BASELINE = {
    "lakefile.toml": "3e6170572705a74eb7434401d56b47eea6d0d8935be1bec8ba6f146bb823c90e",
    "lean-toolchain": "7dc000621e0046d1aada809e2b7177e64454645cf4c741e9daaf79c99ec2e7a2",
    "lake-manifest.json": "cf7757290ed1666c6c8242742931dc4bef3b2d6af42b99d4fe758b4de14947f7",
}

# Release archives, each matched on download (2026-10-01) to the publisher's checksum:
# PowerShell's GitHub release digest, nodejs.org SHASUMS256.txt, elan's GitHub release digest.
VENDOR = {
    "powershell-7.6.6-linux-x64.tar.gz": "ddbc4a2d113bbd46d283cfedcbcd117a70caefd7673f41f2b4e0000badf103bc",
    "node-v24.21.0-linux-x64.tar.gz": "6e1db87ef58b8819e5d5402eff1536491b18edd8eb7bee5ef7897876e88dc5ff",
    "elan-x86_64-unknown-linux-gnu.tar.gz": "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63",
}

# Mirrors of the companion's admission (uconn-hpc-work 0.1.7, _admit_remote_job_script).
NODE_LOCAL_TMP_ROOT = re.compile(
    r"""(^|[ \t\r\n=,:;|&(<>\x5b])(?:[\"']|\\)?/+tmp(?=$|[/ \t\r\n\"';|&)>,:\]])""")
NODE_LOCAL_TMP_PARAMETER_PATH = re.compile(
    r"""\$\{[A-Za-z_][A-Za-z0-9_]*(?::?[-+])(?:[\"']|\\)?/+tmp(?=$|[/}\"'])""")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> str:
    return subprocess.check_output(["git", "-c", "safe.directory=*", "-C", str(REPO), *args],
                                   text=True, encoding="utf-8")


def admission_precheck(script: bytes) -> None:
    if b"\r" in script:
        sys.exit("REFUSING: job script contains CR characters; it must be LF-only")
    text = script.decode("utf-8")
    active = "\n".join(l for l in text.splitlines() if l.strip() and not l.lstrip().startswith("#"))
    if re.search(r"BASH_SOURCE|dirname[^#]*\$0", active):
        sys.exit("REFUSING: job script derives paths from the Slurm spool copy")
    if "${SLURM_TMPDIR:-/tmp}" in active or re.search(r"\$\{SLURM_TMPDIR:\?", active):
        sys.exit("REFUSING: job script depends on SLURM_TMPDIR or its /tmp fallback")
    if NODE_LOCAL_TMP_ROOT.search(active) or NODE_LOCAL_TMP_PARAMETER_PATH.search(active):
        sys.exit("REFUSING: job script references unmanaged node-local /tmp")
    missing = [n for n in ("TMPDIR", "TEMP", "TMP")
               if not re.search(r"(?m)^[ \t]*export[ \t]+%s[ \t]*=" % n, active)]
    if missing:
        sys.exit("REFUSING: job script must export managed temporary storage; missing " + ", ".join(missing))
    bash = shutil.which("bash")
    if bash:
        r = subprocess.run([bash, "-n"], input=script, capture_output=True)
        if r.returncode != 0:
            sys.exit("REFUSING: bash -n failed: " + r.stderr.decode(errors="replace"))
    print("admission pre-check: PASS (LF-only, no spool paths, no node-local /tmp, all three exports"
          + (", bash -n" if bash else ", bash -n SKIPPED: no bash") + ")")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("run_id")
    ap.add_argument("--out", default=r"C:/Users/dsdqd/Work/WritingPreparation/hpc-pilot/runs/spcl-leanbuild",
                    help="authorized local staging root for the companion")
    ap.add_argument("--vendor", default=r"C:/Users/dsdqd/Work/WritingPreparation/hpc-pilot/vendor/spcl",
                    help="directory holding the pinned release archives")
    args = ap.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{2,80}", args.run_id):
        sys.exit("REFUSING: run id must be a plain token")

    script = SCRIPT.read_bytes()
    admission_precheck(script)

    # The map scan probe is generated from the formal supplement's table (LEANREPO M4).
    r = subprocess.run([sys.executable, str(REPO / "scripts" / "map_identifiers.py"), "--check"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("REFUSING: " + (r.stderr or r.stdout).strip())
    print(r.stdout.strip())

    dirty = git("status", "--porcelain", "--untracked-files=all", "--", *PROJECT_SPECS)
    if dirty.strip():
        sys.exit("REFUSING: packaged paths are not clean against HEAD; commit first:\n" + dirty)
    head = git("rev-parse", "HEAD").strip()
    branch = git("rev-parse", "--abbrev-ref", "HEAD").strip()
    print(f"source state: {branch} @ {head} (packaged paths clean)")

    members: dict[str, bytes] = {"build.sh": script, "hpc_gate_receipt.py": HELPER.read_bytes()}

    for name in PINS:
        got = sha((REPO / name).read_bytes())
        if got != PIN_BASELINE[name]:
            sys.exit(f"REFUSING: toolchain pin moved: {name}\n  expected {PIN_BASELINE[name]}\n"
                     f"  got      {got}\nThis is a Rule-17 event. Surface it and update PIN_BASELINE deliberately.")
    print("pins verified against the round-BD baseline")

    tracked = [p for p in git("ls-files", "-z", "--", *PROJECT_SPECS).split("\0") if p]
    n_lean = 0
    for rel in sorted(tracked):
        members["project/" + rel] = (REPO / rel).read_bytes()
        n_lean += rel.endswith(".lean") and rel.startswith("Sanctions")
    on_disk = {p.relative_to(REPO).as_posix() for p in (REPO / "Sanctions").rglob("*.lean")}
    if not on_disk <= set(tracked):
        sys.exit("REFUSING: untracked Lean sources: " + ", ".join(sorted(on_disk - set(tracked))))
    print(f"project files: {len(tracked)} tracked ({n_lean} Lean)")

    names = [l.strip() for l in SCAN_LIST.read_text(encoding="utf-8").splitlines()
             if l.strip() and not l.lstrip().startswith("#")]
    if not names or len(names) != len(set(names)):
        sys.exit("REFUSING: empty or duplicated round axiom-scan list")
    members["project/RoundScan.lean"] = ("import Sanctions\n"
                                         + "".join(f"#print axioms {n}\n" for n in names)).encode("utf-8")
    print(f"round axiom scan: {len(names)} declarations")

    vendor_dir = pathlib.Path(args.vendor)
    lines = []
    for name, want in sorted(VENDOR.items()):
        data = (vendor_dir / name).read_bytes()
        if sha(data) != want:
            sys.exit(f"REFUSING: vendored archive digest mismatch: {name}")
        members["vendor/" + name] = data
        lines.append(f"{want}  {name}\n")
    members["vendor/VENDOR.sha256"] = "".join(lines).encode("utf-8")
    print("vendored archives verified:", ", ".join(sorted(VENDOR)))

    members["SOURCE_STATE.json"] = (json.dumps(
        {"commit": head, "branch": branch, "packaged_paths_clean": True,
         "project_specs": list(PROJECT_SPECS)}, indent=2) + "\n").encode("utf-8")

    rows = ["path,bytes,sha256"] + [f"{rel},{len(d)},{sha(d)}" for rel, d in sorted(members.items())]
    manifest = ("\n".join(rows) + "\n").encode("utf-8")
    members["PACKAGE_MANIFEST.csv"] = manifest

    out_dir = pathlib.Path(args.out) / args.run_id
    out_dir.mkdir(parents=True, exist_ok=False)
    out_zip = out_dir / "leanbuild.zip"
    with zipfile.ZipFile(out_zip, "w") as z:
        for rel in sorted(members):
            info = zipfile.ZipInfo("leanbuild/" + rel, date_time=(2026, 1, 1, 0, 0, 0))
            info.external_attr = 0o644 << 16
            info.compress_type = zipfile.ZIP_STORED if rel.startswith("vendor/") else zipfile.ZIP_DEFLATED
            z.writestr(info, members[rel])

    m = re.search(rb"(?m)^#SBATCH --time=(\d+):", script)
    if not m:
        sys.exit("REFUSING: job script has no parseable #SBATCH --time")
    hours = int(m.group(1))
    partition = "lo-core" if hours > 12 else "general"

    activation = {
        "stagedPackage": out_zip.name,
        "packageRoot": "leanbuild",
        "packageManifest": "PACKAGE_MANIFEST.csv",
        "packageManifestSha256": sha(manifest),
        "jobScript": "leanbuild/build.sh",
        "jobScriptSha256": sha(members["build.sh"]),
        "runId": args.run_id,
        "remoteRunDir": "/home/xig16106/" + args.run_id,
        "sourceCommit": head,
        "partition": partition, "account": "tab13007", "qos": "general",
    }
    with zipfile.ZipFile(out_zip) as archive:
        assert sha(archive.read("leanbuild/PACKAGE_MANIFEST.csv")) == activation["packageManifestSha256"]
        assert sha(archive.read(activation["jobScript"])) == activation["jobScriptSha256"]
    (out_dir / "activation_args.json").write_text(json.dumps(activation, indent=2) + "\n", encoding="utf-8")
    blob = out_zip.read_bytes()
    print("activation path pre-check: PASS (ZIP basename, package-relative manifest, archive-relative script)")
    print()
    print("run id                 :", args.run_id)
    print("package                :", out_zip)
    print("members                :", len(members))
    print("zip bytes              :", len(blob))
    print("zip sha256             :", sha(blob))
    print("build.sh sha256        :", activation["jobScriptSha256"])
    print("PACKAGE_MANIFEST sha256:", activation["packageManifestSha256"])
    print(f"SUBMIT WITH partition = {partition}  account = tab13007  qos = general  (script requests {hours} h)")


if __name__ == "__main__":
    main()
