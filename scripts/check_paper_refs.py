#!/usr/bin/env python3
"""Label and hard-coded-number sweep over the paper sources (round S, 2026-09-15;
doc 87 S5; the reader's Q1-5).

Checks, over every .tex file under paper/ (roots, section directories,
fragments), comments stripped by the backslash-parity rule of
`texcomments.py` (round W, 2026-09-17: `\\%` is a doubled backslash followed
by a comment, `\%` an escaped percent), and a reference separator that
accepts `~` as well as whitespace:

  1. duplicate `\\label{...}` keys across all files — FAIL;
  2. hard-coded cross-reference numbers in prose — `Theorem 3`, `Proposition
     2`, `Lemma 1`, `Corollary 4`, `Section 5`, `Appendix D`, `Assumption 2`,
     `Table 1`, `Figure 2` written as literal numbers instead of `\\Cref` —
     reported with file:line; each hit is a review candidate (a literal number
     in a quotation or a Lean name is legitimate), so hits do not fail the
     check unless `--strict` is passed.

Run from the repository root: python scripts/check_paper_refs.py [--strict]
"""
from __future__ import annotations
import re, pathlib, sys, collections
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from texcomments import strip_comment   # backslash-parity stripper (round W)

sys.stdout.reconfigure(encoding="utf-8")
ROOT = pathlib.Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
STRICT = "--strict" in sys.argv

LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
from check_paper_refs_re import HARD_RE   # `Theorem~3` too (round W); shared with the self-test

def stripped_lines(p: pathlib.Path):
    for i, line in enumerate(p.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        yield i, strip_comment(line)

files = sorted(PAPER.rglob("*.tex"))
labels: dict[str, list[str]] = collections.defaultdict(list)
hard: list[str] = []
for p in files:
    rel = p.relative_to(ROOT).as_posix()
    for i, code in stripped_lines(p):
        for m in LABEL_RE.finditer(code):
            labels[m.group(1)].append(f"{rel}:{i}")
        # skip lines that are Lean paths / verbatim identifiers
        for m in HARD_RE.finditer(code):
            hard.append(f"{rel}:{i}: {m.group(0)!r}")

dups = {k: v for k, v in labels.items() if len(v) > 1}
print(f"files scanned: {len(files)}; labels: {len(labels)}; duplicate labels: {len(dups)}")
for k, v in sorted(dups.items()):
    print(f"  DUPLICATE label {k}: " + ", ".join(v))
print(f"hard-coded reference numbers in prose: {len(hard)}")
for h in hard:
    print("  " + h)
fail = bool(dups) or (STRICT and bool(hard))
print("RESULT:", "FAIL" if fail else "OK")
sys.exit(1 if fail else 0)
