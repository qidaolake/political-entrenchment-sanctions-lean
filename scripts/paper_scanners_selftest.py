#!/usr/bin/env python3
"""Regression fixtures for the paper scanners (round W, 2026-09-17).

The two "expected defect" fixtures are the outside reader's, from
`suggestions/2026-09-16-rounds-sv-jet-readiness/validation_checks.py`
(S–V audit, Q1 §9): `Theorem~3` was missed by the reference regex, and a
percent after a doubled backslash was treated as escaped. Both now pass in
the positive direction. Exit 1 on any failure.

Run from the repository root: python scripts/paper_scanners_selftest.py
"""
from __future__ import annotations
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from texcomments import strip_comment
from check_paper_refs_re import HARD_RE

CASES = [
    ("reference plain space (control)",      lambda: HARD_RE.search("Theorem 3") is not None),
    ("reference tilde (reader's fixture)",   lambda: HARD_RE.search("Theorem~3") is not None),
    ("reference Cref not a hit",             lambda: HARD_RE.search(r"\Cref{thm:persistence}") is None),
    ("reference letter appendix",            lambda: HARD_RE.search("Appendix~D.2") is not None),
    ("comment escaped percent kept (control)", lambda: strip_comment(r"x \% y") == r"x \% y"),
    ("comment after doubled backslash dropped (reader's fixture)",
                                             lambda: strip_comment(r"x \\% comment") == r"x \\"),
    ("comment plain",                        lambda: strip_comment("a % b") == "a "),
    ("comment none",                         lambda: strip_comment("no comment here") == "no comment here"),
    ("comment escaped backslash then percent", lambda: strip_comment(r"\\\\% c") == r"\\\\"),
]
bad = 0
for name, fn in CASES:
    ok = bool(fn())
    print(("PASS " if ok else "FAIL ") + name)
    bad += (not ok)
print("RESULT:", "FAIL" if bad else "OK", f"({len(CASES) - bad}/{len(CASES)})")
sys.exit(1 if bad else 0)
