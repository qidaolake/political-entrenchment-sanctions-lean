"""The hard-coded-reference regex of check_paper_refs.py, importable without
running the sweep (round W, 2026-09-17)."""
import re
HARD_RE = re.compile(
    r"\b(Theorem|Proposition|Lemma|Corollary|Section|Subsection|Assumption|Definition|Remark|Table|Figure|Appendix|Appendices)"
    r"(?:~|\s+)([0-9]+(\.[0-9]+)*|[A-G](\.[0-9]+)*)\b(?![A-Za-z_])")
