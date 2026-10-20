#!/usr/bin/env python3
"""Symbol-use counts over the manuscript and the appendix (doc 83 Q1.1; doc 85
§2.3). Counts occurrences of a curated symbol list in the TeX inputs of the
manuscript (main_sections + main_fragments, as the draft root inputs them) and
of the appendix (the files sanctions_appendix_body.tex inputs), separately,
with comments stripped by the backslash-parity rule of `texcomments.py`
(round W, 2026-09-17; the input walk is now recursive and fails on a missing
file). Single-letter symbols
are counted inside math only ($…$, \(…\), \[…\], align/equation/gather/multline
environments); macro-spelled symbols everywhere. Round S (2026-09-15) added the
inline delimiter and the escaped-percent handling (doc 87 S1, the reader's S5).
Writes docs/SYMBOL-COUNTS.md. A count is a search hit, not a judgement: the
notes column flags letters that also serve other roles.

Run from the repository root: python scripts/symbol_counts.py
"""
from __future__ import annotations
import re, pathlib, datetime, subprocess, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from texcomments import strip_comment, strip_comments   # backslash-parity stripper (round W)

ROOT = pathlib.Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"

def _inputs_rec(tex: pathlib.Path, out: list[pathlib.Path], only_prefix: str | None) -> None:
    for line in tex.read_text(encoding="utf-8", errors="replace").splitlines():
        s = strip_comment(line)
        for m in re.finditer(r"\\input\{([^}]+)\}", s):
            rel = m.group(1)
            if only_prefix and not rel.startswith(only_prefix):
                continue
            p = PAPER / (rel if rel.endswith(".tex") else rel + ".tex")
            if not p.exists():
                raise FileNotFoundError(f"{tex.name} inputs {rel}, which does not exist")   # fail closed (round W)
            if p not in out:
                out.append(p)
                _inputs_rec(p, out, None)   # recursive: fragments of fragments are counted too (round W)

def inputs_of(root_tex: pathlib.Path, only_prefix: str | None = None) -> list[pathlib.Path]:
    """Every .tex file the root inputs, recursively; a missing input is an error."""
    out: list[pathlib.Path] = []
    _inputs_rec(root_tex, out, only_prefix)
    return out

MATH_RE = re.compile(r"\$\$.*?\$\$|\$.*?\$|\\\[.*?\\\]|\\\(.*?\\\)|\\begin\{(align\*?|equation\*?|gather\*?|multline\*?)\}.*?\\end\{\1\}", re.S)

def math_segments(text: str) -> str:
    return "\n".join(m.group(0) for m in MATH_RE.finditer(text))

# (display, regex, math_only, note)
SYMBOLS = [
    ("K_S", r"K_S(?![A-Za-z])", False, ""),
    ("g_S", r"g_S(?![A-Za-z])", False, ""),
    ("M_S", r"M_S(?![A-Za-z])", False, ""),
    ("g_T", r"g_T(?![A-Za-z])", False, ""),
    ("M_T", r"M_T(?![A-Za-z])", False, ""),
    ("mu", r"\\mu(?![A-Za-z])", True, "also the four-group opposition slope"),
    ("varrho", r"\\varrho", False, ""),
    ("sigma_img", r"\\sigma_\{\\mathrm\{img\}\}", False, ""),
    ("sigma_V", r"\\sigma_V(?![A-Za-z])", False, ""),
    ("sigma_C", r"\\sigma_C(?![A-Za-z])", False, ""),
    ("bar sigma", r"\\bar\\sigma|\\bar\{\\sigma\}", False, ""),
    ("L_resp", r"L_\{\\mathrm\{resp\}\}", False, ""),
    ("L_loop", r"L_\{\\mathrm\{loop\}\}", False, ""),
    ("M_tot", r"M_\{\\mathrm\{tot\}\}", False, ""),
    ("A", r"(?<![A-Za-z\\_^{])A(?![A-Za-z_])", True, "appetite bound; also matrix/section letters in math"),
    ("q", r"(?<![A-Za-z\\_^{])q(?![A-Za-z_])", True, "sanction-cost curvature; also q_K"),
    ("u_0", r"u_0(?![A-Za-z0-9])", False, ""),
    ("k", r"(?<![A-Za-z\\_^{])k(?![A-Za-z_])", True, "placation rate; also indices"),
    ("r", r"(?<![A-Za-z\\_^{])r(?![A-Za-z_])", True, "rally slope; also other roles"),
    ("w", r"(?<![A-Za-z\\_^{])w(?![A-Za-z_])", True, "Sender state valuation; also welfare weights"),
    ("ell", r"\\ell(?![A-Za-z])", True, "compliance cost"),
    ("c", r"(?<![A-Za-z\\_^{])c(?![A-Za-z_])", True, "Target sanction pain; also constants"),
    ("n", r"(?<![A-Za-z\\_^{])n(?![A-Za-z_])", True, "rally softening; also indices"),
    ("v", r"(?<![A-Za-z\\_^{])v(?![A-Za-z_])", True, "Target state valuation"),
    ("g_lo", r"g_\{\\mathrm\{lo\}\}", False, ""),
    ("g_hi", r"g_\{\\mathrm\{hi\}\}", False, ""),
    ("d_lo", r"d_\{\\mathrm\{lo\}\}", False, ""),
    ("d_hi", r"d_\{\\mathrm\{hi\}\}", False, ""),
    ("M_x", r"M_x(?![A-Za-z])", False, ""),
    ("M_m", r"M_m(?![A-Za-z])", False, ""),
    ("M_s", r"M_s(?![A-Za-z])", False, ""),
    ("M_cx", r"M_\{\\mathrm\{cx\}\}", False, ""),
    ("M_mix", r"M_\{\\mathrm\{mix\}\}", False, ""),
    ("M_cs", r"M_\{\\mathrm\{cs\}\}", False, ""),
    ("(RM)", r"\(RM\)|\\eqref\{eq:rally-margin\}", False, "label"),
    ("(RL)", r"\(RL\)", False, "label"),
    ("(T6)", r"\(T6\)", False, "label"),
    ("00/01/10/11", r"\^\{?(00|01|10|11)\}?", False, "regime superscripts"),
    ("Q (discriminant)", r"(?<![A-Za-z\\_^{])Q(?![A-Za-z_])", True, "also other Q's"),
    ("D (discriminant)", r"(?<![A-Za-z\\_^{])D(?![A-Za-z_])", True, "also the carrier class D"),
    ("L (discriminant)", r"(?<![A-Za-z\\_^{])L(?![A-Za-z_])", True, "also Lipschitz L_·"),
    ("N (discriminant)", r"(?<![A-Za-z\\_^{])N(?![A-Za-z_])", True, "also horizons"),
    ("K_T", r"K_T(?![A-Za-z])", False, ""),
    ("gamma_T", r"\\gamma_T(?![A-Za-z])", False, ""),
    ("m_S", r"m_S(?![A-Za-z])", False, ""),
    ("c_sigma", r"c_\\sigma", False, ""),
    ("x_F, x_L", r"x_F(?![A-Za-z])|x_L(?![A-Za-z])", False, ""),
    ("sigma_real", r"\\sigma_\{\\mathrm\{real\}\}", False, ""),
    ("P_3, h", r"P_3(?![0-9])", False, "witness label"),
]

def count(files, regex, math_only):
    total, first = 0, ""
    for f in files:
        txt = strip_comments(f.read_text(encoding="utf-8", errors="replace"))
        hay = math_segments(txt) if math_only else txt
        n = len(re.findall(regex, hay))
        if n and not first:
            first = f.name
        total += n
    return total, first

def main():
    main_files = inputs_of(PAPER / "sanctions_jet_draft.tex", only_prefix="main_sections")
    app_files = inputs_of(PAPER / "sanctions_appendix_body.tex", only_prefix="appendix_sections")
    head = subprocess.run(["git", "rev-parse", "--short", "HEAD"], capture_output=True, text=True, cwd=ROOT).stdout.strip()
    rows = []
    for disp, rx, mo, note in SYMBOLS:
        m, fm = count(main_files, rx, mo)
        a, fa = count(app_files, rx, mo)
        rows.append((disp, m, a, fm, fa, note))
    out = [
        "# Symbol-use counts (doc 83 Q1.1; doc 85 §2.3)", "",
        f"Generated {datetime.date.today().isoformat()} by `scripts/symbol_counts.py` at `{head}`. "
        "Manuscript = the files `sanctions_jet_draft.tex` inputs under `main_sections/` and their fragments "
        f"({len(main_files)} files); appendix = the files `sanctions_appendix_body.tex` inputs ({len(app_files)} files). "
        "Comments stripped (only an unescaped `%` starts one). Single-letter symbols are counted in math mode only "
        "(`$…$`, inline `\\(…\\)`, `\\[…\\]`, align/equation/gather/multline) and the notes say where the letter also "
        "serves another role, so a single-letter count can exceed the symbol's uses; before round S (2026-09-15) inline "
        "math was not scanned and an escaped `\\%` split a line, so counts could also fall short (the reader's S5). "
        "A count is a search hit, not a judgement; the trims of round R use the rule of doc 85 §4.2.", "",
        "| symbol | main | appendix | first main file | first appendix file | note |", "|---|---:|---:|---|---|---|",
    ]
    for disp, m, a, fm, fa, note in rows:
        out.append(f"| `{disp}` | {m} | {a} | {fm} | {fa} | {note} |")
    out += ["", "## Used at most twice in the main text", ""]
    few = [r for r in rows if r[1] <= 2 and not r[5].startswith("also") and "label" not in r[5]]
    for disp, m, a, fm, fa, note in few:
        out.append(f"- `{disp}`: main {m}, appendix {a}")
    (ROOT / "docs" / "SYMBOL-COUNTS.md").write_text("\n".join(out) + "\n", encoding="utf-8")
    print(f"OK: {len(rows)} symbols over {len(main_files)} main and {len(app_files)} appendix files -> docs/SYMBOL-COUNTS.md")

if __name__ == "__main__":
    main()
