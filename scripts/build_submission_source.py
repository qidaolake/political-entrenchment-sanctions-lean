#!/usr/bin/env python3
"""Build the single-file LaTeX source of the manuscript for the journal's submission system (2026-10-21, N195).

The Journal of Economic Theory compiles the uploaded LaTeX itself ("A PDF is not an acceptable source file"), and
Elsevier's systems do not process subfolders. The split build resolves the manuscript's references into the Online
Appendix and the formal supplement through `xr-hyper`, which reads those documents' `.aux` files; the submission
system has neither. This script writes one self-contained `.tex` file:

  * the shared preamble and every `main_sections/` file inlined in place of their `\\input`;
  * comments stripped by the backslash-parity rule of `texcomments.py` (a comment-only line is dropped; a trailing
    comment keeps its `%`, so line-end spacing is unchanged);
  * the combined-build block dropped;
  * the `\\newlabel` lines of `sanctions_jet_appendix.aux` and `sanctions_formal_supplement.aux` embedded in
    `filecontents*` blocks before `\\documentclass`, so `\\externaldocument` finds them on the first run;
  * the bibliography inlined from `sanctions_jet_draft.bbl` (no BibTeX run needed).

Run after `scripts/Build-Paper.ps1` (the `.aux` and `.bbl` files must be current), from the repository root:

    python scripts/build_submission_source.py OUTDIR

It writes OUTDIR/sanctions_jet_manuscript.tex. Compile it with pdflatex three times in an empty folder; the
result should match paper/sanctions_jet_draft.pdf page for page.
"""
from __future__ import annotations

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from texcomments import strip_comment  # noqa: E402

PAPER = 'paper'
ROOT = 'sanctions_jet_draft.tex'
EXTERNAL = ('sanctions_jet_appendix', 'sanctions_formal_supplement')


def read(path: str) -> str:
    with open(path, encoding='utf-8-sig') as f:
        return f.read().replace('\r\n', '\n')


def strip(text: str) -> str:
    out = []
    for line in text.split('\n'):
        code = strip_comment(line)
        if code == line:
            out.append(line)
        elif code.strip() == '':
            continue                      # a comment-only line contributes nothing to TeX
        else:
            out.append(code + '%')       # keep the % so the line end is not turned into a space
    return '\n'.join(out)


def inline(text: str) -> str:
    def rep(m: re.Match) -> str:
        name = m.group(1)
        path = os.path.join(PAPER, name if name.endswith('.tex') else name + '.tex')
        return inline(strip(read(path))).rstrip('\n')
    return re.sub(r'^[ \t]*\\input\{([^}]+)\}[ \t]*$', rep, text, flags=re.M)


def labels(stem: str) -> str:
    aux = read(os.path.join(PAPER, stem + '.aux'))
    lines = [l for l in aux.split('\n') if l.startswith('\\newlabel{')]
    if not lines:
        sys.exit(f'no labels in {stem}.aux: run scripts/Build-Paper.ps1 first')
    return '\\begin{filecontents*}{%s.aux}\n\\relax\n%s\n\\end{filecontents*}\n' % (stem, '\n'.join(lines))


def main() -> None:
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    out_dir = sys.argv[1]
    t = strip(read(os.path.join(PAPER, ROOT)))
    t = re.sub(r'\\ifdefined\\COMBINEDAPPENDIX\s*\\input\{sanctions_appendix_body\}\s*\\fi\n?', '', t)
    t = re.sub(r'\\ifdefined\\COMBINEDAPPENDIX\\else\s*(\\externaldocument\[\]\[nocite\]\{sanctions_jet_appendix\})\s*\\fi',
               r'\1', t)
    if 'COMBINEDAPPENDIX' in t:
        sys.exit('combined-build guard not recognized in the root; update this script')
    t = inline(t)
    bbl = read(os.path.join(PAPER, ROOT.replace('.tex', '.bbl'))).rstrip('\n')
    t, n = re.subn(r'\\bibliographystyle\{[^}]*\}\s*\\bibliography\{[^}]*\}', lambda _m: bbl, t)
    if n != 1:
        sys.exit('bibliography commands not found once in the root')
    for stem in EXTERNAL:
        if '\\externaldocument[][nocite]{%s}' % stem not in t:
            sys.exit(f'\\externaldocument for {stem} not found')
    head = ('% Single-file submission source of "Political Entrenchment and the Persistence of Economic Sanctions",\n'
            '% built by scripts/build_submission_source.py. Compile with pdflatex (three runs); no BibTeX run is needed.\n'
            '% The label files of the Online Appendix and the formal supplement are embedded below, so that\n'
            '% references into those supplementary documents resolve.\n')
    t = head + ''.join(labels(s) for s in EXTERNAL) + re.sub(r'\n{3,}', '\n\n', t).lstrip('\n')
    if re.search(r'\\input\{|\\include\{', t):
        sys.exit('an \\input or \\include is left')
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, 'sanctions_jet_manuscript.tex')
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        f.write(t.rstrip('\n') + '\n')
    print('wrote', path, f'({len(t):,} characters)')


if __name__ == '__main__':
    main()
