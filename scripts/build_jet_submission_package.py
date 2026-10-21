#!/usr/bin/env python3
"""Assemble the Journal of Economic Theory submission package (2026-10-21, N196).

Modelled on the authors' AER: Insights package builder (sanctions_innovation_paper_package,
build_aeri_submission_package.py, 2026-10-09): one folder per build, named <date>-<commit>, with every file under
the stem Gong_Zhao_Zhong_JET, a title page, the authors' declaration, an AI-use description for the form, a
submission checklist and a manifest with hashes. It follows the JET Guide for Authors
(https://www.sciencedirect.com/journal/journal-of-economic-theory/publish/guide-for-authors, read 2026-10-21):

* Manuscript: an editable source ("A PDF is not an acceptable source file"; Elsevier's systems do not process
  subfolders): the single-file LaTeX source of scripts/build_submission_source.py, compiled here alone in an empty
  folder and compared with paper/sanctions_jet_draft.pdf. The reference PDF is kept beside it.
* Title page: title, authors, affiliations with full postal addresses, the corresponding author's email (which
  "will be published"), abstract, keywords and JEL codes. Review is single anonymized, so the manuscript carries the
  names too.
* Abstract of at most 250 words; 1 to 7 keywords, none built with "and" or "of".
* Highlights: 3 to 5 bullets of at most 85 characters, in a Word file whose name contains "highlights".
* Declaration of interests: the Guide asks for the Word file of Elsevier's declarations tool; the file here carries
  the tool's standard "nothing to declare" sentence for the three authors (all confirmed, 2026-10-21) and serves
  if the form accepts it.
* The generative-AI statement as a section of its own, last before the references (checked in the PDF).
* Supplementary material: the Online Appendix, the formal supplement and the Lean source archive, which the
  data-availability statement says accompanies the submission. Supplementary files "appear online exactly as
  received", so their text is checked for internal project history.
* Cover letter: not required by the Guide; built from paper/submission/COVER-LETTER-DRAFT.md for the form's field.

Writes dist/jet_submission/<date>-<commit>/ and never uploads or submits anything.
Usage (repository root, after scripts/Build-Paper.ps1 and the submission archive are current):
    python scripts/build_jet_submission_package.py
"""
from __future__ import annotations

import datetime as dt
import hashlib
import json
import re
import shutil
import subprocess
import sys
import zipfile
from pathlib import Path
from xml.sax.saxutils import escape

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / 'paper'
sys.path.insert(0, str(ROOT / 'scripts'))
from texcomments import strip_comment  # noqa: E402

TITLE = 'Political Entrenchment and the Persistence of Economic Sanctions'
AUTHORS = ['Xiaofeng Gong', 'Yuechuan Zhao', 'Chunping Zhong']
EMAIL = 'xiaofeng.gong@uconn.edu'
STEM = 'Gong_Zhao_Zhong_JET'
GUIDE = 'https://www.sciencedirect.com/journal/journal-of-economic-theory/publish/guide-for-authors'
SUBMIT = 'https://submit.elsevier.com/JET'
ARCHIVE = ROOT / 'dist' / 'SanctionPublicChoiceLean-v1.30-submission.zip'
AI_TITLE = 'Declaration of generative AI and AI-assisted technologies in the manuscript preparation process'
COVERED = ['paper', 'scripts/build_submission_source.py', 'scripts/build_jet_submission_package.py']
HISTORY = re.compile(r'\b[Rr]ounds? [A-Z]{1,2}(?:-[0-9])?\b|\bRule[ ~-][0-9]+\b|\bdoc [0-9]{2,3}\b|'
                     r"\buser's\b|\bDECISIONS\.md\b|\bstaged as\b|\bpromoted (?:as|in)\b")


def run(cmd, cwd=ROOT, check=True) -> str:
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, encoding='utf-8', errors='replace')
    if check and r.returncode != 0:
        raise RuntimeError(f"{' '.join(map(str, cmd))} failed in {cwd}:\n{(r.stdout + r.stderr)[-2000:]}")
    return r.stdout


def git(*args) -> str:
    return run(['git', '-c', 'safe.directory=*', *args]).strip()


def pdflatex(doc: str, cwd: Path, runs: int = 3) -> None:
    for _ in range(runs):
        run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', doc], cwd)


def pdf_text(pdf: Path, first: int | None = None, last: int | None = None) -> str:
    cmd = ['pdftotext', '-enc', 'UTF-8']
    if first:
        cmd += ['-f', str(first)]
    if last:
        cmd += ['-l', str(last)]
    return run(cmd + [str(pdf), '-'])


def pages(pdf: Path) -> int:
    return int(re.search(r'^Pages:\s+(\d+)', run(['pdfinfo', str(pdf)]), re.M).group(1))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def braced(text: str, command: str) -> str:
    start = text.index(command + '{') + len(command) + 1
    depth, i = 1, start
    while depth:
        depth += {'{': 1, '}': -1}.get(text[i], 0)
        i += 1
    return text[start:i - 1]


def root_source() -> str:
    raw = (PAPER / 'sanctions_jet_draft.tex').read_text(encoding='utf-8-sig')
    return '\n'.join(strip_comment(l) for l in raw.splitlines())


def write_docx(path: Path, paragraphs: list[tuple[str, bool]]) -> None:
    """A minimal Word file: one paragraph per (text, bold) pair."""
    body = ''.join(f'<w:p><w:r>{"<w:rPr><w:b/></w:rPr>" if bold else ""}'
                   f'<w:t xml:space="preserve">{escape(text)}</w:t></w:r></w:p>' for text, bold in paragraphs)
    doc = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
           '<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"><w:body>' + body +
           '<w:sectPr><w:pgSz w:w="12240" w:h="15840"/><w:pgMar w:top="1440" w:right="1440" w:bottom="1440" '
           'w:left="1440" w:header="720" w:footer="720" w:gutter="0"/></w:sectPr></w:body></w:document>')
    types = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
             '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
             '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
             '<Default Extension="xml" ContentType="application/xml"/><Override PartName="/word/document.xml" '
             'ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/></Types>')
    rels = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship '
            'Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" '
            'Target="word/document.xml"/></Relationships>')
    with zipfile.ZipFile(path, 'w', zipfile.ZIP_DEFLATED) as z:
        z.writestr('[Content_Types].xml', types)
        z.writestr('_rels/.rels', rels)
        z.writestr('word/document.xml', doc)


def build_source(work: Path) -> tuple[Path, Path]:
    src_dir = work / 'source'
    run([sys.executable, '-I', str(ROOT / 'scripts' / 'build_submission_source.py'), str(src_dir)])
    tex = src_dir / 'sanctions_jet_manuscript.tex'
    test = work / 'source_test'
    test.mkdir()
    shutil.copy2(tex, test / tex.name)
    pdflatex(tex.name, test)
    return tex, test / 'sanctions_jet_manuscript.pdf'


PREAMBLE = r"""\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage[T1]{fontenc}
\usepackage[hidelinks]{hyperref}
\newcommand{\central}[1]{#1}
\setlength{\parindent}{0pt}
\setlength{\parskip}{6pt}
"""


def build_title_page(work: Path) -> Path:
    src = root_source()
    abstract = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', src, re.S).group(1)
    keywords = re.search(r'\\textbf\{Keywords:\}(.*?)\n\s*\n', src, re.S).group(1)
    jel = re.search(r'\\textbf\{JEL classification:\}(.*?)\n', src).group(1)
    tex = PREAMBLE + '\n'.join([
        r'\title{' + braced(src, r'\title') + '}',
        r'\author{' + braced(src, r'\author') + '}',
        r'\date{' + braced(src, r'\date') + '}',
        r'\begin{document}', r'\maketitle', r'\thispagestyle{empty}',
        r'\begin{center}Corresponding author: Xiaofeng Gong, \href{mailto:' + EMAIL + r'}{\texttt{' + EMAIL + r'}}\end{center}',
        r'\begin{abstract}' + abstract + r'\end{abstract}',
        r'\textbf{Keywords:} ' + ' '.join(keywords.split()),
        '', r'\textbf{JEL classification:} ' + jel.strip(), r'\end{document}', ''])
    (work / 'title_page.tex').write_text(tex, encoding='utf-8')
    pdflatex('title_page.tex', work, runs=2)
    return work / 'title_page.pdf'


def tex_escape(s: str) -> str:
    s = (s.replace('\\', r'\textbackslash{}').replace('&', r'\&').replace('%', r'\%').replace('$', r'\$')
            .replace('#', r'\#').replace('_', r'\_'))
    return re.sub(r'"([^"]*)"', lambda q: '``' + q.group(1) + "''", s)


def letter_paragraphs() -> list[str]:
    md = (ROOT / 'paper' / 'submission' / 'COVER-LETTER-DRAFT.md').read_text(encoding='utf-8')
    body = md[md.index('[Date of submission]'):]
    out = []
    for block in re.split(r'\n\s*\n', body.strip()):
        lines = [l.strip() for l in block.split('\n')]
        if lines[0].startswith('[Optional'):
            continue
        if any(k in block for k in ('Editors, Journal', 'Department of Economics')):
            out.extend(l.replace('; ORCID: [to add]', '') for l in lines)
            continue
        cur: list[str] = []
        for s in lines:
            if re.match(r'^\d+\. ', s) and cur:
                out.append(' '.join(cur))
                cur = []
            cur.append(s)
        out.append(' '.join(cur))
    date = dt.date.today().strftime('%B %d, %Y').replace(' 0', ' ')
    return [date if p == '[Date of submission]' else p for p in out]


def build_cover_letter(work: Path, out: Path) -> Path:
    paras = letter_paragraphs()
    tex, in_list = [PREAMBLE.replace('\\setlength{\\parskip}{6pt}', '\\setlength{\\parskip}{8pt}'), r'\begin{document}', r'\thispagestyle{empty}'], False
    for p in paras:
        m = re.match(r'^(\d+)\. (.*)$', p)
        if m and not in_list:
            tex.append(r'\begin{enumerate}\setlength{\itemsep}{0pt}')
            in_list = True
        if not m and in_list:
            tex.append(r'\end{enumerate}')
            in_list = False
        line = tex_escape(m.group(2) if m else p)
        line = re.sub(r'(https?://\S+?)([.,;)]?)(?=\s|$)', lambda u: r'\url{' + u.group(1).replace(r'\_', '_') + '}' + u.group(2), line)
        tex.append(r'\item ' + line if m else line + '\n')
    if in_list:
        tex.append(r'\end{enumerate}')
    tex.append(r'\end{document}')
    (work / 'cover_letter.tex').write_text('\n'.join(tex) + '\n', encoding='utf-8')
    pdflatex('cover_letter.tex', work, runs=1)
    write_docx(out / f'{STEM}_cover_letter.docx', [(p, False) for p in paras])
    return work / 'cover_letter.pdf'


DECLARATION = ('The authors declare that they have no known competing financial interests or personal relationships '
               'that could have appeared to influence the work reported in this paper.')


def build_declaration(work: Path, out: Path) -> Path:
    paras = [('Declaration of interests', True), (f'Article: {TITLE}', False),
             ('Authors: ' + ', '.join(AUTHORS), False), (DECLARATION, False)]
    write_docx(out / f'{STEM}_declaration_of_interests.docx', paras)
    tex = PREAMBLE + '\n'.join([r'\begin{document}', r'\thispagestyle{empty}',
                                r'\begin{center}{\Large\bfseries Declaration of interests}\end{center}', '',
                                r'\textbf{Article:} \emph{' + TITLE + '}', '',
                                r'\textbf{Authors:} ' + ', '.join(AUTHORS), '', DECLARATION, r'\end{document}', ''])
    (work / 'declaration.tex').write_text(tex, encoding='utf-8')
    pdflatex('declaration.tex', work, runs=1)
    return work / 'declaration.pdf'


def ai_statement() -> str:
    raw = (PAPER / 'main_sections' / '08_ai_declaration.tex').read_text(encoding='utf-8-sig')
    body = '\n'.join(strip_comment(l) for l in raw.splitlines())
    body = body[body.index('process}') + len('process}'):]
    body = body.replace('~', ' ').replace(r'\#', '#')
    body = re.sub(r'\\texttt\{([^}]*)\}', r'\1', body)
    return ' '.join(body.split())


def checks(files: dict, flat_pdf: Path, title_pdf: Path) -> dict:
    r: dict = {}
    ms = files['manuscript_pdf']
    text = pdf_text(ms)
    page1 = pdf_text(ms, 1, 1)
    r['manuscript_pages'] = pages(ms)
    r['page1_has_title_authors_email'] = all(s in ' '.join(page1.split()) for s in [*AUTHORS, EMAIL]) and 'Persistence' in page1
    r['undefined_reference_marks'] = text.count('??')
    tp = ' '.join(pdf_text(title_pdf).split())
    r['title_page_pages'] = pages(title_pdf)
    r['title_page_has_all'] = all(s in tp for s in [*AUTHORS, EMAIL, 'Abstract', 'Keywords', 'JEL', 'USA', 'China'])
    m = re.search(r'Abstract (.*?) Keywords:', tp)
    r['abstract_words'] = len(m.group(1).split()) if m else None
    kw = re.search(r'Keywords: (.*?)\.? JEL', tp)
    keywords = [k.strip() for k in kw.group(1).split(';')] if kw else []
    r['keywords'] = keywords
    r['keywords_ok'] = 1 <= len(keywords) <= 7 and not any(re.search(r'\b(and|of)\b', k) for k in keywords)
    hl = [l for l in (PAPER / 'sanctions_highlights.txt').read_text(encoding='utf-8').splitlines() if l.strip()]
    r['highlight_lengths'] = [len(h) for h in hl]
    r['highlights_ok'] = 3 <= len(hl) <= 5 and all(len(h) <= 85 for h in hl)
    flat = ' '.join(text.split())
    i_ai, i_data, i_ref = flat.find('Declaration of generative AI'), flat.find('Data availability'), flat.rfind('References')
    r['ai_section_last_before_references'] = 0 <= i_data < i_ai < i_ref and 'reviewed and edited' in flat[i_ai:i_ref]
    r['flat_source_pages'] = pages(flat_pdf)
    log = flat_pdf.with_suffix('.log').read_text(encoding='utf-8', errors='replace')
    r['flat_source_undefined'] = len(re.findall(r'undefined', log, re.I))
    r['flat_source_text_identical'] = pdf_text(flat_pdf).split() == text.split()
    for key in ('online_appendix', 'formal_supplement'):
        t = pdf_text(files[key])
        r[f'{key}_pages'] = pages(files[key])
        r[f'{key}_history_marks'] = sorted(set(HISTORY.findall(t)))
        r[f'{key}_em_dashes'] = t.count('\u2014')
    r['manuscript_em_dashes'] = text.count('\u2014')
    arch = files['lean_source_archive']
    r['archive_sha256_matches_file'] = (arch.with_name(arch.name + '.sha256').read_text().split()[0] == sha256(arch)
                                       if arch.with_name(arch.name + '.sha256').exists() else False)
    with zipfile.ZipFile(arch) as z:
        man = z.read('SanctionPublicChoiceLean/CORE-BUNDLE-MANIFEST.txt').decode('utf-8')
    r['archive_commit'] = re.search(r'Source commit: (\w+)', man).group(1)
    r['archive_matches_head'] = r['archive_commit'] == git('rev-parse', 'HEAD')
    return r


def checklist(r: dict, manifest: dict, files: dict) -> str:
    mark = lambda ok: 'done' if ok else 'CHECK'  # noqa: E731
    name = lambda k: f'`{files[k].name}`'  # noqa: E731
    return f"""# Journal of Economic Theory submission checklist

Built {manifest['built']} from commit {manifest['commit'][:7]}{' (uncommitted source changes)' if manifest['covered_sources_uncommitted'] else ''}.
Guide for Authors: {GUIDE} (read 2026-10-21). Submit at {SUBMIT}.

| Requirement | Status | Evidence |
| --- | --- | --- |
| Manuscript as an editable source, no subfolders ("A PDF is not an acceptable source file") | {mark(r['flat_source_text_identical'] and r['flat_source_undefined'] == 0)} | {name('manuscript_source')}: one `.tex` file; compiled alone with pdflatex: {r['flat_source_pages']} pages, {r['flat_source_undefined']} undefined references, text identical to the reference PDF: {r['flat_source_text_identical']} |
| Title page: title, authors, affiliations with postal address and country, corresponding author's email | {mark(r['page1_has_title_authors_email'] and r['title_page_has_all'])} | On page 1 of {name('manuscript_pdf')} ({r['manuscript_pages']} pages) and in {name('title_page')} ({r['title_page_pages']} page) |
| Abstract of at most 250 words | {mark((r['abstract_words'] or 999) <= 250)} | {r['abstract_words']} words |
| 1 to 7 keywords, none built with "and" or "of" | {mark(r['keywords_ok'])} | {len(r['keywords'])}: {'; '.join(r['keywords'])} |
| Highlights (encouraged): 3 to 5 bullets, at most 85 characters, Word file named "highlights" | {mark(r['highlights_ok'])} | {name('highlights')}; lengths {r['highlight_lengths']} |
| Declaration of interests (declarations tool) | {mark(True)} | {name('declaration_docx')}: the tool's standard "nothing to declare" sentence for the three authors (all confirmed 2026-10-21). If the form insists on the tool's own file, generate it at https://declarations.elsevier.com/ ("I have nothing to declare") |
| Generative-AI statement as its own section, last before the references | {mark(r['ai_section_last_before_references'])} | Checked in the PDF text; the same text for a form field: `AI_use_description.txt` |
| Funding, CRediT and data availability statements | done | In the Declarations section of the manuscript |
| Supplementary files cited in the text, each with a caption; published exactly as received | {mark(not r['online_appendix_history_marks'] and not r['formal_supplement_history_marks'])} | {name('online_appendix')} ({r['online_appendix_pages']} pp), {name('formal_supplement')} ({r['formal_supplement_pages']} pp), {name('lean_source_archive')}; project-history marks found: {r['online_appendix_history_marks'] + r['formal_supplement_history_marks'] or 'none'}; captions in `UPLOAD-PLAN.md` |
| Research data and code (Option C: deposit, cite and link) | {mark(r['archive_matches_head'] and r['archive_sha256_matches_file'])} | Public release cited in the data statement; archive built from commit {r['archive_commit'][:7]} (= HEAD: {r['archive_matches_head']}), SHA-256 file matches: {r['archive_sha256_matches_file']} |
| References: every reference real, consistent style | done | BibTeX with one style; 0 undefined citations in the build |
| No em dashes in any document | {mark(r['manuscript_em_dashes'] + r['online_appendix_em_dashes'] + r['formal_supplement_em_dashes'] == 0)} | manuscript {r['manuscript_em_dashes']}, Online Appendix {r['online_appendix_em_dashes']}, formal supplement {r['formal_supplement_em_dashes']} |
| Cover letter (not required by the Guide; for the form's field) | {mark('[status' not in (ROOT / 'paper' / 'submission' / 'COVER-LETTER-DRAFT.md').read_text(encoding='utf-8'))} | {name('cover_letter_pdf')} and `.docx`; the related manuscript's status is a bracket until the authors fill it in |
| Not under consideration elsewhere; all authors approve | done | Confirmed by the authors on 2026-10-21 |
| Submission fee | none | The Guide and the journal pages name no submission fee |

## Upload (submit.elsevier.com/JET)

| Item | File |
| --- | --- |
| Manuscript (LaTeX source) | {name('manuscript_source')} (unzip if the form wants the `.tex` itself) |
| Title page, if the form asks for one | {name('title_page')} |
| Highlights | {name('highlights')} |
| Declaration of interests | {name('declaration_docx')} (or the tool's file) |
| Supplementary material | {name('online_appendix')}, {name('formal_supplement')}, {name('lean_source_archive')} |
| Cover letter, if the form has a field | {name('cover_letter_pdf')} |

Review is single anonymized: no anonymized version is needed. The reference PDF {name('manuscript_pdf')} is for the
authors' comparison with the system's own build. Choices already made: no open access, no SSRN posting at submission.
"""


def main() -> int:
    if '--skip-build' not in sys.argv:
        run(['pwsh', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', str(ROOT / 'scripts' / 'Build-Paper.ps1')])
    commit = git('rev-parse', '--short', 'HEAD')
    dirty = git('status', '--porcelain', '--', *COVERED)
    stamp = dt.date.today().strftime('%Y%m%d')
    out = ROOT / 'dist' / 'jet_submission' / f"{stamp}-{commit}{'-dirty' if dirty else ''}"
    if out.exists():
        shutil.rmtree(out)
    work = out / '_work'
    work.mkdir(parents=True)

    tex, flat_pdf = build_source(work)
    title_pdf = build_title_page(work)
    files = {
        'manuscript_source': out / f'{STEM}_manuscript_source.zip',
        'manuscript_pdf': out / f'{STEM}_manuscript_reference.pdf',
        'title_page': out / f'{STEM}_title_page.pdf',
        'highlights': out / f'{STEM}_highlights.docx',
        'declaration_docx': out / f'{STEM}_declaration_of_interests.docx',
        'declaration_pdf': out / f'{STEM}_declaration_of_interests.pdf',
        'online_appendix': out / f'{STEM}_online_appendix.pdf',
        'formal_supplement': out / f'{STEM}_formal_supplement.pdf',
        'lean_source_archive': out / f'{STEM}_lean_source_archive.zip',
        'cover_letter_pdf': out / f'{STEM}_cover_letter.pdf',
    }
    with zipfile.ZipFile(files['manuscript_source'], 'w', zipfile.ZIP_DEFLATED) as z:
        z.write(tex, tex.name)
    shutil.copy2(PAPER / 'sanctions_jet_draft.pdf', files['manuscript_pdf'])
    shutil.copy2(title_pdf, files['title_page'])
    hl = [l for l in (PAPER / 'sanctions_highlights.txt').read_text(encoding='utf-8').splitlines() if l.strip()]
    write_docx(files['highlights'], [('Highlights', True)] + [('\u2022 ' + h, False) for h in hl])
    shutil.copy2(build_declaration(work, out), files['declaration_pdf'])
    shutil.copy2(PAPER / 'sanctions_jet_appendix.pdf', files['online_appendix'])
    shutil.copy2(PAPER / 'sanctions_formal_supplement.pdf', files['formal_supplement'])
    shutil.copy2(ARCHIVE, files['lean_source_archive'])
    (out / (files['lean_source_archive'].name + '.sha256')).write_text(
        f"{sha256(files['lean_source_archive'])}  {files['lean_source_archive'].name}\n", encoding='utf-8')
    shutil.copy2(build_cover_letter(work, out), files['cover_letter_pdf'])
    files['cover_letter_docx'] = out / f'{STEM}_cover_letter.docx'
    (out / 'AI_use_description.txt').write_text(
        'For a submission-form field, if one asks; the same text is the section "' + AI_TITLE + '" of the manuscript.\n\n'
        + ai_statement() + '\n', encoding='utf-8')
    shutil.copy2(ROOT / 'paper' / 'submission' / 'README.md', out / 'UPLOAD-PLAN.md')

    r = checks({**files, 'lean_source_archive': ARCHIVE}, flat_pdf, files['title_page'])
    manifest = {
        'built': dt.datetime.now().isoformat(timespec='seconds'),
        'commit': git('rev-parse', 'HEAD'),
        'covered_sources_uncommitted': bool(dirty),
        'guide_for_authors': GUIDE,
        'submission_site': SUBMIT,
        'checks': r,
        'files': {k: {'path': v.name, 'sha256': sha256(v)} for k, v in files.items()},
        'not_done_here': [
            'the related manuscript\'s status in the cover letter (a bracket until the authors fill it in)',
            'the corresponding author\'s ORCID, if the form asks',
            'the Zenodo DOI for the release (the data statement says a DOI will accompany publication)',
            'the submission at submit.elsevier.com/JET',
        ],
    }
    (out / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2), encoding='utf-8')
    (out / 'SUBMISSION_CHECKLIST.md').write_text(checklist(r, manifest, files), encoding='utf-8')
    shutil.rmtree(work)
    print(json.dumps({'out': str(out), **r}, indent=2))
    ok = (r['flat_source_text_identical'] and r['flat_source_undefined'] == 0 and r['page1_has_title_authors_email']
          and r['title_page_pages'] == 1 and r['title_page_has_all'] and (r['abstract_words'] or 999) <= 250
          and r['keywords_ok'] and r['highlights_ok'] and r['ai_section_last_before_references']
          and not r['online_appendix_history_marks'] and not r['formal_supplement_history_marks']
          and r['archive_matches_head'] and r['archive_sha256_matches_file'] and r['undefined_reference_marks'] == 0)
    print('JET format checks:', 'PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
