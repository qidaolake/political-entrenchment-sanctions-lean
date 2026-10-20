"""Shared TeX comment stripper for the paper scanners (round W, 2026-09-17;
the reader's S–V audit, Q1 §9: the regex `(?<!\\)%` treats `\\%` as an
escaped percent, so a comment after a doubled backslash was kept as prose).

`strip_comment(line)` drops everything from the first `%` that is preceded by
an even number of backslashes (zero included). It tracks backslash parity
character by character, which is the rule of the supported plain-TeX syntax;
verbatim environments and catcode changes are outside its scope, as they are
outside the scanners' scope.
"""
from __future__ import annotations


def strip_comment(line: str) -> str:
    i = 0
    n = len(line)
    while i < n:
        ch = line[i]
        if ch == "\\":
            i += 2          # an escaped character (\%, \\, \{ ...) is never a comment start
            continue
        if ch == "%":
            return line[:i]
        i += 1
    return line


def strip_comments(text: str) -> str:
    return "\n".join(strip_comment(l) for l in text.splitlines())
