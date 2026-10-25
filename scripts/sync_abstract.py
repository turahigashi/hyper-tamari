#!/usr/bin/env python3
r"""Regenerate (or verify) submission_abstract.txt from the abstract of the paper.

A submission form accepts LaTeX math but not user macros or text-level formatting,
so the macros defined in the preamble are expanded and \emph/\textbf are stripped.
Run with --check to fail when the two have drifted apart.
"""
import re, sys, io, pathlib

PAPER = pathlib.Path(__file__).resolve().parent.parent / "paper"
TEX = str(PAPER / "hyper-tamari.tex")
OUT = str(PAPER / "submission_abstract.txt")
HEAD = ("The abstract as plain text, for the submission form.\n"
        "Generated from the abstract of paper/hyper-tamari.tex by scripts/sync_abstract.py; do not edit by hand.\n"
        "LaTeX math is allowed; user macros and non-math formatting are not, so \\HH, \\ev,\n"
        "\\St, \\emph and \\textbf have been expanded or removed.  Paste the text below.\n"
        + "=" * 72 + "\n\n")
MACRO = {r"\HH": r"\mathrm{H}", r"\ev": r"\mathrm{ev}", r"\St": r"\mathrm{St}",
         r"\Tam": r"\mathrm{Tam}", r"\tw": r"\uparrow\uparrow", r"\N": r"\mathbb{N}"}

def body():
    s = io.open(TEX, encoding="utf-8").read()
    m = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", s, re.S)
    if not m:
        sys.exit("no abstract found")
    t = m.group(1)
    for k, v in sorted(MACRO.items(), key=lambda kv: -len(kv[0])):
        t = re.sub(re.escape(k) + r"(?![A-Za-z])", lambda _m, v=v: v, t)
    # strip text-level formatting, keeping the words
    for cmd in ("emph", "textbf", "textit"):
        while True:
            t2 = re.sub(r"\\" + cmd + r"\{([^{}]*)\}", r"\1", t)
            if t2 == t:
                break
            t = t2
    t = t.replace("Lean~4", "Lean 4").replace("~", " ")
    paras = [" ".join(p.split()) for p in t.strip().split("\n\n")]
    return "\n\n".join(p for p in paras if p) + "\n"

def main():
    want = HEAD + body()
    if "--check" in sys.argv:
        have = io.open(OUT, encoding="utf-8").read()
        if have != want:
            sys.exit("FAIL: paper/submission_abstract.txt is out of date with the abstract of paper/hyper-tamari.tex")
        print("OK: paper/submission_abstract.txt matches the abstract")
        return
    io.open(OUT, "w", encoding="utf-8").write(want)
    print("wrote paper/submission_abstract.txt (" + str(len(body().split())) + " words)")
    for bad in ("\\emph", "\\textbf", "\\HH", "\\ev{", "\\St", "~"):
        if bad in want[len(HEAD):]:
            sys.exit("FAIL: unexpanded " + bad + " remains")

main()
