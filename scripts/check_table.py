#!/usr/bin/env python3
"""Check the correspondence table of the merged paper against its own population.

The paper fixes the population of `tab:map` explicitly.  This script recomputes it
from the source and checks every claim made about it:

  * the population is every numbered environment of the Part II sections, minus the
    three Part I statements of the introduction, plus the six environments of the
    preliminaries that Part II uses;
  * its size and its breakdown by kind are as printed;
  * every member is \\ref'd in the table except Remark rem:fit, and the table \\ref's
    nothing outside the population apart from section labels;
  * every member carries a \\label.

What it does **not** check: that every *clause* of a statement has its own row (a
statement with several clauses may occupy several, and the paper prints no row count),
nor that the Lean declaration named in a row actually says what the row claims.  Those
are read by eye.  `check_names.py` checks that the names exist; nothing here checks that
a named theorem has the hypotheses and conclusion of the printed statement.

Usage: python3 scripts/check_table.py [path/to/bracketing-orders.tex]
"""
import re, sys, pathlib
from collections import Counter

here = pathlib.Path(__file__).resolve().parent
root = here.parent
if len(sys.argv) > 1:
    tex = pathlib.Path(sys.argv[1])
else:
    candidates = [
        root / "paper" / "bracketing-orders.tex",
        root.parent / "paper" / "bracketing-orders.tex",
    ]
    tex = next((p for p in candidates if p.exists()), None)
    if tex is None:
        raise SystemExit("bracketing-orders.tex not found; pass its path explicitly")
src = tex.read_text(encoding="utf-8")

ENVS = "theorem|proposition|lemma|corollary|definition|example|remark|conjecture"

# --- what the paper says -----------------------------------------------------------
PART2_SECS   = ["sec:rank3", "sec:rank4", "sec:dicho", "sec:general", "sec:varleaf"]
INTRO_EXCEPT = {"thm:main", "thm:sep", "cor:test"}
PRELIM6      = {"def:hyper", "def:trees", "def:rot",
                "lem:conv", "lem:mul-le-pow", "prop:mul-eq-pow"}
NOT_IN_TABLE   = {"rem:fit"}

# The size and the breakdown are read from what the paper prints, not hard-coded, so
# that changing either the paper or the source makes the check fail.
WORDS = {"theorem": "theorems", "proposition": "propositions", "lemma": "lemmas",
         "corollary": "corollaries", "definition": "definitions", "example": "example",
         "remark": "remarks"}

# --- recompute it ------------------------------------------------------------------
secs = [(m.start(), m.group(1))
        for m in re.finditer(r"\\section\{[^}]*\}\\label\{([^}]*)\}", src)]

def sec_of(pos):
    cur = None
    for p, lab in secs:
        if p <= pos:
            cur = lab
        else:
            break
    return cur

i0 = src.index(r"\section{Introduction}")
i1 = src.index(r"\section{The Lean development}")
found = []
for m in re.finditer(r"\\begin\{(" + ENVS + r")\}(?:\[[^\]]*\])?(?:\\label\{([^}]*)\})?",
                     src[i0:i1]):
    found.append((sec_of(i0 + m.start()), m.group(1), m.group(2), i0 + m.start()))

pop = []
for sec, env, lab, pos in found:
    keep = (sec in PART2_SECS
            or (sec == "sec:intro" and lab not in INTRO_EXCEPT)
            or (sec == "sec:prelim" and lab in PRELIM6))
    if keep:
        if lab is None:
            print(f"ERROR: unlabelled {env} in {sec} at offset {pos}"); sys.exit(1)
        pop.append((env, lab))

kinds = dict(Counter(e for e, _ in pop))
print(f"population: {len(pop)} {kinds}")
ok = True

msize = re.search(r"There are \$(\d+)\$ of them", src)
if msize is None:
    print("ERROR: the paper does not print the size of the population"); sys.exit(1)
printed_size = int(msize.group(1))
sentence = src[msize.start():msize.start() + 400]
printed_kinds = {}
for env, word in WORDS.items():
    m = re.search(r"\$(\d+)\$~?\\?\s*" + word, sentence)
    if m:
        printed_kinds[env] = int(m.group(1))
print(f"the paper prints: {printed_size} {printed_kinds}")

if len(pop) != printed_size:
    print(f"ERROR: the paper prints {printed_size}, the source has {len(pop)}"); ok = False
if printed_kinds != kinds:
    print(f"ERROR: the printed breakdown {printed_kinds} is not the source's {kinds}")
    ok = False
if sum(printed_kinds.values()) != printed_size:
    print(f"ERROR: the printed breakdown does not add up to {printed_size}"); ok = False

tm = re.search(r"\\begin\{longtable\}.*?\\label\{tab:map\}.*?\\end\{longtable\}", src, re.S)
if tm is None:
    print("ERROR: table tab:map not found"); sys.exit(1)
refs = set(re.findall(r"\\ref\{([^}]*)\}", tm.group(0)))
labs = {lab for _, lab in pop}
missing = labs - refs - NOT_IN_TABLE
extra   = {r for r in refs - labs if not r.startswith("sec:")}
if missing:
    print(f"ERROR: in the population but not in the table: {sorted(missing)}"); ok = False
if extra:
    print(f"ERROR: in the table but not in the population: {sorted(extra)}"); ok = False
for lab in NOT_IN_TABLE:
    if lab in refs:
        print(f"ERROR: {lab} is said not to appear in the table, but it does"); ok = False
    if lab not in labs:
        print(f"ERROR: {lab} is said to be in the population, but it is not"); ok = False

rows = [r for r in tm.group(0).split(r"\\") if r.strip()]
print(f"table rows (raw): {len(rows)}   refs in table: {len(refs)}")
if not ok:
    sys.exit(1)
print("OK: the population, its breakdown and the two exceptions are as the paper says")
