#!/usr/bin/env python3
"""Check the correspondence table of the paper against its own population and
against the Lean sources.

  * population = every numbered environment (theorem, proposition, lemma, corollary,
    definition, example, remark, conjecture) in the source of Sections 1-6, i.e.
    between \\section{Introduction} and \\section{The Lean development};
  * every member of the population must be \\ref'd in the table `tab:map`, and the
    table must \\ref nothing outside the population;
  * every \\verb|name| in Section 7 that looks like an identifier must be a
    declaration of the Lean development (or a Lean/Mathlib name on a short allowlist).

Usage: python3 scripts/check_table.py [paper/hyper-tamari.tex]
"""
import re, sys, pathlib

root = pathlib.Path(__file__).resolve().parent.parent
tex = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else root / "paper" / "hyper-tamari.tex")
src = tex.read_text(encoding="utf-8")

ENVS = "theorem|proposition|lemma|corollary|definition|example|remark|conjecture"
i0 = src.index(r"\section{Introduction}")
i1 = src.index(r"\section{The Lean development}")
body = src[i0:i1]
pop = []
for m in re.finditer(r"\\begin\{(" + ENVS + r")\}(?:\[[^\]]*\])?(\\label\{([^}]*)\})?", body):
    env, lab = m.group(1), m.group(3)
    if lab is None:
        print(f"ERROR: unlabelled {env} environment at offset {m.start()}"); sys.exit(1)
    pop.append((env, lab))
from collections import Counter
print("population:", len(pop), dict(Counter(e for e, _ in pop)))

# numbered environments outside sections 1-6 (must be none for the population claim)
outside = re.findall(r"\\begin\{(" + ENVS + r")\}", src[i1:])
print("numbered environments in sections 7-8:", len(outside))

tm = re.search(r"\\begin\{table\}.*?\\label\{tab:map\}.*?\\end\{table\}", src, re.S)
table = tm.group(0)
refs = set(re.findall(r"\\ref\{([^}]*)\}", table))
poplabels = {lab for _, lab in pop}
missing = sorted(poplabels - refs)
extra = sorted(refs - poplabels)
print("in population but not in table:", missing)
print("in table but not in population:", extra)

# Lean declarations
decl_re = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|def|abbrev|inductive|structure)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)")
names = set()
for f in sorted((root / "HyperTamari").glob("*.lean")):
    stack = []
    for line in f.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^namespace\s+(\S+)", line)
        if m: stack.append(m.group(1)); continue
        m = re.match(r"^end\s+(\S+)", line)
        if m and stack and stack[-1] == m.group(1): stack.pop(); continue
        m = decl_re.match(line)
        if m:
            full = ".".join(stack + [m.group(1)])
            names.add(full)
            if full.startswith("HyperTamari."):
                names.add(full[len("HyperTamari."):])
ALLOW = {"sorry", "native_decide", "sorryAx", "propext", "Quot.sound", "Classical.choice",
         "nlinarith", "norm_num", "omega", "decide", "Nat.pow_lt_pow_right",
         "Nat.pow_right_injective", "Nat.pow_le_pow_right", "Nat.add_le_mul",
         "Nat.pow_lt_pow_succ", "Relation.ReflTransGen", "lake"}
sec7 = src[i1:src.index(r"\section{Related work}")]
unknown = []
for v in re.findall(r"\\verb\|([^|]*)\|", sec7):
    tok = v.split()[0] if v.split() else v
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", tok) and tok not in names and tok not in ALLOW:
        unknown.append(v)
print("verb names in section 7 not found in the development:", unknown)
ok = not missing and not extra and not unknown and not outside
print("TABLE", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
