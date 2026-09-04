#!/usr/bin/env python3
"""Check that every theorem in HyperTamari/*.lean is covered by a `#print axioms`
line in the build log, and summarise the axiom dependencies.

Usage:  lake build > logs/axiom-audit.txt 2>&1 ; python3 scripts/check_audit.py logs/axiom-audit.txt

Exit status 0 iff  declared == audited, no sorryAx, no Classical.choice,
no `sorry` / `native_decide` / `axiom` in the sources.
"""
import re, sys, pathlib

root = pathlib.Path(__file__).resolve().parent.parent
log = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else root / "logs" / "axiom-audit.txt")
files = sorted((root / "HyperTamari").glob("*.lean"))

decl_re = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)")
ns_open = re.compile(r"^namespace\s+(\S+)")
ns_close = re.compile(r"^end\s+(\S+)")

declared = {}
bad_tokens = {"sorry": 0, "native_decide": 0, "axiom ": 0}
for f in files:
    stack = []
    for line in f.read_text(encoding="utf-8").splitlines():
        m = ns_open.match(line)
        if m:
            stack.append(m.group(1)); continue
        m = ns_close.match(line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop(); continue
        m = decl_re.match(line)
        if m:
            full = ".".join(stack + [m.group(1)])
            declared[full] = f.name
        for tok in bad_tokens:
            # count occurrences outside comments/docstrings is hard; count raw lines
            # that start a declaration with the token
            if re.match(r"^\s*(?:theorem|lemma|def|example).*\b" + tok.strip() + r"\b", line) or \
               re.match(r"^\s*" + tok.strip() + r"\b", line):
                bad_tokens[tok] += 1

aud_dep = re.compile(r"'([^']+(?:'[^' ]*)?)' depends on axioms: \[([^\]]*)\]")
aud_none = re.compile(r"'([^']+(?:'[^' ]*)?)' does not depend on any axioms")
audited = {}
text = log.read_text(encoding="utf-8", errors="replace")
for m in aud_dep.finditer(text):
    audited[m.group(1)] = tuple(s.strip() for s in m.group(2).split(","))
for m in aud_none.finditer(text):
    audited[m.group(1)] = ()

missing = sorted(set(declared) - set(audited))
extra = sorted(set(audited) - set(declared))
from collections import Counter
hist = Counter(audited.values())
n_sorry = sum(1 for v in audited.values() if "sorryAx" in v)
n_choice = sum(1 for v in audited.values() if "Classical.choice" in v)

print(f"declared theorems : {len(declared)}")
print(f"audited (depends) : {sum(1 for v in audited.values() if v)}")
print(f"audited (no axioms): {sum(1 for v in audited.values() if not v)}")
print(f"audited total     : {len(audited)}")
print(f"missing from audit: {len(missing)} {missing}")
print(f"audited but not declared: {len(extra)} {extra}")
for k, v in sorted(hist.items(), key=lambda kv: -kv[1]):
    print(f"  {', '.join(k) if k else '(none)'}: {v}")
print(f"sorryAx: {n_sorry}   Classical.choice: {n_choice}   source tokens: {bad_tokens}")
ok = not missing and not extra and n_sorry == 0 and n_choice == 0 and all(v == 0 for v in bad_tokens.values())
print("AUDIT", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
