#!/usr/bin/env python3
"""Check every name printed in the paper's section "The Lean development".

Three kinds of name occur there and each is checked differently.

  * declarations of the two developments: accepted only if they appear in an audit
    log (which lists fully qualified names) or as a declaration header in a source
    file of the development;
  * names from Lean core or Mathlib: checked by elaborating `#check @name` inside the
    Part I project, which has Mathlib as a dependency;
  * tactic names and file names: skipped, from a fixed list.

Usage: python3 scripts/check_names.py [path/to/hyper-tamari.tex] [--no-lean]
"""
import re, subprocess, sys, pathlib, tempfile

here = pathlib.Path(__file__).resolve().parent
root = here.parent
args = [a for a in sys.argv[1:] if not a.startswith("--")]
run_lean = "--no-lean" not in sys.argv
tex = pathlib.Path(args[0]) if args else root / "paper" / "hyper-tamari.tex"
src = tex.read_text(encoding="utf-8")

partI  = root / "part1"     # the Part I development (ChowStanley)
partII = root               # the Part II development (HyperTamari)
logs = [partI / "logs" / "axiom-audit.txt", partII / "logs" / "axiom-audit.txt"]

decls = set()
for lg in logs:
    if not lg.exists():
        print(f"ERROR: missing audit log {lg}"); sys.exit(1)
    text = lg.read_text(encoding="utf-8")
    decls |= set(re.findall(r"'([A-Za-z_][A-Za-z0-9_.'!?]*)'\s+(?:depends on axioms|does not depend)", text))
    for m in re.finditer(r"^(?:AXIOM-FREE|prop/quot|CHOICE|OTHER)\s+(\S+)", text, re.M):
        decls.add(m.group(1))

# Declaration names of the sources, fully qualified by tracking `namespace`/`end`.
# Definitions and inductives are not audited, so the sources are the only record of them;
# but a *qualified* name printed in the paper must match a qualified name here, or an
# invented namespace on a real declaration slips through.
heads = set()          # bare names
qheads = set()         # fully qualified names
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
                  r"(?:theorem|lemma|def|abbrev|inductive|structure|instance)\s+"
                  r"([A-Za-z_][A-Za-z0-9_.']*)")
for d in [partI / "ChowStanley", partII / "HyperTamari"]:
    if not d.exists():
        continue
    for f in sorted(d.rglob("*.lean")):
        stack = []
        for line in f.read_text(encoding="utf-8").splitlines():
            mns = re.match(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)", line)
            if mns:
                stack.extend(mns.group(1).split(".")); continue
            if re.match(r"^\s*end\b", line):
                if stack: stack.pop()
                continue
            m = DECL.match(line)
            if m:
                heads.add(m.group(1))
                qheads.add(".".join(stack + [m.group(1)]) if stack else m.group(1))
filestems = {f.stem for d in [partI / "ChowStanley", partII / "HyperTamari"]
             if d.exists() for f in d.rglob("*.lean")}
print(f"audited declarations: {len(decls)}   source declaration headers: {len(heads)}"
      f"   source files: {len(filestems)}")

def find_section(*prefixes):
    for pre in prefixes:
        j = src.find(pre)
        if j >= 0:
            return j
    print(f"ERROR: none of {prefixes} found in {tex}"); sys.exit(1)

i0 = find_section(r"\section{The Lean development}",
                  r"\section{Computations, and the Lean developments}")
i1 = find_section(r"\section{Related work")
sec = src[i0:i1]

# The correspondence table names declarations too.  It used to sit inside the section;
# it now lives in an appendix, so it must be scanned separately or its names go
# unchecked.  If the paper has a table, failing to find it is an error, not a pass.
tm = re.search(r"\\begin\{longtable\}.*?\\label\{tab:map\}.*?\\end\{longtable\}", src, re.S)
if r"\label{tab:map}" in src and tm is None:
    print("ERROR: tab:map is referenced but its longtable was not found"); sys.exit(1)
if tm is not None:
    sec = sec + "\n" + tm.group(0)
    print("the correspondence table is included in the scan")

TACTICS = {"omega", "decide", "native_decide", "norm_num", "nlinarith", "simp", "rfl",
           "sorry", "sorryAx", "propext", "Quot.sound", "Classical.choice"}
SKIP = re.compile(r"\.(lean|py|sh|json|md|txt)$|^logs/|/$|\s")
EXTERNAL = re.compile(r"^(Nat|Int|List|Option|Function|Relation|Finset|Classical)\.")

printed = re.findall(r"\\verb\|([^|]*)\|", sec)
local, external, bad = set(), set(), []
for n in printed:
    if SKIP.search(n) or n in TACTICS or n in filestems:
        continue
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']*", n):
        continue
    if EXTERNAL.match(n):
        external.add(n); continue
    known = decls | qheads
    if "." in n:
        # a namespace was printed: it must really be that declaration's namespace
        ok = any(d == n or d.endswith("." + n) for d in known)
    else:
        ok = n in known or any(d.endswith("." + n) for d in known) or n in heads
    if ok:
        local.add(n)
    else:
        bad.append(n)

print(f"development names checked: {len(local)}   external names: {len(external)}")
if bad:
    print("MISSING from both developments:")
    for n in sorted(set(bad)):
        print("   ", n)
    sys.exit(1)

if run_lean and external:
    body = "import Mathlib\n" + "".join(f"#check @{n}\n" for n in sorted(external))
    f = partI / "scripts" / "_CheckNames.lean"
    f.write_text(body, encoding="utf-8")
    try:
        r = subprocess.run(["lake", "env", "lean", "scripts/_CheckNames.lean"],
                           cwd=partI, capture_output=True, text=True, timeout=1800)
        out = r.stdout + r.stderr
        if r.returncode != 0 or "error" in out:
            print("EXTERNAL NAMES THAT DO NOT ELABORATE:")
            print(out[:4000]); sys.exit(1)
        print(f"external names elaborated with Mathlib: {len(external)}")
    finally:
        f.unlink(missing_ok=True)
elif external:
    print(f"external names NOT checked (--no-lean): {sorted(external)}")

print("OK: every name printed in the section is a real declaration")
