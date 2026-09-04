# hyper-tamari

A Lean 4 formalization accompanying the paper

> **Bracketing hyperoperations: a rank dichotomy for the Tamari order**
> Toshihisa Urahigashi

## What the paper proves

Let `H_r` be the Goodstein hyperoperation hierarchy: `H_1` is addition, `H_2`
multiplication, `H_3` exponentiation, `H_4` tetration. For `r ≥ 3` the operation is
non-associative, so the value of `H_r(a, …, a)` depends on the bracketing, i.e. on a
binary tree. The paper studies how that value varies over the **Tamari lattice** of
such trees.

**A semi-associative law runs through the whole hierarchy.** For every `r ≥ 3` and
all `x, y ≥ 2`,

```
H_r(H_r(x,y), z)  ≤  H_r(x, H_r(y,z)).
```

Hence a right rotation at any node never decreases the value, evaluation is
order-preserving from the Tamari lattice to `(ℕ, ≤)`, the left comb is a minimiser,
and the right comb — whose value is `H_{r+1}(a,n)` — is a maximiser.

**From rank 4 the evaluation is strictly increasing along every Tamari cover**
(`Rot.eval_lt`), not merely along root rotations, and hence along the Tamari order
itself (`Rot.eval_lt_of_transGen`, the transitive closure of the cover relation);
the non-strict version lifts likewise (`Rot.eval_le_of_reflTransGen`).

**Everything is proved for arbitrary leaf values** (`HyperTamari/VarLeaves.lean`), not
only for a single repeated label — `LRot.eval_lt` gives strict monotonicity along every
Tamari cover at every rank `r ≥ 4` for arbitrary leaf values `≥ 2`. This extends to the
whole hierarchy a rank-3 observation that appears to have been made only for
exponentiation, in a 2018 MathOverflow discussion whose author states he completed only
"half of the proof". The single-label case is recovered by specialisation
(`Rot.eval_lt_of_var`).

**The collapse at rank 3 is completely located** (`cover_strict_unless_rank3_two`):
a Tamari cover fails to be strict exactly when the two rotated subtrees are both
leaves labelled `2`. So for a single repeated label `a`, every cover is strict unless
`(r, a) = (3, 2)`.

**The main result is a complete classification of the equality cases.**
For `x, y ≥ 2`:

```
r  = 3 :   equality  ⟺  z = 1  or  (y,z) = (2,2)
r ≥ 4 :   equality  ⟺  z = 1
```

So rank 3 carries **exactly one** non-trivial *equality pattern* — already visible
with four leaves, where the Tamari cover `((aa)a)a ⋖ (aa)(aa)` has equal endpoints —
and from rank 4 onwards the evaluation is strictly increasing along every such cover.
(Several trees do share a value at rank 3 with `a = 2` and four leaves; what is unique
is the non-trivial equality pattern `(y,z) = (2,2)` of the local law itself.) The
rank-3 equality is produced by the collapsing law `(x^y)^z = x^{yz}`, which reduces
the rank-3 inequality to `yz ≤ y^z`; the classification shows that no equality of
this kind survives at rank 4 or above.

The statement is not an asymptotic triviality: the two sides compare a growing first
argument against a growing second one, and small arguments do not blow up with the
rank, since `H_r(2,2) = 4` for every `r ≥ 2`. The hypothesis `y ≥ 2` is sharp as a
uniform hypothesis: for every `r ≥ 3` and all `x, z ≥ 2`, taking `y = 1` reverses the
inequality.

## Contents

| Path | Lines | Contents |
|---|---:|---|
| `HyperTamari/Basic.lean` | 351 | `hyper`, verification of the conventions, the complete rank-3 analysis, `BTree` / `eval`, the five values of `T_4` (`rank3_five_values`) |
| `HyperTamari/Tetration.lean` | 537 | rank 4 (tetration): `tet_ht`, strictness, the dichotomy, the rotation relation `Rot`, `sq_le_pow_fails` |
| `HyperTamari/General.lean` | 695 | general rank: `sum_lemma`, `ht_of_sum`, `ht_general`, `equality_classification`, `hyper_lt_base`, `Rot.eval_lt`, `ht_lt_at_zero`, `add_eq_hyper_iff`, `ht_reversed_at_y_one` |
| `HyperTamari/VarLeaves.lean` | 357 | arbitrary leaf values: `LTree`, `LTree.eval`, the cover relation `LRot`, `LRot.eval_lt` and its transitive closure, `cover_strict_unless_rank3_two`, and the bridge theorems recovering the single-label statements (`Rot.eval_le_of_var`, `Rot.eval_lt_of_var`, `Rot.eval_le_of_reflTransGen_of_var`, `Rot.eval_lt_of_transGen_of_var`) |
| `logs/axiom-audit.txt` | — | raw `lake build` output recording the axiom audit |
| `scripts/check_audit.py` | — | checks declared theorems against the audit log (coverage, `sorryAx`, `Classical.choice`) |
| `scripts/check_table.py` | — | checks the paper's correspondence table against its population and against the Lean declaration names |
| `paper/` | — | the paper (LaTeX source and PDF) |

Section 8 of the paper (*The Lean development*) contains a statement-by-statement
correspondence table whose population is defined explicitly: all 24 numbered
environments of Sections 1–7 (6 theorems, 3 propositions, 6 lemmas, 2 corollaries,
4 definitions, 1 example, 2 remarks). It classifies each clause as **exact** (one
declaration with the same quantifiers, hypotheses and conclusion), **collective**
(covered by a combination of declarations) or **prose** (background facts about the
Tamari lattice, or explanatory remarks, that are *not* formalized here). The only row outside that population is one recording the
specialisation of the labelled-tree results to a single repeated label. That the
table covers the whole population, adds nothing else beyond that row, and names only
existing declarations is checked by `scripts/check_table.py`. The paper does not claim that everything it
says is machine-checked; what is machine-checked is every clause of every numbered
statement that asserts an inequality or an equality about `H_r` or about the
evaluation of trees.

## Prior work on the rank-3 case

The rank-3 monotonicity is **not new**. A MathOverflow discussion of January 2018
(question 289708, asked by D. Spivak) orders bracketings of exponentiation by
comparing values *for every* assignment of leaf labels, and in the answers T. Chow
proves that a Stanley cover decreases the value, while M. Rubey reduces the same
covering relation to exactly the rank-3 semi-associative inequality. Since that
evaluation order quantifies over all leaf assignments and the Stanley lattice extends
the Tamari lattice, the rank-3 case here is already contained in that discussion, in
a stronger form. What is not there is any rank other than 3, the equality analysis, or
the strictness phenomenon. See Section 9 of the paper.

## Prior work on orders attached to iterated exponentials

Brunson (*Amer. Math. Monthly* 93, 1986), Stembridge (*JCTA* 50, 1989),
Griggs (*Discrete Math.* 88, 1991) and Griggs–Wachs (*European J. Combin.* 13, 1992)
all study orders on iterated exponentials, but in every case **the bracketing is
fixed** — it is the right comb, "association is always to the upper right" — and what
varies is the assignment of entries to its leaves (a permutation, or a word over two
letters). Here the reverse holds: the entries are fixed, all equal to `a`, and the
bracketing varies. The two families of questions are orthogonal.

## Audit

Measured, not asserted (`logs/axiom-audit.txt` is the raw evidence):

- `lake build` exits 0.
- **116** theorems and lemmas; **116** audited with `#print axioms`; **0** missing.
  Coverage is checked mechanically by `scripts/check_audit.py`, which compares the
  declaration names in the sources against the audit output.
- **No `sorryAx`.** No `sorry`, no `native_decide`, no private `axiom`, no
  `ofReduceBool`.
- Axiom dependencies: `propext` alone (5), `propext, Quot.sound` (105), and six
  theorems depending on no axioms at all.
  In particular **no declaration depends on `Classical.choice`.**

Choice-freeness is not what the paper is about — every statement here is an
elementary assertion about natural numbers. It is recorded because it costs nothing
and makes the artifact reusable in settings that must avoid choice. An earlier
version did depend on `Classical.choice` in 30 declarations; the dependency came
from four incidental sources — the Mathlib lemmas `Nat.pow_lt_pow_right` and
`Nat.pow_right_injective`, the `nlinarith` tactic, and `norm_num` applied to a
numeric *inequality* (`omega` discharges the same goals without choice; `norm_num`
on an *equation* is fine). Replacing them changed no statement.

## Building

```bash
lake exe cache get
lake build > logs/axiom-audit.txt 2>&1
python3 scripts/check_audit.py logs/axiom-audit.txt
python3 scripts/check_table.py paper/hyper-tamari.tex
```

Lean 4 **v4.30.0** with Mathlib **v4.30.0** (pinned in `lean-toolchain` and
`lake-manifest.json`; Mathlib revision `c5ea00351c28`). The `#print axioms` results
appear in the build output.

## Use of AI assistance

Large language models were used substantially in preparing this work, including in
writing this entire Lean development. The paper contains a section *Use of AI
assistance* stating what was and was not done by them. The point of publishing this
artifact is that the correctness of the mathematical statements does not rest on the
reliability of any language model: it rests on the Lean 4 kernel, and the evidence is
in this repository.

## License

MIT. See `LICENSE`.
