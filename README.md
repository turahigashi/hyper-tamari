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

**The main result is a complete classification of the equality cases.**
For `x, y ≥ 2`:

```
r  = 3 :   equality  ⟺  z = 1  or  (y,z) = (2,2)
r ≥ 4 :   equality  ⟺  z = 1
```

So rank 3 carries **exactly one** non-trivial collision — already visible with four
leaves, where the Tamari cover `((aa)a)a ⋖ (aa)(aa)` has equal endpoints — and from
rank 4 onwards the evaluation is strictly increasing along every such cover. The
mechanism is identified: the collapsing law `(x^y)^z = x^{yz}`, which produces the
rank-3 equality, has no analogue at rank 4 or above.

The statement is not an asymptotic triviality: the two sides compare a growing first
argument against a growing second one, and small arguments do not blow up with the
rank, since `H_r(2,2) = 4` for every `r ≥ 2`. The hypothesis `y ≥ 2` is sharp at
every rank — for `y = 1` the inequality reverses.

## Contents

| Path | Lines | Contents |
|---|---:|---|
| `HyperTamari/Basic.lean` | 329 | `hyper`, verification of the conventions, the complete rank-3 analysis, `BTree` / `eval` / the rotation relation `Rot` |
| `HyperTamari/Tetration.lean` | 523 | rank 4 (tetration): `tet_ht`, strictness, the dichotomy |
| `HyperTamari/General.lean` | 517 | general rank: `sum_lemma`, `ht_general`, `equality_classification` |
| `logs/axiom-audit.txt` | — | raw `lake build` output recording the axiom audit |
| `paper/` | — | the paper (LaTeX source and PDF) |

Section 7 of the paper (*The Lean development*) maps every numbered statement of the
paper to a named declaration here.

## Audit

Measured, not asserted (`logs/axiom-audit.txt` is the raw evidence):

- `lake build` exits 0.
- **77** theorems and lemmas; **77** audited with `#print axioms`; **0** missing.
  Coverage is checked mechanically by comparing declaration names against the audit
  output.
- **No `sorryAx`.** No `sorry`, no `native_decide`, no private `axiom`, no
  `ofReduceBool`.
- Axiom dependencies: `propext` alone (2), `propext, Quot.sound` (45),
  `propext, Classical.choice, Quot.sound` (30). The uses of choice come from
  standard library lemmas about `Nat` and are not essential to the arguments.

## Building

```bash
lake exe cache get
lake build
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
