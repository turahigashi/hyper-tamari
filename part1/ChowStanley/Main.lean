import ChowStanley.Eval

/-!
# The main theorem

`Tree.evalLe T U` is the evaluation order: `T ≤ U` when `T` is at most `U` at **every**
assignment of values `≥ 2` to the leaves.  `Tree.stanleyLe` is the Stanley order in the
right-depth coordinates of Proposition 4.1.

`Tree.not_evalLe_of_rdepth_lt` is the half of the main theorem that was open: a
violation of the coordinate order is realised at an explicit assignment, and
`Tree.stanleyLe_of_evalLe` concludes `evalLe → stanleyLe`.

The converse `stanleyLe → evalLe` is the inclusion proved by Chow in 2018 (Rubey
independently reduced it to a single inequality).  It is **not** proved in this
development.  This development proves that the Stanley order is the reflexive-transitive
closure of its covers (`Tree.stanleyLe_iff_reflTransGen_stRot`, in `Cover.lean`); the
Part II development proves that evaluation does not decrease along such a chain
(`StRot.eval_le_rank3_star`, on labelled trees); the join between the two tree types is
made on paper, so no equivalence `evalLe ↔ stanleyLe` is stated here.
-/

namespace ChowStanley
namespace Tree

/-- The evaluation order: `T ≤ U` when `T` is at most `U` at every assignment of values
`≥ 2` to the leaves. -/
def evalLe (T U : Tree) : Prop :=
  ∀ as : List Nat, as.length = T.numLeaves → (∀ x ∈ as, 2 ≤ x) → T.ev as ≤ U.ev as

/-- The Stanley order in right-depth coordinates (Proposition 4.1). -/
def stanleyLe (T U : Tree) : Prop :=
  T.rseq.length = U.rseq.length ∧
  ∀ (i : Nat) (h : i < T.rseq.length) (h' : i < U.rseq.length),
    T.rseq[i]'h ≤ U.rseq[i]'h'

/-- The explicit separating assignment of Theorem 1.2: leaf `i` carries `M`, every other
leaf carries `2`. -/
def sepAssign (n i M : Nat) : List Nat := (List.replicate n 2).set i M

@[simp] theorem sepAssign_length (n i M : Nat) : (sepAssign n i M).length = n := by
  simp [sepAssign]

theorem two_le_of_mem_sepAssign {n i M : Nat} (hM : 2 ≤ M) :
    ∀ x ∈ sepAssign n i M, 2 ≤ x := by
  intro x hx
  have := List.mem_or_eq_of_mem_set hx
  rcases this with h | h
  · have := List.eq_of_mem_replicate h; omega
  · omega

/-- **The new half of the main theorem.**  If the `i`th right depth of `U` is strictly
smaller than that of `T`, then `T` exceeds `U` at the explicit assignment that puts
`M = 2 K²` on leaf `i` and `2` on every other leaf.  In particular `¬ evalLe T U`. -/
theorem not_evalLe_of_rdepth_lt {T U : Tree} {i : Nat}
    (hn : T.numLeaves = U.numLeaves) (hiT : i < T.numLeaves)
    (h : (U.points[i]'(by simpa [points_length, hn] using hiT)).rdepth
          < (T.points[i]'(by simpa [points_length] using hiT)).rdepth) :
    ¬ evalLe T U := by
  set Q := U.points[i]'(by simpa [points_length, hn] using hiT) with hQ
  set M := 2 * Q.K ^ 2 with hM
  have hK : 1 ≤ Q.K := Q.one_le_K
  have hKsq : 1 ≤ Q.K ^ 2 := by
    calc (1:Nat) = 1 ^ 2 := by omega
      _ ≤ Q.K ^ 2 := Nat.pow_le_pow_left hK 2
  have h2M : 2 ≤ M := by omega
  intro hle
  have hlen : (sepAssign T.numLeaves i M).length = T.numLeaves := by simp
  have hmem := two_le_of_mem_sepAssign (n := T.numLeaves) (i := i) (M := M) h2M
  have hcmp := hle _ hlen hmem
  -- 左辺と右辺をそれぞれ PTree.val に書き換える
  have hT : T.ev (sepAssign T.numLeaves i M)
      = (T.points[i]'(by simpa [points_length] using hiT)).val M := ev_set T i M hiT
  have hU : U.ev (sepAssign T.numLeaves i M) = Q.val M := by
    rw [hn]; exact ev_set U i M (by omega)
  rw [hT, hU] at hcmp
  exact absurd hcmp (Nat.not_le.mpr (PTree.separation h))

/-- **Main theorem, the half that was open.**  If `T ≤ U` in the evaluation order and the
two trees have the same number of leaves, then `T ≤ U` in the Stanley order. -/
theorem stanleyLe_of_evalLe {T U : Tree}
    (hn : T.numLeaves = U.numLeaves) (hle : evalLe T U) : stanleyLe T U := by
  refine ⟨by simp [rseq_length, hn], ?_⟩
  intro i h h'
  by_contra hcon
  have hlt : U.rseq[i]'h' < T.rseq[i]'h := by omega
  have hiT : i < T.numLeaves := by simpa [rseq_length] using h
  have hpT : (T.points[i]'(by simpa [points_length] using hiT)).rdepth = T.rseq[i]'h :=
    rdepth_points_getElem T i _
  have hpU : (U.points[i]'(by simpa [points_length, hn] using hiT)).rdepth = U.rseq[i]'h' :=
    rdepth_points_getElem U i _
  exact not_evalLe_of_rdepth_lt hn hiT (by rw [hpT, hpU]; exact hlt) hle

end Tree
end ChowStanley
