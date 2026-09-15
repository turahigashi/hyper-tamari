import ChowStanley.Pointed

/-!
# From trees to pointed trees

`Tree.points T` lists the `T.numLeaves` ways of choosing a hole in `T`, in the same
left-to-right order as the leaves.  The bridge lemma

  `Tree.points_map_rdepth : (T.points).map PTree.rdepth = T.rseq`

says that the `i`th pointed tree has right depth exactly the `i`th entry of the
right-depth sequence, so the separation theorem of `ChowStanley.PTree` can be stated in
terms of `rseq`.

`Tree.rseq` is the coordinate presentation of the Stanley order (Proposition 4.1); that
identification is due to Knuth (exercise 28 of the draft of §7.2.1.6 of *The Art of
Computer Programming*), to Csákány and Waldhauser (2.8 of *Associative spectra of binary
operations*), and to Lehtonen and Waldhauser (§2.5 of *Associative spectra of graph
algebras I*).  It is **not** formalised here; what is formalised is the arithmetic that
was open, namely that a violation of the coordinate order is realised by an explicit
assignment.
-/

namespace ChowStanley
namespace Tree

/-- The ways of choosing a hole in `T`, in left-to-right leaf order. -/
def points : Tree → List PTree
  | leaf => [PTree.hole]
  | node L R =>
      L.points.map (fun P => PTree.left P R) ++ R.points.map (fun P => PTree.right L P)

@[simp] theorem points_length : ∀ T : Tree, T.points.length = T.numLeaves
  | leaf => rfl
  | node L R => by simp [points, numLeaves, points_length L, points_length R]

/-- Every pointed tree in `T.points` has `T` as its underlying tree. -/
theorem mem_points_tree : ∀ (T : Tree) (P : PTree), P ∈ T.points → P.tree = T
  | leaf, P, hP => by simpa [points] using congrArg PTree.tree (by simpa [points] using hP)
  | node L R, P, hP => by
      simp only [points, List.mem_append, List.mem_map] at hP
      rcases hP with ⟨Q, hQ, rfl⟩ | ⟨Q, hQ, rfl⟩
      · simp [PTree.tree, mem_points_tree L Q hQ]
      · simp [PTree.tree, mem_points_tree R Q hQ]

/-- **Bridge lemma**: the right depths of the pointed trees of `T`, read left to right,
are exactly the right-depth sequence of `T`. -/
theorem points_map_rdepth : ∀ T : Tree, T.points.map PTree.rdepth = T.rseq
  | leaf => rfl
  | node L R => by
      simp [points, rseq, List.map_append, List.map_map, Function.comp_def,
            PTree.rdepth, points_map_rdepth L, ← points_map_rdepth R]

/-- The right depth of the `i`th pointed tree is the `i`th entry of `rseq`. -/
theorem rdepth_points_getElem (T : Tree) (i : Nat) (h : i < T.points.length) :
    (T.points[i]'h).rdepth = T.rseq[i]'(by
      have := points_map_rdepth T
      have hl : T.rseq.length = T.points.length := by
        rw [← this]; simp
      omega) := by
  have hmap := points_map_rdepth T
  have : (T.points.map PTree.rdepth)[i]'(by simpa using h) = T.rseq[i]'(by
      have hl : T.rseq.length = T.points.length := by rw [← hmap]; simp
      omega) := by
    simp [hmap]
  simpa using this

end Tree

/-- **The new half of the main theorem, in tree terms.**
If the `i`th right depth of `U` is strictly smaller than that of `T`, then `T` is
strictly larger at an explicit assignment: the `i`th leaf carries
`M = 2 * (K of the `i`th pointed tree of `U`)²` and every other leaf carries `2`.
Consequently `T ≤ U` fails in the evaluation order. -/
theorem not_le_of_rseq_lt {T U : Tree} {i : Nat}
    (hT : i < T.points.length) (hU : i < U.points.length)
    (h : (U.points[i]'hU).rdepth < (T.points[i]'hT).rdepth) :
    ∃ M : Nat, 2 ≤ M ∧ (U.points[i]'hU).val M < (T.points[i]'hT).val M := by
  set Q := U.points[i]'hU
  refine ⟨2 * Q.K ^ 2, ?_, PTree.separation h⟩
  have hK : 1 ≤ Q.K := Q.one_le_K
  have : 1 ≤ Q.K ^ 2 := by
    calc (1:Nat) = 1 ^ 2 := by omega
      _ ≤ Q.K ^ 2 := Nat.pow_le_pow_left hK 2
  omega

end ChowStanley
