import ChowStanley.Main

/-!
# Non-degeneracy witnesses

The separation theorem would be worthless if no pair of trees ever satisfied its
hypothesis.  This file exhibits concrete instances and checks, by kernel computation,
that the numbers agree with the ones printed in the paper.

* `rseq_four_leaves` reproduces the table of Example 4.3.
* `knuth_fig41_agrees` checks our right-depth vectors for five leaves, shifted by
  `c_j = r_{j+1} - 1` (Knuth's depth coordinates `c_j`), against the fourteen depth
  sequences printed in Fig. 41 of the
  draft of §7.2.1.6 of *The Art of Computer Programming*.
* `sep_512` and `sep_128` are the two separations of Example 15.1, with the thresholds
  `512` and `128` obtained from `K = 16` and `K = 8` exactly as in the paper.

Every proof here is by `decide`, so none of them depends on any axiom.
-/

namespace ChowStanley

/-- Auxiliary enumeration with fuel, so the recursion is structural. -/
def allTreesAux : Nat → Nat → List Tree
  | 0, _ => []
  | (_ + 1), 0 => [Tree.leaf]
  | (fuel + 1), (n + 1) =>
      (List.range (n + 1)).flatMap (fun k =>
        (allTreesAux fuel k).flatMap (fun L =>
          (allTreesAux fuel (n - k)).map (fun R => Tree.node L R)))

/-- All binary trees with `n + 1` leaves. -/
def allTrees (n : Nat) : List Tree := allTreesAux (n + 1) n

theorem allTrees_card_four : (allTrees 3).length = 5 := by decide
theorem allTrees_card_five : (allTrees 4).length = 14 := by decide

/-- Example 4.3: the five right-depth vectors for four leaves. -/
theorem rseq_four_leaves :
    (allTrees 3).map Tree.rseq
      = [[0,1,2,3], [0,1,2,2], [0,1,1,2], [0,1,2,1], [0,1,1,1]] := by decide

/-- Knuth's Fig. 41: the Stanley lattice of order 4, each forest given by its sequence of
node depths in preorder. -/
def knuthFig41 : List (List Nat) :=
  [[0,1,2,3], [0,1,2,2],
   [0,1,1,2], [0,1,2,1],
   [0,0,1,2], [0,1,1,1], [0,1,2,0],
   [0,0,1,1], [0,1,0,1], [0,1,1,0],
   [0,0,0,1], [0,0,1,0], [0,1,0,0],
   [0,0,0,0]]

/-- Our right-depth vectors for five leaves, shifted by `c_j = r_{j+1} - 1`. -/
def shiftedFive : List (List Nat) :=
  (allTrees 4).map (fun T => (T.rseq.drop 1).map (· - 1))

/-- The two lists of Fig. 41 and `shiftedFive` have the same fourteen elements. -/
theorem knuth_fig41_agrees :
    shiftedFive.length = 14 ∧ knuthFig41.length = 14 ∧
    (∀ x ∈ shiftedFive, x ∈ knuthFig41) ∧ (∀ x ∈ knuthFig41, x ∈ shiftedFive) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ### The incomparable pair of Example 4.3 -/

/-- `((ab)(cd))`. -/
def T4 : Tree := Tree.node (Tree.node Tree.leaf Tree.leaf) (Tree.node Tree.leaf Tree.leaf)
/-- `((a(bc))d)`. -/
def U4 : Tree := Tree.node (Tree.node Tree.leaf (Tree.node Tree.leaf Tree.leaf)) Tree.leaf

theorem T4_rseq : T4.rseq = [0,1,1,2] := by decide
theorem U4_rseq : U4.rseq = [0,1,2,1] := by decide

/-- The two vectors differ in both directions, so the trees are Stanley-incomparable. -/
theorem T4_U4_incomparable :
    (∃ i, ∃ h : i < T4.rseq.length, ∃ h' : i < U4.rseq.length,
        U4.rseq[i]'h' < T4.rseq[i]'h) ∧
    (∃ i, ∃ h : i < T4.rseq.length, ∃ h' : i < U4.rseq.length,
        T4.rseq[i]'h < U4.rseq[i]'h') := by
  constructor
  · exact ⟨3, by decide, by decide, by decide⟩
  · exact ⟨2, by decide, by decide, by decide⟩

theorem T4_points_length : T4.points.length = 4 := by decide
theorem U4_points_length : U4.points.length = 4 := by decide

/-- At the fourth leaf, `U4` has right depth 1 and `T4` has right depth 2. -/
theorem depths_at_three :
    (U4.points[3]'(by decide)).rdepth = 1 ∧ (T4.points[3]'(by decide)).rdepth = 2 := by
  refine ⟨by decide, by decide⟩

/-- The constant `K` of Definition 6.1 for the fourth leaf of `U4` is 16, so the
threshold of Theorem 1.2 is `2 * 16² = 512`, exactly as printed in Example 15.1. -/
theorem K_at_three : (U4.points[3]'(by decide)).K = 16 := by decide

/-- **Example 15.1, first separation.** -/
theorem sep_512 :
    (U4.points[3]'(by decide)).val 512 < (T4.points[3]'(by decide)).val 512 := by
  have h : (U4.points[3]'(by decide)).rdepth < (T4.points[3]'(by decide)).rdepth := by
    decide
  have hK : 2 * (U4.points[3]'(by decide)).K ^ 2 = 512 := by decide
  have hsep := PTree.separation h
  rwa [hK] at hsep

/-- The constant `K` for the third leaf of `T4` is 8, so the threshold is `2 * 8² = 128`. -/
theorem K_at_two : (T4.points[2]'(by decide)).K = 8 := by decide

/-- **Example 15.1, second separation** (the other direction). -/
theorem sep_128 :
    (T4.points[2]'(by decide)).val 128 < (U4.points[2]'(by decide)).val 128 := by
  have h : (T4.points[2]'(by decide)).rdepth < (U4.points[2]'(by decide)).rdepth := by
    decide
  have hK : 2 * (T4.points[2]'(by decide)).K ^ 2 = 128 := by decide
  have hsep := PTree.separation h
  rwa [hK] at hsep

/-! ### The evaluation function computes, and the order is not vacuous -/

namespace Tree

/-- `ev` really is exponentiation read left-to-right. -/
theorem ev_node_leaf_leaf : (Tree.node Tree.leaf Tree.leaf).ev [3, 4] = 81 := by decide

theorem ev_T4 : T4.ev [2,3,2,2] = 4096 := by decide
theorem ev_U4 : U4.ev [2,3,2,2] = 262144 := by decide

/-- The separating assignment really is "all `2` except one entry". -/
theorem sepAssign_example : sepAssign 4 3 512 = [2,2,2,512] := by decide

/-- `ev_set` checked numerically at a value small enough to compute. -/
theorem ev_set_check :
    T4.ev (sepAssign 4 3 4) = (T4.points[3]'(by decide)).val 4 ∧
    U4.ev (sepAssign 4 3 4) = (U4.points[3]'(by decide)).val 4 ∧
    T4.ev (sepAssign 4 3 4) = 4294967296 ∧
    U4.ev (sepAssign 4 3 4) = 65536 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The evaluation order is reflexive, so it is not the empty relation. -/
theorem evalLe_refl (T : Tree) : evalLe T T := fun _ _ _ => Nat.le_refl _

theorem T4_numLeaves : T4.numLeaves = 4 := by decide
theorem U4_numLeaves : U4.numLeaves = 4 := by decide

/-- **`T4` is not below `U4`** in the evaluation order. -/
theorem not_evalLe_T4_U4 : ¬ evalLe T4 U4 := by
  refine not_evalLe_of_rdepth_lt (i := 3) (by decide) (by decide) ?_
  decide

/-- **`U4` is not below `T4`** either: the two are incomparable. -/
theorem not_evalLe_U4_T4 : ¬ evalLe U4 T4 := by
  refine not_evalLe_of_rdepth_lt (i := 2) (by decide) (by decide) ?_
  decide

/-- The two trees of Example 4.3 are incomparable in the evaluation order, so the main
theorem is not vacuous: its hypothesis is satisfiable and its conclusion has content. -/
theorem T4_U4_evalIncomparable : ¬ evalLe T4 U4 ∧ ¬ evalLe U4 T4 :=
  ⟨not_evalLe_T4_U4, not_evalLe_U4_T4⟩

/-- They are incomparable in the Stanley order as well, so
`stanleyLe_of_evalLe` is asserting something at this pair and not merely
restating a truth. -/
theorem not_stanleyLe_T4_U4 : ¬ stanleyLe T4 U4 := by
  rintro ⟨-, h⟩
  have h3 := h 3 (by decide) (by decide)
  revert h3
  decide

theorem not_stanleyLe_U4_T4 : ¬ stanleyLe U4 T4 := by
  rintro ⟨-, h⟩
  have h2 := h 2 (by decide) (by decide)
  revert h2
  decide

/-- `stanleyLe` is reflexive, so it too is not the empty relation. -/
theorem stanleyLe_refl (T : Tree) : stanleyLe T T := ⟨rfl, fun _ _ _ => Nat.le_refl _⟩

end Tree
end ChowStanley
