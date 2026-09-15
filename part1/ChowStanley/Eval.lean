import ChowStanley.Bridge

/-!
# Evaluation at an assignment

`Tree.ev T as` evaluates `T` with the leaf values taken from `as`, left to right.  The
point of this file is `Tree.ev_set`:

  evaluating `T` at the assignment "leaf `i` carries `t`, every other leaf carries `2`"
  gives exactly `PTree.val (T.points[i]) t`,

so the separation theorem of `ChowStanley.PTree` really is a statement about the
evaluation order, and not merely about the auxiliary function `PTree.val`.
-/

namespace ChowStanley
namespace Tree

/-- Evaluate `T`, consuming leaf values from the front of `as`; returns the value
together with the unconsumed remainder.  (A missing value defaults to `2`; this branch
is never taken below, where `as` is always long enough.) -/
def evAux : Tree → List Nat → Nat × List Nat
  | leaf,     []          => (2, [])
  | leaf,     (a :: rest) => (a, rest)
  | node L R, as =>
      let p := L.evAux as
      let q := R.evAux p.2
      (p.1 ^ q.1, q.2)

/-- The value of `T` at the assignment `as`. -/
def ev (T : Tree) (as : List Nat) : Nat := (T.evAux as).1

/-- Reading `T`'s leaves off an all-`2` prefix returns the all-`2` value and leaves the
rest of the list untouched. -/
theorem evAux_replicate : ∀ (T : Tree) (rest : List Nat),
    T.evAux (List.replicate T.numLeaves 2 ++ rest) = (T.two, rest)
  | leaf, rest => by simp [evAux, numLeaves, two]
  | node L R, rest => by
      have hsplit : List.replicate (L.numLeaves + R.numLeaves) (2:Nat)
          = List.replicate L.numLeaves 2 ++ List.replicate R.numLeaves 2 :=
        List.replicate_append_replicate.symm
      simp only [numLeaves, hsplit, List.append_assoc, evAux]
      rw [evAux_replicate L (List.replicate R.numLeaves 2 ++ rest)]
      rw [evAux_replicate R rest]
      simp [two]

/-- The `i`th pointed tree of a node, when `i` lies in the left factor. -/
theorem points_getElem_left (L R : Tree) (i : Nat) (hi : i < L.points.length)
    (h : i < (node L R).points.length) :
    (node L R).points[i]'h = PTree.left (L.points[i]'hi) R := by
  simp only [points] at h ⊢
  rw [List.getElem_append_left (by simpa using hi)]
  simp

/-- The `i`th pointed tree of a node, when `i` lies in the right factor. -/
theorem points_getElem_right (L R : Tree) (i : Nat) (hL : L.points.length ≤ i)
    (hi : i - L.points.length < R.points.length) (h : i < (node L R).points.length) :
    (node L R).points[i]'h = PTree.right L (R.points[i - L.points.length]'hi) := by
  simp only [points] at h ⊢
  rw [List.getElem_append_right (by simpa using hL)]
  simp

/-- **Evaluation at a one-leaf-enlarged assignment.**  Reading `T` off the list
`(replicate n 2).set i t ++ rest` returns `PTree.val (T.points[i]) t`. -/
theorem evAux_set : ∀ (T : Tree) (i t : Nat) (hi : i < T.numLeaves) (rest : List Nat),
    T.evAux ((List.replicate T.numLeaves 2).set i t ++ rest)
      = ((T.points[i]'(by simpa using hi)).val t, rest)
  | leaf, i, t, hi, rest => by
      have : i = 0 := by simp [numLeaves] at hi; omega
      subst this
      simp [evAux, numLeaves, points, PTree.val]
  | node L R, i, t, hi, rest => by
      have hsplit : List.replicate (L.numLeaves + R.numLeaves) (2:Nat)
          = List.replicate L.numLeaves 2 ++ List.replicate R.numLeaves 2 :=
        List.replicate_append_replicate.symm
      have hlenL : (List.replicate L.numLeaves (2:Nat)).length = L.numLeaves := by simp
      have hpL : L.points.length = L.numLeaves := points_length L
      have hpR : R.points.length = R.numLeaves := points_length R
      rcases Nat.lt_or_ge i L.numLeaves with hlt | hge
      · -- 左の因子に入る場合
        have hset : ((List.replicate L.numLeaves (2:Nat)
              ++ List.replicate R.numLeaves 2).set i t)
            = (List.replicate L.numLeaves 2).set i t ++ List.replicate R.numLeaves 2 :=
          List.set_append_left i t (by simpa using hlt)
        simp only [numLeaves, hsplit, hset, List.append_assoc, evAux]
        rw [evAux_set L i t hlt (List.replicate R.numLeaves 2 ++ rest)]
        rw [evAux_replicate R rest]
        have hp : (node L R).points[i]'(by simpa [numLeaves] using hi)
            = PTree.left (L.points[i]'(by omega)) R :=
          points_getElem_left L R i (by omega) _
        simp [hp, PTree.val]
      · -- 右の因子に入る場合
        have hlt' : i - L.numLeaves < R.numLeaves := by
          simp [numLeaves] at hi; omega
        have hset : ((List.replicate L.numLeaves (2:Nat)
              ++ List.replicate R.numLeaves 2).set i t)
            = List.replicate L.numLeaves 2
              ++ (List.replicate R.numLeaves 2).set (i - L.numLeaves) t := by
          have h := List.set_append_right (s := List.replicate L.numLeaves (2:Nat))
            (t := List.replicate R.numLeaves (2:Nat)) i t (by simpa using hge)
          simpa using h
        simp only [numLeaves, hsplit, hset, List.append_assoc, evAux]
        rw [evAux_replicate L
              ((List.replicate R.numLeaves 2).set (i - L.numLeaves) t ++ rest)]
        rw [evAux_set R (i - L.numLeaves) t hlt' rest]
        have hp : (node L R).points[i]'(by simpa [numLeaves] using hi)
            = PTree.right L (R.points[i - L.points.length]'(by omega)) :=
          points_getElem_right L R i (by omega) (by omega) _
        simp [hp, PTree.val, hpL]

/-- **Corollary.**  `T` evaluated at "leaf `i` carries `t`, every other leaf carries `2`"
is `PTree.val (T.points[i]) t`. -/
theorem ev_set (T : Tree) (i t : Nat) (hi : i < T.numLeaves) :
    T.ev ((List.replicate T.numLeaves 2).set i t)
      = (T.points[i]'(by simpa using hi)).val t := by
  have := evAux_set T i t hi []
  simp only [List.append_nil] at this
  simp [ev, this]

end Tree
end ChowStanley
