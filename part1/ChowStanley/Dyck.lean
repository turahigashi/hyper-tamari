import ChowStanley.TestFamily

/-!
# Dyck words and the Stanley order (Definition 2.5 and Proposition 4.1)

A step is `true` for an up-step `U` and `false` for a down-step `D`.

Two words are attached to a tree.  The paper's `w` is
`w (L,R) = U · w R · D · w L`; the auxiliary word of the proof of Proposition 4.1 is
`q (L,R) = q L · U · q R · D`, which is postfix notation with the initial `U` deleted.

The route taken here is the one in the paper: the height after the `j`-th up-step of
`q T` is the `(j+1)`-st right depth, so the up-step heights of `q T` are exactly
`(rseq T).tail`; and one Dyck word lies weakly below another exactly when each of its
up-steps occurs no earlier, which is the same as comparing those heights.

The proposition itself is `Tree.stDom_iff_stanleyLe`, stated in the `w` convention of
Definition 2.5.  Its four ingredients are separate declarations:

* `Tree.upHeights_eq_rseq_tail` — the height after the `j`-th up-step of `q T` is
  `r_{j+1}(T)`;
* `Tree.upPos_add_upHeights` — the arithmetic relation `p_j + e_j = 2j`;
* `Word.countP_le_iff_getElem_le` — the counting duality between prefix counts and
  up-step positions;
* `Tree.wword_eq_barW_qword` together with `Word.ht_barW` — the passage from `q` to `w`.

`Tree.hq_add_upCount` is the height/count identity `h_k + (k+1) = 2 u(k+1)` that turns
heights into counts.
-/

namespace ChowStanley

/-- A Dyck step: `true` is `U`, `false` is `D`. -/
abbrev Step := Bool

namespace Word

/-- Number of up-steps among the first `k` letters. -/
def ups (w : List Step) (k : Nat) : Nat := ((w.take k).filter id).length

/-- Height after the first `k` letters, as an integer. -/
def ht (w : List Step) (k : Nat) : Int := 2 * (ups w k) - (min k w.length)

@[simp] theorem ups_zero (w : List Step) : ups w 0 = 0 := by simp [ups]

theorem ups_le (w : List Step) (k : Nat) : ups w k ≤ min k w.length := by
  have h1 : ((w.take k).filter id).length ≤ (w.take k).length :=
    List.length_filter_le _ _
  simpa [ups, List.length_take] using h1

end Word

namespace Tree

/-- The postfix word `q T = q L · U · q R · D`. -/
def qword : Tree → List Step
  | leaf => []
  | node L R => qword L ++ (true :: (qword R ++ [false]))

/-- The paper's word `w T = U · w R · D · w L`. -/
def wword : Tree → List Step
  | leaf => []
  | node L R => true :: (wword R ++ (false :: wword L))

/-- The heights immediately after each up-step of `q T`. -/
def upHeights : Tree → List Nat
  | leaf => []
  | node L R => upHeights L ++ (1 :: (upHeights R).map (· + 1))

/-- **The key computation**: the up-step heights of `q T` are the right depths of the
leaves from the second onwards. -/
theorem upHeights_eq_rseq_tail : ∀ T : Tree, upHeights T = T.rseq.tail
  | leaf => rfl
  | node L R => by
      obtain ⟨tL, hL⟩ := rseq_cons L
      obtain ⟨tR, hR⟩ := rseq_cons R
      have ihL := upHeights_eq_rseq_tail L
      have ihR := upHeights_eq_rseq_tail R
      show upHeights L ++ (1 :: (upHeights R).map (· + 1))
          = (L.rseq ++ (R.rseq.map (· + 1))).tail
      rw [ihL, ihR, hL, hR]
      simp

theorem upHeights_length : ∀ T : Tree, (upHeights T).length + 1 = T.numLeaves := by
  intro T
  have h := upHeights_eq_rseq_tail T
  obtain ⟨t, ht⟩ := rseq_cons T
  have hl : T.rseq.length = T.numLeaves := rseq_length T
  rw [h, ht] at *
  simp at hl ⊢
  omega

end Tree
end ChowStanley

namespace ChowStanley
namespace Tree

/-- The length of the postfix word is `2(n-1)`. -/
theorem qword_length : ∀ T : Tree, T.qword.length + 2 = 2 * T.numLeaves
  | leaf => rfl
  | node L R => by
      have hL := qword_length L
      have hR := qword_length R
      have h : (node L R).qword.length
          = L.qword.length + (R.qword.length + 2) := by
        simp [qword]
      have hn : (node L R).numLeaves = L.numLeaves + R.numLeaves := rfl
      omega

/-- Positions (1-based) of the up-steps of `q T`, in order. -/
def upPos : Tree → List Nat
  | leaf => []
  | node L R =>
      upPos L ++ ((L.qword.length + 1) ::
        (upPos R).map (· + (L.qword.length + 1)))

theorem upPos_length : ∀ T : Tree, (upPos T).length = (upHeights T).length
  | leaf => rfl
  | node L R => by
      simp [upPos, upHeights, upPos_length L, upPos_length R]

theorem upPos_len_node (L R : Tree) :
    (upPos (node L R)).length = (upPos L).length + 1 + (upPos R).length := by
  simp [upPos]; omega

theorem upHeights_len_node (L R : Tree) :
    (upHeights (node L R)).length = (upHeights L).length + 1 + (upHeights R).length := by
  simp [upHeights]; omega

/-- **The arithmetic link**: after the `j`-th up-step (1-based) the height is
`2j - p_j`.  Stated as `p_j + e_j = 2j`, with `j` running over the list. -/
theorem upPos_add_upHeights : ∀ (T : Tree) (j : Nat) (h : j < (upPos T).length)
    (h' : j < (upHeights T).length),
    (upPos T)[j]'h + (upHeights T)[j]'h' = 2 * (j + 1)
  | leaf, j, h, _ => by simp [upPos] at h
  | node L R, j, h, h' => by
      have hlenL : (upPos L).length = (upHeights L).length := upPos_length L
      have hqL : L.qword.length + 2 = 2 * L.numLeaves := qword_length L
      have hnL : (upHeights L).length + 1 = L.numLeaves := upHeights_length L
      rcases Nat.lt_or_ge j (upPos L).length with hj | hj
      · -- 左の部分木の中
        have h1 : (upPos (node L R))[j]'h = (upPos L)[j]'hj := by
          simp only [upPos]; rw [List.getElem_append_left hj]
        have h2 : (upHeights (node L R))[j]'h' = (upHeights L)[j]'(by omega) := by
          simp only [upHeights]; rw [List.getElem_append_left (by omega)]
        rw [h1, h2]; exact upPos_add_upHeights L j hj (by omega)
      · rcases Nat.eq_or_lt_of_le hj with hj0 | hj1
        · -- ちょうど中央の U
          have h1 : (upPos (node L R))[j]'h = L.qword.length + 1 := by
            simp only [upPos]
            rw [List.getElem_append_right (by omega)]
            simp [← hj0]
          have h2 : (upHeights (node L R))[j]'h' = 1 := by
            simp only [upHeights]
            rw [List.getElem_append_right (by omega)]
            simp [← hj0, hlenL]
          rw [h1, h2]; omega
        · -- 右の部分木の中
          have hlenP := upPos_len_node L R
          have hlenH := upHeights_len_node L R
          have hlenL' : (upPos L).length = (upHeights L).length := upPos_length L
          obtain ⟨d, hd⟩ : ∃ d, j = (upPos L).length + 1 + d := ⟨j - (upPos L).length - 1, by omega⟩
          have hdP : d < (upPos R).length := by omega
          have hdH : d < (upHeights R).length := by
            have := upPos_length R; omega
          have h1 : (upPos (node L R))[j]'h
              = (upPos R)[d]'hdP + (L.qword.length + 1) := by
            subst hd
            show (upPos L ++ ((L.qword.length + 1) ::
                  (upPos R).map (· + (L.qword.length + 1))))[_]'_ = _
            rw [List.getElem_append_right (by omega)]
            have : (upPos L).length + 1 + d - (upPos L).length = d + 1 := by omega
            simp [this]
          have h2 : (upHeights (node L R))[j]'h'
              = (upHeights R)[d]'hdH + 1 := by
            subst hd
            show (upHeights L ++ (1 :: (upHeights R).map (· + 1)))[_]'_ = _
            rw [List.getElem_append_right (by omega)]
            have : (upPos L).length + 1 + d - (upHeights L).length = d + 1 := by omega
            simp [this]
          have ih := upPos_add_upHeights R d hdP hdH
          rw [h1, h2]
          have hqL2 : L.qword.length + 2 = 2 * L.numLeaves := qword_length L
          have hnL2 : (upHeights L).length + 1 = L.numLeaves := upHeights_length L
          omega

end Tree
end ChowStanley

namespace ChowStanley
namespace Tree

/-- Reversing a word and exchanging `U` with `D`. -/
def barW (w : List Step) : List Step := (w.map (!·)).reverse

/-- **`w T` is `q T` reversed with the two symbols exchanged** (the last step of the
proof of Proposition 4.1). -/
theorem wword_eq_barW_qword : ∀ T : Tree, wword T = barW (qword T)
  | leaf => rfl
  | node L R => by
      have ihL := wword_eq_barW_qword L
      have ihR := wword_eq_barW_qword R
      show true :: (wword R ++ (false :: wword L)) = barW (qword L ++ (true :: (qword R ++ [false])))
      rw [ihL, ihR]
      simp [barW, List.map_append, List.reverse_append]

theorem barW_length (w : List Step) : (barW w).length = w.length := by
  simp [barW]

end Tree
end ChowStanley

namespace ChowStanley
namespace Tree

/-- Every up-step position lies in `[1, |q T|]`. -/
theorem upPos_mem_bounds : ∀ (T : Tree) (x : Nat), x ∈ upPos T → 1 ≤ x ∧ x ≤ T.qword.length := by
  intro T
  induction T with
  | leaf =>
      intro x hx
      have hx' : x ∈ ([] : List Nat) := hx
      exact absurd hx' List.not_mem_nil
  | node L R ihL ihR =>
      intro x hx
      have hqn : (node L R).qword.length
          = L.qword.length + (R.qword.length + 2) := by simp [qword]
      simp only [upPos, List.mem_append, List.mem_cons, List.mem_map] at hx
      rcases hx with hL | hx
      · have := ihL x hL
        exact ⟨by omega, by omega⟩
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · exact ⟨by omega, by omega⟩
      · have := ihR y hy
        exact ⟨by omega, by omega⟩

/-- The up-step positions are strictly increasing. -/
theorem upPos_pairwise : ∀ T : Tree, (upPos T).Pairwise (· < ·)
  | leaf => by simp [upPos]
  | node L R => by
      have hL := upPos_pairwise L
      have hR := upPos_pairwise R
      set c := L.qword.length + 1 with hc
      have hmapR : ((upPos R).map (· + c)).Pairwise (· < ·) := by
        rw [List.pairwise_map]
        exact hR.imp (by intro a b h; omega)
      have hconsR : ((c :: (upPos R).map (· + c))).Pairwise (· < ·) := by
        refine List.pairwise_cons.mpr ⟨?_, hmapR⟩
        intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        have := upPos_mem_bounds R z hz
        omega
      show ((upPos L) ++ (c :: (upPos R).map (· + c))).Pairwise (· < ·)
      refine List.pairwise_append.mpr ⟨hL, hconsR, ?_⟩
      intro a ha b hb
      have hA := upPos_mem_bounds L a ha
      simp only [List.mem_cons, List.mem_map] at hb
      rcases hb with rfl | ⟨z, hz, rfl⟩
      · omega
      · have := upPos_mem_bounds R z hz; omega

end Tree
end ChowStanley

namespace ChowStanley
namespace Word

/-- `countP` of a list none of whose entries satisfy the predicate is zero.
Proved directly, because `List.countP_eq_zero` depends on `Classical.choice`. -/
theorem countP_eq_zero_of_all {k : Nat} :
    ∀ l : List Nat, (∀ x ∈ l, ¬ (x ≤ k)) → l.countP (fun x => decide (x ≤ k)) = 0
  | [], _ => rfl
  | a :: t, h => by
      have ha : ¬ (a ≤ k) := h a (List.mem_cons_self ..)
      have ht : t.countP (fun x => decide (x ≤ k)) = 0 :=
        countP_eq_zero_of_all t (fun x hx => h x (List.mem_cons_of_mem a hx))
      rw [List.countP_cons]
      simp [ha, ht]

/-- For a strictly increasing list, an entry at index `j` that is `≤ k` forces at least
`j+1` entries to be `≤ k`. -/
theorem countP_ge_of_getElem_le {k : Nat} :
    ∀ (l : List Nat), l.Pairwise (· < ·) → ∀ (j : Nat) (h : j < l.length),
      l[j] ≤ k → j + 1 ≤ l.countP (fun x => decide (x ≤ k))
  | [], _, j, h, _ => by
      have hn : ([] : List Nat).length = 0 := rfl
      have h' : j < 0 := by omega
      exact absurd h' (Nat.not_lt_zero j)
  | a :: t, hp, 0, _, ha => by
      have ha' : a ≤ k := ha
      have hc : (a :: t).countP (fun x => decide (x ≤ k))
          = t.countP (fun x => decide (x ≤ k)) + 1 := by
        simp [ha']
      omega
  | a :: t, hp, (j + 1), h, hj => by
      have hpt : t.Pairwise (· < ·) := (List.pairwise_cons.mp hp).2
      have hlc : (a :: t).length = t.length + 1 := rfl
      have hjt : j < t.length := by omega
      have hjv : t[j] ≤ k := hj
      have ih := countP_ge_of_getElem_le t hpt j hjt hjv
      have hat : a < t[j] := (List.pairwise_cons.mp hp).1 _ (List.getElem_mem hjt)
      have hak : a ≤ k := by omega
      have hc : (a :: t).countP (fun x => decide (x ≤ k))
          = t.countP (fun x => decide (x ≤ k)) + 1 := by
        simp [hak]
      omega

/-- For a strictly increasing list, an entry at index `j` that exceeds `k` bounds the
number of entries `≤ k` by `j`. -/
theorem countP_le_of_lt_getElem {k : Nat} :
    ∀ (l : List Nat), l.Pairwise (· < ·) → ∀ (j : Nat) (h : j < l.length),
      k < l[j] → l.countP (fun x => decide (x ≤ k)) ≤ j
  | [], _, j, h, _ => by
      have hn : ([] : List Nat).length = 0 := rfl
      have h' : j < 0 := by omega
      exact absurd h' (Nat.not_lt_zero j)
  | a :: t, hp, 0, _, ha => by
      have ha' : k < a := ha
      have hall : ∀ x ∈ a :: t, ¬ (x ≤ k) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · have := (List.pairwise_cons.mp hp).1 x hx
          omega
      have hz : (a :: t).countP (fun x => decide (x ≤ k)) = 0 :=
        countP_eq_zero_of_all _ hall
      omega
  | a :: t, hp, (j + 1), h, hj => by
      have hpt : t.Pairwise (· < ·) := (List.pairwise_cons.mp hp).2
      have hlc : (a :: t).length = t.length + 1 := rfl
      have hjt : j < t.length := by omega
      have hjv : k < t[j] := hj
      have ih := countP_le_of_lt_getElem t hpt j hjt hjv
      have hc : (a :: t).countP (fun x => decide (x ≤ k))
          ≤ t.countP (fun x => decide (x ≤ k)) + 1 := by
        rw [List.countP_cons]
        split <;> omega
      omega

/-- **The counting duality.**  For strictly increasing lists of the same length, the
prefix counts compare one way exactly when the entries compare the other way. -/
theorem countP_le_iff_getElem_le {p q : List Nat}
    (hp : p.Pairwise (· < ·)) (hq : q.Pairwise (· < ·)) (hlen : p.length = q.length) :
    (∀ k : Nat, p.countP (fun x => decide (x ≤ k)) ≤ q.countP (fun x => decide (x ≤ k)))
      ↔ (∀ (j : Nat) (h : j < p.length) (h' : j < q.length), q[j] ≤ p[j]) := by
  constructor
  · intro hc j h h'
    by_contra hlt
    have hpq : p[j] < q[j] := by omega
    have h1 : j + 1 ≤ p.countP (fun x => decide (x ≤ p[j])) :=
      countP_ge_of_getElem_le p hp j h (le_refl _)
    have h2 : q.countP (fun x => decide (x ≤ p[j])) ≤ j :=
      countP_le_of_lt_getElem q hq j h' hpq
    have := hc p[j]
    omega
  · intro he k
    have : ∀ x ∈ p, x ≤ k → True := fun _ _ _ => trivial
    -- 添字の像で比較する
    have key : ∀ n : Nat, n ≤ p.length →
        (p.take n).countP (fun x => decide (x ≤ k))
          ≤ (q.take n).countP (fun x => decide (x ≤ k)) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
          intro hn
          have hnp : n < p.length := by omega
          have hnq : n < q.length := by omega
          have hpt : p.take (n+1) = p.take n ++ [p[n]] := by
            rw [List.take_add_one]
            simp [List.getElem?_eq_getElem hnp]
          have hqt : q.take (n+1) = q.take n ++ [q[n]] := by
            rw [List.take_add_one]
            simp [List.getElem?_eq_getElem hnq]
          have hle := he n hnp hnq
          rw [hpt, hqt, List.countP_append, List.countP_append]
          have hstep : (List.countP (fun x => decide (x ≤ k)) [p[n]])
              ≤ (List.countP (fun x => decide (x ≤ k)) [q[n]]) := by
            by_cases hc : p[n] ≤ k
            · have : q[n] ≤ k := by omega
              simp [hc, this]
            · simp [List.countP_cons, hc]
          have := ih (by omega)
          omega
    have hp' : p.take p.length = p := by simp
    have hq' : q.take p.length = q := by rw [hlen]; simp
    have := key p.length (le_refl _)
    rwa [hp', hq'] at this

end Word
end ChowStanley

namespace ChowStanley
namespace Tree

/-- The word has twice as many letters as there are up-steps. -/
theorem qword_length_eq (T : Tree) : T.qword.length = 2 * (upPos T).length := by
  have h1 := qword_length T
  have h2 := upPos_length T
  have h3 := upHeights_length T
  omega

/-- All up-step positions of `T` are counted once the bound reaches `|q T|`. -/
theorem countP_upPos_all (T : Tree) {k : Nat} (hk : T.qword.length ≤ k) :
    (upPos T).countP (fun x => decide (x ≤ k)) = (upPos T).length := by
  rw [List.countP_eq_length]
  intro x hx
  have := upPos_mem_bounds T x hx
  simp; omega

/-- The height of `q T` after each letter. -/
def hq : Tree → List Nat
  | leaf => []
  | node L R => hq L ++ ((1 :: (hq R).map (· + 1)) ++ [0])

theorem hq_length : ∀ T : Tree, (hq T).length = T.qword.length
  | leaf => rfl
  | node L R => by
      have hL := hq_length L
      have hR := hq_length R
      have h1 : (hq (node L R)).length
          = (hq L).length + ((hq R).length + 2) := by simp [hq]
      have h2 : (node L R).qword.length
          = L.qword.length + (R.qword.length + 2) := by simp [qword]
      omega

end Tree
end ChowStanley

namespace ChowStanley
namespace Word

/-- Shifting every entry by `c` shifts the counting bound by `c`. -/
theorem countP_map_add : ∀ (l : List Nat) (c m : Nat), c ≤ m →
    (l.map (· + c)).countP (fun x => decide (x ≤ m))
      = l.countP (fun x => decide (x ≤ m - c))
  | [], _, _, _ => rfl
  | a :: t, c, m, hc => by
      have ih := countP_map_add t c m hc
      by_cases h : a + c ≤ m
      · have h2 : a ≤ m - c := by omega
        simp [h, h2, ih]
      · have h2 : ¬ (a ≤ m - c) := by omega
        simp [h, h2, ih]

/-- Entries shifted past the bound are not counted. -/
theorem countP_map_add_zero (l : List Nat) (c m : Nat) (hc : m < c) :
    (l.map (· + c)).countP (fun x => decide (x ≤ m)) = 0 := by
  refine countP_eq_zero_of_all _ ?_
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  omega

end Word
end ChowStanley

namespace ChowStanley
namespace Tree

/-- Number of up-steps of `q T` at position at most `k`; the paper's `u_T(k)`. -/
def upCount (T : Tree) (k : Nat) : Nat := (upPos T).countP (fun x => decide (x ≤ k))

theorem upCount_zero (T : Tree) : upCount T 0 = 0 := by
  refine Word.countP_eq_zero_of_all _ ?_
  intro x hx
  have := upPos_mem_bounds T x hx
  omega

theorem upCount_all (T : Tree) {k : Nat} (hk : T.qword.length ≤ k) :
    upCount T k = (upPos T).length := countP_upPos_all T hk

/-- Splitting `u` at a node: the left factor, the new up-step, and the shifted right
factor. -/
theorem upCount_node (L R : Tree) (k : Nat) :
    upCount (node L R) k
      = upCount L k
        + (if L.qword.length + 1 ≤ k then 1 else 0)
        + ((upPos R).map (· + (L.qword.length + 1))).countP (fun x => decide (x ≤ k)) := by
  unfold upCount
  show ((upPos L ++ ((L.qword.length + 1) ::
      (upPos R).map (· + (L.qword.length + 1)))).countP _) = _
  rw [List.countP_append, List.countP_cons]
  by_cases h : L.qword.length + 1 ≤ k
  · simp only [h, decide_true, if_true]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    omega

end Tree
end ChowStanley

namespace ChowStanley
namespace Tree

/-- **The height/count identity**, the arithmetic core of Proposition 4.1: after the
first `k+1` letters of `q T` the height is `2 u_T(k+1) - (k+1)`, where `u_T(m)` counts
the up-steps at position at most `m`. -/
theorem hq_add_upCount : ∀ (T : Tree) (k v : Nat), (hq T)[k]? = some v →
    v + (k + 1) = 2 * upCount T (k + 1)
  | leaf, k, v, h => by
      have hnil : (hq leaf)[k]? = none := by
        show ([] : List Nat)[k]? = none
        rfl
      rw [hnil] at h
      exact absurd h.symm (Option.some_ne_none v)
  | node L R, k, v, h => by
      have haL : (hq L).length = L.qword.length := hq_length L
      have hbR : (hq R).length = R.qword.length := hq_length R
      have hqL : L.qword.length = 2 * (upPos L).length := qword_length_eq L
      have hqR : R.qword.length = 2 * (upPos R).length := qword_length_eq R
      have hdef : hq (node L R)
          = hq L ++ (1 :: ((hq R).map (· + 1) ++ [0])) := by
        show hq L ++ ((1 :: (hq R).map (· + 1)) ++ [0]) = _
        rw [List.cons_append]
      rw [hdef] at h
      by_cases hk : k < (hq L).length
      · -- inside the left factor
        rw [List.getElem?_append_left hk] at h
        have ih := hq_add_upCount L k v h
        have hz : ((upPos R).map (· + (L.qword.length + 1))).countP
            (fun x => decide (x ≤ k + 1)) = 0 :=
          Word.countP_map_add_zero _ _ _ (by omega)
        rw [upCount_node, hz]
        have hif : (if L.qword.length + 1 ≤ k + 1 then 1 else 0) = 0 :=
          if_neg (by omega)
        rw [hif]
        omega
      · -- at or after the new up-step
        rw [List.getElem?_append_right (by omega)] at h
        have hcL : upCount L (k + 1) = (upPos L).length :=
          upCount_all L (by omega)
        cases hd : k - (hq L).length with
        | zero =>
            -- the new up-step itself
            rw [hd] at h
            have hv : v = 1 := by
              have : (1 :: ((hq R).map (· + 1) ++ [0]))[0]? = some 1 :=
                List.getElem?_cons_zero
              rw [this] at h
              exact (Option.some.inj h).symm
            have hka : k = L.qword.length := by omega
            have hshift : ((upPos R).map (· + (L.qword.length + 1))).countP
                (fun x => decide (x ≤ k + 1))
                = (upPos R).countP (fun x => decide (x ≤ (k + 1) - (L.qword.length + 1))) :=
              Word.countP_map_add _ _ _ (by omega)
            have hzero : (upPos R).countP
                (fun x => decide (x ≤ (k + 1) - (L.qword.length + 1))) = 0 := by
              have : (k + 1) - (L.qword.length + 1) = 0 := by omega
              rw [this]
              exact upCount_zero R
            rw [upCount_node, hshift, hzero, hcL]
            have hif : (if L.qword.length + 1 ≤ k + 1 then 1 else 0) = 1 :=
              if_pos (by omega)
            rw [hif]
            omega
        | succ e =>
            rw [hd] at h
            have hke : k = (hq L).length + e + 1 := by omega
            have hstep : (1 :: ((hq R).map (· + 1) ++ [0]))[e + 1]?
                = ((hq R).map (· + 1) ++ [0])[e]? := rfl
            rw [hstep] at h
            by_cases he : e < (hq R).length
            · -- inside the right factor
              have hlen : ((hq R).map (· + 1)).length = (hq R).length :=
                List.length_map _
              rw [List.getElem?_append_left (by omega), List.getElem?_map] at h
              cases hw : (hq R)[e]? with
              | none =>
                  rw [hw] at h
                  have h' : (none : Option Nat) = some v := h
                  exact absurd h'.symm (Option.some_ne_none v)
              | some w =>
                  rw [hw] at h
                  have hvw : v = w + 1 := by
                    have h' : some (w + 1) = some v := h
                    exact (Option.some.inj h').symm
                  have ih := hq_add_upCount R e w hw
                  have hshift : ((upPos R).map (· + (L.qword.length + 1))).countP
                      (fun x => decide (x ≤ k + 1))
                      = (upPos R).countP
                        (fun x => decide (x ≤ (k + 1) - (L.qword.length + 1))) :=
                    Word.countP_map_add _ _ _ (by omega)
                  have harg : (k + 1) - (L.qword.length + 1) = e + 1 := by omega
                  rw [upCount_node, hshift, harg, hcL]
                  have hif : (if L.qword.length + 1 ≤ k + 1 then 1 else 0) = 1 :=
                    if_pos (by omega)
                  rw [hif]
                  have ih' : w + (e + 1)
                      = 2 * (upPos R).countP (fun x => decide (x ≤ e + 1)) := ih
                  omega
            · -- the final down-step
              have hlen : ((hq R).map (· + 1)).length = (hq R).length :=
                List.length_map _
              rw [List.getElem?_append_right (by omega)] at h
              cases hj : e - ((hq R).map (· + 1)).length with
              | succ j =>
                  rw [hj] at h
                  have hnone : ([0] : List Nat)[j + 1]? = none := rfl
                  rw [hnone] at h
                  exact absurd h.symm (Option.some_ne_none v)
              | zero =>
                  rw [hj] at h
                  have hv : v = 0 := by
                    have h0 : ([0] : List Nat)[0]? = some 0 := List.getElem?_cons_zero
                    rw [h0] at h
                    exact (Option.some.inj h).symm
                  have hee : e = (hq R).length := by omega
                  have hkall : (node L R).qword.length ≤ k + 1 := by
                    have hq2 : (node L R).qword.length
                        = L.qword.length + (R.qword.length + 2) := by
                      show (L.qword ++ (true :: (R.qword ++ [false]))).length = _
                      rw [List.length_append, List.length_cons, List.length_append]
                      rfl
                    omega
                  have hall : upCount (node L R) (k + 1)
                      = (upPos (node L R)).length := upCount_all _ hkall
                  have hlenn := upPos_len_node L R
                  rw [hall, hlenn]
                  omega

end Tree
end ChowStanley

namespace ChowStanley
namespace Word

theorem ups_append (l₁ l₂ : List Step) (k : Nat) :
    ups (l₁ ++ l₂) k = ups l₁ k + ups l₂ (k - l₁.length) := by
  unfold ups
  rw [List.take_append, List.filter_append, List.length_append]

theorem ups_cons_true (l : List Step) (k : Nat) :
    ups (true :: l) (k + 1) = ups l k + 1 := by
  unfold ups
  rw [List.take_succ_cons]
  show ((true :: (l.take k).filter id).length) = _
  rw [List.length_cons]

theorem ups_cons_false (l : List Step) (k : Nat) :
    ups (false :: l) (k + 1) = ups l k := by
  unfold ups
  rw [List.take_succ_cons]
  rfl

theorem ups_saturate (l : List Step) {k : Nat} (h : l.length ≤ k) :
    ups l k = ups l l.length := by
  unfold ups
  rw [List.take_of_length_le h, List.take_length]

theorem ups_singleton_false (k : Nat) : ups [false] k = 0 := by
  cases k with
  | zero => rfl
  | succ j => rw [ups_cons_false]; simp [ups]

end Word
end ChowStanley

namespace ChowStanley
namespace Tree

/-- The up-step count of the postfix word is the count of up-step positions: the two
descriptions of `u_T(k)` agree. -/
theorem ups_qword_eq_upCount : ∀ (T : Tree) (k : Nat), Word.ups T.qword k = upCount T k
  | leaf, k => by
      show Word.ups [] k = ([] : List Nat).countP _
      simp [Word.ups]
  | node L R, k => by
      have ihL := ups_qword_eq_upCount L k
      have hqd : (node L R).qword = L.qword ++ (true :: (R.qword ++ [false])) := rfl
      rw [hqd, Word.ups_append, ihL, upCount_node]
      cases hk : k - L.qword.length with
      | zero =>
          have hle : k ≤ L.qword.length := by omega
          have h1 : Word.ups (true :: (R.qword ++ [false])) 0 = 0 := by simp [Word.ups]
          have h2 : ((upPos R).map (· + (L.qword.length + 1))).countP
              (fun x => decide (x ≤ k)) = 0 :=
            Word.countP_map_add_zero _ _ _ (by omega)
          have h3 : ¬ (L.qword.length + 1 ≤ k) := by omega
          rw [h1, h2]
          simp [h3]
      | succ m =>
          have hge : L.qword.length + 1 ≤ k := by omega
          have ihR := ups_qword_eq_upCount R m
          have h1 : Word.ups (true :: (R.qword ++ [false])) (m + 1)
              = upCount R m + 1 := by
            rw [Word.ups_cons_true, Word.ups_append, Word.ups_singleton_false, ihR]
          have h2 : ((upPos R).map (· + (L.qword.length + 1))).countP
              (fun x => decide (x ≤ k))
              = (upPos R).countP (fun x => decide (x ≤ k - (L.qword.length + 1))) :=
            Word.countP_map_add _ _ _ (by omega)
          have h3 : k - (L.qword.length + 1) = m := by omega
          have h4 : (if L.qword.length + 1 ≤ k then 1 else 0) = 1 := by simp [hge]
          rw [h1, h2, h3, h4]
          show upCount L k + (upCount R m + 1) = upCount L k + 1 + upCount R m
          omega

end Tree
end ChowStanley

namespace ChowStanley
namespace Tree

/-- **Definition 2.5**, read in the postfix convention: `q T` lies weakly below `q U`. -/
def qDom (T U : Tree) : Prop := ∀ k : Nat, Word.ht T.qword k ≤ Word.ht U.qword k

theorem qDom_iff_upCount {T U : Tree} (hlen : T.qword.length = U.qword.length) :
    qDom T U ↔ ∀ k, upCount T k ≤ upCount U k := by
  constructor
  · intro h k
    have hk := h k
    simp only [Word.ht, hlen] at hk
    have hT := ups_qword_eq_upCount T k
    have hU := ups_qword_eq_upCount U k
    omega
  · intro h k
    have hk := h k
    have hT := ups_qword_eq_upCount T k
    have hU := ups_qword_eq_upCount U k
    simp only [Word.ht, hlen]
    omega

theorem upPos_length_eq {T U : Tree} (hlen : T.qword.length = U.qword.length) :
    (upPos T).length = (upPos U).length := by
  have h1 := qword_length_eq T
  have h2 := qword_length_eq U
  omega

/-- The counting duality of the proof of Proposition 4.1: the prefix counts compare one
way exactly when the up-step positions compare the other way. -/
theorem upCount_le_iff_upPos {T U : Tree} (hlen : T.qword.length = U.qword.length) :
    (∀ k, upCount T k ≤ upCount U k)
      ↔ (∀ (j : Nat) (h : j < (upPos T).length) (h' : j < (upPos U).length),
          (upPos U)[j]'h' ≤ (upPos T)[j]'h) :=
  Word.countP_le_iff_getElem_le (upPos_pairwise T) (upPos_pairwise U) (upPos_length_eq hlen)

/-- `p_j + e_j = 2j` turns the comparison of positions into the comparison of heights. -/
theorem upPos_le_iff_upHeights (T U : Tree) :
    (∀ (j : Nat) (h : j < (upPos T).length) (h' : j < (upPos U).length),
        (upPos U)[j]'h' ≤ (upPos T)[j]'h)
      ↔ (∀ (j : Nat) (h : j < (upHeights T).length) (h' : j < (upHeights U).length),
        (upHeights T)[j]'h ≤ (upHeights U)[j]'h') := by
  have hlT := upPos_length T
  have hlU := upPos_length U
  constructor
  · intro hp j h h'
    have hjT : j < (upPos T).length := by omega
    have hjU : j < (upPos U).length := by omega
    have e1 := upPos_add_upHeights T j hjT h
    have e2 := upPos_add_upHeights U j hjU h'
    have := hp j hjT hjU
    omega
  · intro he j h h'
    have hjT : j < (upHeights T).length := by omega
    have hjU : j < (upHeights U).length := by omega
    have e1 := upPos_add_upHeights T j h hjT
    have e2 := upPos_add_upHeights U j h' hjU
    have := he j hjT hjU
    omega

theorem rseq_getElem_succ (T : Tree) (j : Nat) (h : j < (upHeights T).length)
    (h' : j + 1 < T.rseq.length) : (upHeights T)[j]'h = T.rseq[j + 1]'h' := by
  obtain ⟨t, ht⟩ := rseq_cons T
  have e1 : upHeights T = t := by rw [upHeights_eq_rseq_tail, ht]; rfl
  simp only [e1, ht, List.getElem_cons_succ]

theorem rseq_getElem_zero (T : Tree) (h : 0 < T.rseq.length) : T.rseq[0]'h = 0 := by
  obtain ⟨t, ht⟩ := rseq_cons T
  simp only [ht, List.getElem_cons_zero]

theorem stanleyLe_iff_upHeights {T U : Tree} (hn : T.numLeaves = U.numLeaves) :
    stanleyLe T U
      ↔ (∀ (j : Nat) (h : j < (upHeights T).length) (h' : j < (upHeights U).length),
          (upHeights T)[j]'h ≤ (upHeights U)[j]'h') := by
  have hrT : T.rseq.length = T.numLeaves := rseq_length T
  have hrU : U.rseq.length = U.numLeaves := rseq_length U
  have hhT := upHeights_length T
  have hhU := upHeights_length U
  constructor
  · rintro ⟨hl, hc⟩ j h h'
    have h1 : j + 1 < T.rseq.length := by omega
    have h2 : j + 1 < U.rseq.length := by omega
    rw [rseq_getElem_succ T j h h1, rseq_getElem_succ U j h' h2]
    exact hc (j + 1) h1 h2
  · intro he
    refine ⟨by omega, ?_⟩
    intro i h h'
    cases i with
    | zero =>
        rw [rseq_getElem_zero T h, rseq_getElem_zero U h']
    | succ j =>
        have h1 : j < (upHeights T).length := by omega
        have h2 : j < (upHeights U).length := by omega
        rw [← rseq_getElem_succ T j h1 h, ← rseq_getElem_succ U j h2 h']
        exact he j h1 h2

/-- **Proposition 4.1** (coordinate presentation).  For trees with the same number of
leaves, the Stanley order — the Dyck word of one lying weakly below that of the other —
is exactly the coordinatewise order on right depths. -/
theorem qDom_iff_stanleyLe {T U : Tree} (hn : T.numLeaves = U.numLeaves) :
    qDom T U ↔ stanleyLe T U := by
  have hlen : T.qword.length = U.qword.length := by
    have h1 := qword_length T
    have h2 := qword_length U
    omega
  rw [qDom_iff_upCount hlen, upCount_le_iff_upPos hlen, upPos_le_iff_upHeights T U,
    stanleyLe_iff_upHeights hn]

end Tree
end ChowStanley

namespace ChowStanley
namespace Word

/-- Negating every letter exchanges up-steps and down-steps. -/
theorem length_filter_map_not : ∀ l : List Step,
    ((l.map (!·)).filter id).length + (l.filter id).length = l.length
  | [] => rfl
  | a :: t => by
      have ih := length_filter_map_not t
      cases a with
      | false => simp; omega
      | true => simp; omega

theorem ups_eq_length_filter (l : List Step) : ups l l.length = (l.filter id).length := by
  unfold ups
  rw [List.take_length]

/-- The height of a word is unchanged once the whole word has been read. -/
theorem ht_saturate (w : List Step) {k : Nat} (h : w.length ≤ k) :
    ht w k = ht w w.length := by
  unfold ht
  rw [ups_saturate w h]
  have h1 : min k w.length = w.length := by omega
  have h2 : min w.length w.length = w.length := by omega
  rw [h1, h2]

/-- Splitting a word at position `m` splits the up-step count. -/
theorem ups_split (l : List Step) (m : Nat) :
    ups l m + ((l.drop m).filter id).length = ups l l.length := by
  have hsplit : ((l.take m).filter id).length + ((l.drop m).filter id).length
      = (l.filter id).length := by
    conv_rhs => rw [← List.take_append_drop m l]
    rw [List.filter_append, List.length_append]
  have h1 : ups l m = ((l.take m).filter id).length := rfl
  have h2 : ups l l.length = (l.filter id).length := ups_eq_length_filter l
  omega

theorem ups_le_ups_length (l : List Step) (m : Nat) : ups l m ≤ ups l l.length := by
  have := ups_split l m
  omega

/-- The up-steps in a suffix are at most as many as its letters. -/
theorem ups_sub_le (l : List Step) (k : Nat) :
    ups l l.length - ups l (l.length - k) ≤ l.length - (l.length - k) := by
  have hs := ups_split l (l.length - k)
  have hdrop : ((l.drop (l.length - k)).filter id).length
      ≤ (l.drop (l.length - k)).length := List.length_filter_le _ _
  have hlend : (l.drop (l.length - k)).length = l.length - (l.length - k) :=
    List.length_drop
  omega

/-- Reading `bar w` forwards is reading `w` backwards. -/
theorem ups_barW (w : List Step) (k : Nat) :
    ups (Tree.barW w) k
      = (w.length - (w.length - k)) - (ups w w.length - ups w (w.length - k)) := by
  have hm : (w.map (!·)).length = w.length := List.length_map _
  have h1 : (Tree.barW w).take k = ((w.drop (w.length - k)).map (!·)).reverse := by
    show ((w.map (!·)).reverse).take k = _
    rw [List.take_reverse, hm, ← List.map_drop]
  have h3 : ups (Tree.barW w) k
      = (((w.drop (w.length - k)).map (!·)).filter id).length := by
    unfold ups
    rw [h1, List.filter_reverse, List.length_reverse]
  have hnot := length_filter_map_not (w.drop (w.length - k))
  have hlend : (w.drop (w.length - k)).length = w.length - (w.length - k) :=
    List.length_drop
  have hs := ups_split w (w.length - k)
  rw [h3]
  omega

/-- **The reversal identity** of the proof of Proposition 4.1: for a balanced word,
the height of `bar w` after `k` letters is the height of `w` after `|w| - k`. -/
theorem ht_barW (w : List Step) (hbal : w.length = 2 * ups w w.length) (k : Nat) :
    ht (Tree.barW w) k = ht w (w.length - k) := by
  have hlen : (Tree.barW w).length = w.length := Tree.barW_length w
  have hups := ups_barW w k
  have hle := ups_le_ups_length w (w.length - k)
  have hsub := ups_sub_le w k
  unfold ht
  rw [hlen, hups]
  omega

end Word
end ChowStanley

namespace ChowStanley
namespace Tree

/-- `q T` is a balanced word: half of its letters are up-steps. -/
theorem qword_balanced (T : Tree) :
    T.qword.length = 2 * Word.ups T.qword T.qword.length := by
  have h1 := ups_qword_eq_upCount T T.qword.length
  have h2 := upCount_all T (Nat.le_refl T.qword.length)
  have h3 := qword_length_eq T
  omega

/-- **Definition 2.5** exactly as stated in the paper, in the `w` convention. -/
def stDom (T U : Tree) : Prop := ∀ k : Nat, Word.ht T.wword k ≤ Word.ht U.wword k

theorem ht_wword (T : Tree) (k : Nat) :
    Word.ht T.wword k = Word.ht T.qword (T.qword.length - k) := by
  rw [wword_eq_barW_qword T]
  exact Word.ht_barW _ (qword_balanced T) k

/-- The two conventions define the same order. -/
theorem stDom_iff_qDom {T U : Tree} (hlen : T.qword.length = U.qword.length) :
    stDom T U ↔ qDom T U := by
  constructor
  · intro h m
    by_cases hm : m ≤ T.qword.length
    · have hk := h (T.qword.length - m)
      rw [ht_wword T, ht_wword U, ← hlen] at hk
      have e : T.qword.length - (T.qword.length - m) = m := by omega
      rw [e] at hk
      exact hk
    · have h0 := h 0
      rw [ht_wword T, ht_wword U, ← hlen] at h0
      have e : T.qword.length - 0 = T.qword.length := by omega
      rw [e] at h0
      have s1 : Word.ht T.qword m = Word.ht T.qword T.qword.length :=
        Word.ht_saturate _ (by omega)
      have s2 : Word.ht U.qword m = Word.ht U.qword U.qword.length :=
        Word.ht_saturate _ (by omega)
      rw [s1, s2, ← hlen]
      exact h0
  · intro h k
    rw [ht_wword T, ht_wword U, ← hlen]
    exact h _

/-- **Proposition 4.1**, exactly as stated in the paper: for trees with the same number
of leaves, `T ≤_St U` (the Dyck word of `T` lies weakly below that of `U`) if and only if
`r_i(T) ≤ r_i(U)` for every `i`. -/
theorem stDom_iff_stanleyLe {T U : Tree} (hn : T.numLeaves = U.numLeaves) :
    stDom T U ↔ stanleyLe T U := by
  have hlen : T.qword.length = U.qword.length := by
    have h1 := qword_length T
    have h2 := qword_length U
    omega
  rw [stDom_iff_qDom hlen, qDom_iff_stanleyLe hn]

end Tree
end ChowStanley
