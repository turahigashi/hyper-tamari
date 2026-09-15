import ChowStanley.Dyck

/-!
# The Stanley covers (Lemma 4.4)

`T ⋖ U` in the Stanley order exactly when `w U` is obtained from `w T` by replacing one
occurrence of `DU` by `UD`.  The proof runs through the right-depth coordinates: a cover
is exactly a step that raises one coordinate by one.

The ingredient the printed proof does not need, and which is supplied here, is that the
raised sequence is again the sequence of a tree.  It is produced by surgery on `T`
itself (`Tree.raise`), whose boundary case is the move of Lemma 4.5,
`node (node A B) R ↦ node A (graftLeft B R)`.
-/

namespace ChowStanley
namespace Tree

theorem rseq_length_pos (T : Tree) : 0 < (rseq T).length := by
  obtain ⟨t, ht⟩ := rseq_cons T
  rw [ht]
  exact Nat.succ_pos _

/-- Graft `B` onto the leftmost leaf `c` of `R`, so that `c` becomes `B · c`.  Every tree
factors along its leftmost leaf, so this is the operation of Lemma 4.5. -/
def graftLeft (B : Tree) : Tree → Tree
  | leaf => node B leaf
  | node P Q => node (graftLeft B P) Q

theorem rseq_graftLeft (B : Tree) : ∀ R : Tree,
    rseq (graftLeft B R) = rseq B ++ (1 :: (rseq R).tail)
  | leaf => by
      show rseq B ++ (rseq leaf).map (· + 1) = _
      rfl
  | node P Q => by
      have ih := rseq_graftLeft B P
      obtain ⟨t, ht⟩ := rseq_cons P
      show rseq (graftLeft B P) ++ (rseq Q).map (· + 1)
          = rseq B ++ (1 :: (rseq P ++ (rseq Q).map (· + 1)).tail)
      rw [ih, ht]
      simp

/-- Indexing the sequence of a node. -/
theorem rseq_node_getElem? (L R : Tree) (i : Nat) :
    (rseq (node L R))[i]?
      = if i < (rseq L).length then (rseq L)[i]?
        else ((rseq R)[i - (rseq L).length]?).map (· + 1) := by
  show (rseq L ++ (rseq R).map (· + 1))[i]? = _
  by_cases h : i < (rseq L).length
  · rw [List.getElem?_append_left h, if_pos h]
  · rw [List.getElem?_append_right (by omega), if_neg h, List.getElem?_map]

theorem rseq_head_getElem? (T : Tree) : (rseq T)[0]? = some 0 := by
  obtain ⟨t, ht⟩ := rseq_cons T
  rw [ht]
  rfl

/-- The right depths of consecutive leaves grow by at most one. -/
theorem rseq_step : ∀ (T : Tree) {i x y : Nat},
    (rseq T)[i + 1]? = some x → (rseq T)[i]? = some y → x ≤ y + 1
  | leaf, i, x, y, hx, _ => by
      have : (rseq leaf)[i + 1]? = none := by
        show ([0] : List Nat)[i + 1]? = none
        cases i <;> rfl
      rw [this] at hx
      exact absurd hx.symm (Option.some_ne_none x)
  | node L R, i, x, y, hx, hy => by
      have hLpos := rseq_length_pos L
      rw [rseq_node_getElem?] at hx hy
      by_cases h1 : i + 1 < (rseq L).length
      · -- both inside the left factor
        have h0 : i < (rseq L).length := by omega
        rw [if_pos h1] at hx
        rw [if_pos h0] at hy
        exact rseq_step L hx hy
      · by_cases h0 : i < (rseq L).length
        · -- the junction: the first leaf of the right factor
          rw [if_neg h1] at hx
          have he : i + 1 - (rseq L).length = 0 := by omega
          rw [he, rseq_head_getElem?] at hx
          have : x = 1 := by
            have h' : some (0 + 1) = some x := hx
            exact (Option.some.inj h').symm
          omega
        · -- both inside the right factor
          rw [if_neg h1] at hx
          rw [if_neg h0] at hy
          have he : i + 1 - (rseq L).length = (i - (rseq L).length) + 1 := by omega
          rw [he] at hx
          cases hxr : (rseq R)[(i - (rseq L).length) + 1]? with
          | none =>
              rw [hxr] at hx
              exact absurd hx.symm (Option.some_ne_none x)
          | some x' =>
              cases hyr : (rseq R)[i - (rseq L).length]? with
              | none =>
                  rw [hyr] at hy
                  exact absurd hy.symm (Option.some_ne_none y)
              | some y' =>
                  rw [hxr] at hx
                  rw [hyr] at hy
                  have hx1 : x = x' + 1 := by
                    have h' : some (x' + 1) = some x := hx
                    exact (Option.some.inj h').symm
                  have hy1 : y = y' + 1 := by
                    have h' : some (y' + 1) = some y := hy
                    exact (Option.some.inj h').symm
                  have := rseq_step R hxr hyr
                  omega

/-- **The surgery.**  `raise T i` is the tree whose `i`-th right depth is one more than
that of `T`, all others being unchanged.  It is defined whenever the raise is legal, that
is whenever `r_i(T) ≤ r_{i-1}(T)`; the boundary case is the move of Lemma 4.5,
`node (node A B) R ↦ node A (graftLeft B R)`. -/
def raise : Tree → Nat → Tree
  | leaf, _ => leaf
  | node L R, i =>
      if i < L.numLeaves then node (raise L i) R
      else if i = L.numLeaves then
        (match L with
         | leaf => node leaf R
         | node A B => node A (graftLeft B R))
      else node L (raise R (i - L.numLeaves))

theorem raise_node (L R : Tree) (i : Nat) :
    raise (node L R) i =
      if i < L.numLeaves then node (raise L i) R
      else if i = L.numLeaves then
        (match L with
         | leaf => node leaf R
         | node A B => node A (graftLeft B R))
      else node L (raise R (i - L.numLeaves)) := rfl

theorem raise_left {L R : Tree} {i : Nat} (h : i < L.numLeaves) :
    raise (node L R) i = node (raise L i) R := by
  rw [raise_node, if_pos h]

theorem raise_right {L R : Tree} {i : Nat} (h : L.numLeaves < i) :
    raise (node L R) i = node L (raise R (i - L.numLeaves)) := by
  rw [raise_node, if_neg (by omega), if_neg (by omega)]

theorem raise_boundary (A B R : Tree) {i : Nat} (h : i = (node A B).numLeaves) :
    raise (node (node A B) R) i = node A (graftLeft B R) := by
  rw [raise_node, if_neg (by omega), if_pos h]

/-- **The surgery does what it should.**  If the raise at index `i+1` is legal, that is
if `r_{i+1} ≤ r_i`, then `raise T (i+1)` is a tree whose right-depth sequence is that of
`T` with the entry at `i+1` increased by one. -/
theorem rseq_raise : ∀ (T : Tree) {i x y : Nat},
    (rseq T)[i]? = some y → (rseq T)[i + 1]? = some x → x ≤ y →
    rseq (raise T (i + 1)) = (rseq T).set (i + 1) (x + 1)
  | leaf, i, x, y, _, hx, _ => by
      have hn : (rseq leaf)[i + 1]? = none := by
        show ([0] : List Nat)[i + 1]? = none
        cases i <;> rfl
      rw [hn] at hx
      exact absurd hx.symm (Option.some_ne_none x)
  | node L R, i, x, y, hy, hx, hxy => by
      have hLlen : (rseq L).length = L.numLeaves := rseq_length L
      have hLpos := rseq_length_pos L
      have hsplit : rseq (node L R) = rseq L ++ (rseq R).map (· + 1) := rfl
      obtain ⟨t, ht⟩ := rseq_cons R
      rw [rseq_node_getElem?] at hx hy
      by_cases h1 : i + 1 < (rseq L).length
      · -- inside the left factor
        have h0 : i < (rseq L).length := by omega
        rw [if_pos h1] at hx
        rw [if_pos h0] at hy
        have ih := rseq_raise L hy hx hxy
        rw [raise_left (by omega), hsplit]
        show rseq (raise L (i + 1)) ++ (rseq R).map (· + 1) = _
        rw [ih, List.set_append_left _ _ (by omega)]
      · by_cases h0 : i < (rseq L).length
        · -- the junction
          have hia : i + 1 = (rseq L).length := by omega
          rw [if_neg h1] at hx
          have he : i + 1 - (rseq L).length = 0 := by omega
          rw [he, rseq_head_getElem?] at hx
          have hx1 : x = 1 := by
            have h' : some (0 + 1) = some x := hx
            exact (Option.some.inj h').symm
          rw [if_pos h0] at hy
          cases L with
          | leaf =>
              have hone : (rseq leaf).length = 1 := rfl
              have hi0 : i = 0 := by omega
              subst hi0
              have h' : some 0 = some y := hy
              have hy0 : y = 0 := (Option.some.inj h').symm
              omega
          | node A B =>
              have hAB : (rseq (node A B)).length = (node A B).numLeaves :=
                rseq_length (node A B)
              have hT : rseq (node (node A B) R)
                  = (rseq A ++ (rseq B).map (· + 1)) ++ (1 :: t.map (· + 1)) := by
                show (rseq (node A B)) ++ (rseq R).map (· + 1) = _
                rw [ht]
                show (rseq A ++ (rseq B).map (· + 1)) ++ (0 :: t).map (· + 1) = _
                simp
              have hT' : rseq (node A (graftLeft B R))
                  = (rseq A ++ (rseq B).map (· + 1)) ++ (2 :: t.map (· + 1)) := by
                show rseq A ++ (rseq (graftLeft B R)).map (· + 1) = _
                rw [rseq_graftLeft, ht]
                simp
              have hlen : ((rseq A ++ (rseq B).map (· + 1))).length = i + 1 := by
                have hh : (rseq (node A B)).length
                    = (rseq A ++ (rseq B).map (· + 1)).length := rfl
                omega
              rw [raise_boundary A B R (by omega), hx1, hT, hT',
                List.set_append_right _ _ (by omega), hlen]
              simp
        · -- inside the right factor
          rw [if_neg h1] at hx
          rw [if_neg h0] at hy
          have hk : i + 1 - (rseq L).length = (i - (rseq L).length) + 1 := by omega
          rw [hk] at hx
          cases hxr : (rseq R)[(i - (rseq L).length) + 1]? with
          | none =>
              rw [hxr] at hx
              exact absurd hx.symm (Option.some_ne_none x)
          | some x' =>
              cases hyr : (rseq R)[i - (rseq L).length]? with
              | none =>
                  rw [hyr] at hy
                  exact absurd hy.symm (Option.some_ne_none y)
              | some y' =>
                  rw [hxr] at hx
                  rw [hyr] at hy
                  have hx1 : x = x' + 1 := by
                    have h' : some (x' + 1) = some x := hx
                    exact (Option.some.inj h').symm
                  have hy1 : y = y' + 1 := by
                    have h' : some (y' + 1) = some y := hy
                    exact (Option.some.inj h').symm
                  have ih := rseq_raise R hyr hxr (by omega)
                  rw [raise_right (by omega), ← hLlen, hk, hsplit]
                  show rseq L ++ (rseq (raise R ((i - (rseq L).length) + 1))).map (· + 1) = _
                  rw [ih, List.map_set, List.set_append_right _ _ (by omega)]
                  have hidx : i + 1 - (rseq L).length = (i - (rseq L).length) + 1 := by omega
                  rw [hidx, hx1]

/-! ## Comparing sequences without carrying index proofs -/

theorem stanleyLe_iff_getElem? {T U : Tree} :
    stanleyLe T U ↔ (rseq T).length = (rseq U).length ∧
      ∀ (i x y : Nat), (rseq T)[i]? = some x → (rseq U)[i]? = some y → x ≤ y := by
  constructor
  · rintro ⟨hl, hc⟩
    refine ⟨hl, ?_⟩
    intro i x y hx hy
    have hi : i < (rseq T).length := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hx
      exact absurd hx.symm (Option.some_ne_none x)
    have hi' : i < (rseq U).length := by omega
    have ex : (rseq T)[i]'hi = x := by
      rw [List.getElem?_eq_getElem hi] at hx
      exact Option.some.inj hx
    have ey : (rseq U)[i]'hi' = y := by
      rw [List.getElem?_eq_getElem hi'] at hy
      exact Option.some.inj hy
    have := hc i hi hi'
    omega
  · rintro ⟨hl, hc⟩
    refine ⟨hl, ?_⟩
    intro i hi hi'
    exact hc i _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hi')

/-- The first index at which two lists differ.  Constructive, so that the search for a
witness below stays free of the axiom of choice. -/
def firstDiff : List Nat → List Nat → Option Nat
  | [], [] => none
  | [], _ :: _ => some 0
  | _ :: _, [] => some 0
  | a :: s, b :: t => if a = b then (firstDiff s t).map (· + 1) else some 0

theorem firstDiff_none : ∀ {s t : List Nat}, firstDiff s t = none → s = t
  | [], [], _ => rfl
  | [], _ :: _, h => by exact absurd h (by simp [firstDiff])
  | _ :: _, [], h => by exact absurd h (by simp [firstDiff])
  | a :: s, b :: t, h => by
      by_cases hab : a = b
      · have h' : (firstDiff s t).map (· + 1) = none := by
          rw [show firstDiff (a :: s) (b :: t) = (firstDiff s t).map (· + 1) by
            simp [firstDiff, hab]] at h
          exact h
        have : firstDiff s t = none := by
          cases hs : firstDiff s t with
          | none => rfl
          | some v => rw [hs] at h'; exact absurd h' (by simp)
        rw [hab, firstDiff_none this]
      · exact absurd h (by simp [firstDiff, hab])

theorem firstDiff_lt : ∀ {s t : List Nat} {i : Nat}, firstDiff s t = some i →
    ∀ j, j < i → s[j]? = t[j]?
  | [], [], i, h, _, _ => by exact absurd h (by simp [firstDiff])
  | [], _ :: _, i, h, j, hj => by
      have : i = 0 := by
        have h' : some 0 = some i := by rw [← h]; simp [firstDiff]
        exact (Option.some.inj h').symm
      omega
  | _ :: _, [], i, h, j, hj => by
      have : i = 0 := by
        have h' : some 0 = some i := by rw [← h]; simp [firstDiff]
        exact (Option.some.inj h').symm
      omega
  | a :: s, b :: t, i, h, j, hj => by
      by_cases hab : a = b
      · have h' : (firstDiff s t).map (· + 1) = some i := by
          rw [show firstDiff (a :: s) (b :: t) = (firstDiff s t).map (· + 1) by
            simp [firstDiff, hab]] at h
          exact h
        cases hs : firstDiff s t with
        | none => rw [hs] at h'; exact absurd h'.symm (Option.some_ne_none i)
        | some k =>
            rw [hs] at h'
            have hik : i = k + 1 := by
              have h'' : some (k + 1) = some i := h'
              exact (Option.some.inj h'').symm
            cases j with
            | zero => rw [hab]; rfl
            | succ m =>
                have := firstDiff_lt hs m (by omega)
                exact this
      · have : i = 0 := by
          have h' : some 0 = some i := by rw [← h]; simp [firstDiff, hab]
          exact (Option.some.inj h').symm
        omega

theorem firstDiff_ne : ∀ {s t : List Nat} {i : Nat}, firstDiff s t = some i →
    s[i]? ≠ t[i]?
  | [], [], i, h => by exact absurd h (by simp [firstDiff])
  | [], b :: t, i, h => by
      have hi : i = 0 := by
        have h' : some 0 = some i := by rw [← h]; simp [firstDiff]
        exact (Option.some.inj h').symm
      subst hi
      show ([] : List Nat)[0]? ≠ (b :: t)[0]?
      intro hc
      exact absurd hc.symm (Option.some_ne_none b)
  | a :: s, [], i, h => by
      have hi : i = 0 := by
        have h' : some 0 = some i := by rw [← h]; simp [firstDiff]
        exact (Option.some.inj h').symm
      subst hi
      show (a :: s)[0]? ≠ ([] : List Nat)[0]?
      intro hc
      exact absurd hc (Option.some_ne_none a)
  | a :: s, b :: t, i, h => by
      by_cases hab : a = b
      · have h' : (firstDiff s t).map (· + 1) = some i := by
          rw [show firstDiff (a :: s) (b :: t) = (firstDiff s t).map (· + 1) by
            simp [firstDiff, hab]] at h
          exact h
        cases hs : firstDiff s t with
        | none => rw [hs] at h'; exact absurd h'.symm (Option.some_ne_none i)
        | some k =>
            rw [hs] at h'
            have hik : i = k + 1 := by
              have h'' : some (k + 1) = some i := h'
              exact (Option.some.inj h'').symm
            subst hik
            exact firstDiff_ne (s := s) (t := t) (i := k) hs
      · have hi : i = 0 := by
          have h' : some 0 = some i := by rw [← h]; simp [firstDiff, hab]
          exact (Option.some.inj h').symm
        subst hi
        show (a :: s)[0]? ≠ (b :: t)[0]?
        intro hc
        exact hab (Option.some.inj hc)

/-! ## The covering relation -/

/-- A cover in the Stanley order: `T` lies below `U`, not conversely, and no tree lies
strictly between them. -/
def StCover (T U : Tree) : Prop :=
  stanleyLe T U ∧ ¬ stanleyLe U T ∧
  ∀ V : Tree, stanleyLe T V → stanleyLe V U → stanleyLe V T ∨ stanleyLe U V

/-- `U` is obtained from `T` by raising exactly one right depth by one. -/
def RaisesOne (T U : Tree) : Prop :=
  ∃ i x, (rseq T)[i]? = some x ∧ rseq U = (rseq T).set i (x + 1)

theorem lt_length_of_getElem? {l : List Nat} {i x : Nat} (h : l[i]? = some x) :
    i < l.length := by
  by_contra hcon
  rw [List.getElem?_eq_none (by omega)] at h
  exact absurd h.symm (Option.some_ne_none x)

theorem stCover_of_raisesOne {T U : Tree} (h : RaisesOne T U) : StCover T U := by
  obtain ⟨i, x, hx, hU⟩ := h
  have hi := lt_length_of_getElem? hx
  have hlen : (rseq T).length = (rseq U).length := by rw [hU, List.length_set]
  have hUi : (rseq U)[i]? = some (x + 1) := by
    rw [hU]; exact List.getElem?_set_self hi
  have hUj : ∀ j, j ≠ i → (rseq U)[j]? = (rseq T)[j]? := by
    intro j hj
    rw [hU]; exact List.getElem?_set_ne (Ne.symm hj)
  refine ⟨?_, ?_, ?_⟩
  · refine stanleyLe_iff_getElem?.mpr ⟨hlen, ?_⟩
    intro j a b ha hb
    by_cases hj : j = i
    · subst hj
      rw [hx] at ha; rw [hUi] at hb
      have e1 : a = x := (Option.some.inj ha).symm
      have e2 : b = x + 1 := (Option.some.inj hb).symm
      omega
    · rw [hUj j hj, ha] at hb
      have : a = b := (Option.some.inj hb)
      omega
  · intro hcon
    obtain ⟨_, hc⟩ := stanleyLe_iff_getElem?.mp hcon
    have := hc i (x + 1) x hUi hx
    omega
  · intro V hTV hVU
    obtain ⟨hl1, hc1⟩ := stanleyLe_iff_getElem?.mp hTV
    obtain ⟨hl2, hc2⟩ := stanleyLe_iff_getElem?.mp hVU
    -- off the raised index, `V` agrees with `T`
    have hoff : ∀ j, j ≠ i → (rseq V)[j]? = (rseq T)[j]? := by
      intro j hj
      cases hV : (rseq V)[j]? with
      | none =>
          have : ¬ j < (rseq V).length := by
            intro hc
            rw [List.getElem?_eq_getElem hc] at hV
            exact absurd hV (Option.some_ne_none _)
          rw [List.getElem?_eq_none (by omega)]
      | some v =>
          have hjV : j < (rseq V).length := lt_length_of_getElem? hV
          have hjT : j < (rseq T).length := by omega
          have hT : (rseq T)[j]? = some ((rseq T)[j]'hjT) := List.getElem?_eq_getElem hjT
          have h1 := hc1 j _ v hT hV
          have h2 := hc2 j v _ hV ((hUj j hj).trans hT)
          have hvT : v = (rseq T)[j]'hjT := by omega
          rw [hT, hvT]
    -- at the raised index it is either `T` or `U`
    have hiV : i < (rseq V).length := by omega
    have hV : (rseq V)[i]? = some ((rseq V)[i]'hiV) := List.getElem?_eq_getElem hiV
    have h1 := hc1 i x _ hx hV
    have h2 := hc2 i _ (x + 1) hV hUi
    by_cases hval : (rseq V)[i]'hiV = x
    · left
      refine stanleyLe_iff_getElem?.mpr ⟨by omega, ?_⟩
      intro j a b ha hb
      by_cases hj : j = i
      · subst hj
        rw [hV, hval] at ha
        rw [hx] at hb
        have ea : a = x := (Option.some.inj ha).symm
        have eb : b = x := (Option.some.inj hb).symm
        omega
      · rw [hoff j hj, hb] at ha
        have eab : b = a := Option.some.inj ha
        omega
    · right
      have hval' : (rseq V)[i]'hiV = x + 1 := by omega
      refine stanleyLe_iff_getElem?.mpr ⟨by omega, ?_⟩
      intro j a b ha hb
      by_cases hj : j = i
      · subst hj
        rw [hUi] at ha
        rw [hV, hval'] at hb
        have ea : a = x + 1 := (Option.some.inj ha).symm
        have eb : b = x + 1 := (Option.some.inj hb).symm
        omega
      · rw [hUj j hj] at ha
        rw [hoff j hj] at hb
        rw [ha] at hb
        have : a = b := Option.some.inj hb
        omega

theorem stanleyLe_of_rseq_eq {A B : Tree} (h : rseq A = rseq B) : stanleyLe A B := by
  refine stanleyLe_iff_getElem?.mpr ⟨by rw [h], ?_⟩
  intro j a b ha hb
  rw [h, hb] at ha
  have : b = a := Option.some.inj ha
  omega

theorem stanleyLe_trans {A B C : Tree} (h1 : stanleyLe A B) (h2 : stanleyLe B C) :
    stanleyLe A C := by
  obtain ⟨l1, c1⟩ := stanleyLe_iff_getElem?.mp h1
  obtain ⟨l2, c2⟩ := stanleyLe_iff_getElem?.mp h2
  refine stanleyLe_iff_getElem?.mpr ⟨by omega, ?_⟩
  intro i x z hx hz
  have hi : i < (rseq B).length := by
    have := lt_length_of_getElem? hx
    omega
  have hB : (rseq B)[i]? = some ((rseq B)[i]'hi) := List.getElem?_eq_getElem hi
  have p1 := c1 i x _ hx hB
  have p2 := c2 i _ z hB hz
  omega

theorem rseq_eq_of_le_le {A B : Tree} (h1 : stanleyLe A B) (h2 : stanleyLe B A) :
    rseq A = rseq B := by
  obtain ⟨hl, hc1⟩ := stanleyLe_iff_getElem?.mp h1
  obtain ⟨_, hc2⟩ := stanleyLe_iff_getElem?.mp h2
  refine List.ext_getElem? ?_
  intro j
  cases hA : (rseq A)[j]? with
  | none =>
      have hj : ¬ j < (rseq A).length := by
        intro hc
        rw [List.getElem?_eq_getElem hc] at hA
        exact absurd hA (Option.some_ne_none _)
      rw [List.getElem?_eq_none (by omega)]
  | some a =>
      have hjA := lt_length_of_getElem? hA
      have hjB : j < (rseq B).length := by omega
      have hB : (rseq B)[j]? = some ((rseq B)[j]'hjB) := List.getElem?_eq_getElem hjB
      have p1 := hc1 j a _ hA hB
      have p2 := hc2 j _ a hB hA
      rw [hB]
      exact congrArg some (by omega)

theorem raisesOne_of_stCover {T U : Tree} (h : StCover T U) : RaisesOne T U := by
  obtain ⟨hTU, hnot, hbetween⟩ := h
  obtain ⟨hlen, hc⟩ := stanleyLe_iff_getElem?.mp hTU
  cases hd : firstDiff (rseq T) (rseq U) with
  | none =>
      exact absurd (stanleyLe_of_rseq_eq (firstDiff_none hd).symm) hnot
  | some k =>
      have hne := firstDiff_ne hd
      have hlt := firstDiff_lt hd
      -- the differing index is inside both sequences
      have hk : k < (rseq T).length := by
        by_contra hcon
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)] at hne
        exact hne rfl
      have hk' : k < (rseq U).length := by omega
      have hTk : (rseq T)[k]? = some ((rseq T)[k]'hk) := List.getElem?_eq_getElem hk
      have hUk : (rseq U)[k]? = some ((rseq U)[k]'hk') := List.getElem?_eq_getElem hk'
      have hab : (rseq T)[k]'hk < (rseq U)[k]'hk' := by
        have hle := hc k _ _ hTk hUk
        have : (rseq T)[k]'hk ≠ (rseq U)[k]'hk' := by
          intro hcon
          exact hne (by rw [hTk, hUk, hcon])
        omega
      -- the index is not the first one, where both sequences vanish
      have hk0 : k ≠ 0 := by
        intro hcon
        subst hcon
        rw [rseq_head_getElem? T, rseq_head_getElem? U] at hne
        exact hne rfl
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      -- the predecessor, where the two sequences still agree
      have hm : m < (rseq T).length := by omega
      have hTm : (rseq T)[m]? = some ((rseq T)[m]'hm) := List.getElem?_eq_getElem hm
      have hUm : (rseq U)[m]? = some ((rseq T)[m]'hm) := by
        rw [← hlt m (by omega)]; exact hTm
      -- legality of the raise
      have hstep := rseq_step U hUk hUm
      have hlegal : (rseq T)[m + 1]'hk ≤ (rseq T)[m]'hm := by omega
      -- the raised tree
      set V := raise T (m + 1) with hV
      have hVseq : rseq V = (rseq T).set (m + 1) ((rseq T)[m + 1]'hk + 1) :=
        rseq_raise T hTm hTk hlegal
      have hR : RaisesOne T V := ⟨m + 1, _, hTk, hVseq⟩
      obtain ⟨hTV, _, _⟩ := stCover_of_raisesOne hR
      have hVU : stanleyLe V U := by
        refine stanleyLe_iff_getElem?.mpr ⟨by rw [hVseq, List.length_set]; omega, ?_⟩
        intro j a b ha hb
        by_cases hj : j = m + 1
        · subst hj
          rw [hVseq, List.getElem?_set_self (by omega)] at ha
          rw [hUk] at hb
          have ea : a = (rseq T)[m + 1]'hk + 1 := (Option.some.inj ha).symm
          have eb : b = (rseq U)[m + 1]'hk' := (Option.some.inj hb).symm
          omega
        · rw [hVseq, List.getElem?_set_ne (Ne.symm hj)] at ha
          exact hc j a b ha hb
      rcases hbetween V hTV hVU with hVT | hUV
      · -- impossible: `V` is strictly above `T`
        obtain ⟨_, hcVT⟩ := stanleyLe_iff_getElem?.mp hVT
        have hVk : (rseq V)[m + 1]? = some ((rseq T)[m + 1]'hk + 1) := by
          rw [hVseq]; exact List.getElem?_set_self (by omega)
        have hcon := hcVT (m + 1) _ _ hVk hTk
        exact absurd hcon (by omega)
      · exact ⟨m + 1, _, hTk, by rw [← hVseq]; exact rseq_eq_of_le_le hUV hVU⟩

/-- **Lemma 4.4 in coordinates.**  A cover of the Stanley order is exactly a step that
raises one right depth by one. -/
theorem stCover_iff_raisesOne {T U : Tree} : StCover T U ↔ RaisesOne T U :=
  ⟨raisesOne_of_stCover, stCover_of_raisesOne⟩

/-! ## The sequence determines the tree (2.8 of Csákány–Waldhauser) -/

/-- Right depth `0` is attained only by the leftmost leaf. -/
theorem rseq_zero_iff : ∀ (T : Tree) {j : Nat}, (rseq T)[j]? = some 0 → j = 0
  | leaf, j, h => by
      cases j with
      | zero => rfl
      | succ m =>
          have hn : (rseq leaf)[m + 1]? = none := by
            show ([0] : List Nat)[m + 1]? = none
            cases m <;> rfl
          rw [hn] at h
          exact absurd h.symm (Option.some_ne_none 0)
  | node L R, j, h => by
      rw [rseq_node_getElem?] at h
      by_cases hj : j < (rseq L).length
      · rw [if_pos hj] at h
        exact rseq_zero_iff L h
      · rw [if_neg hj] at h
        cases hR : (rseq R)[j - (rseq L).length]? with
        | none => rw [hR] at h; exact absurd h.symm (Option.some_ne_none 0)
        | some v =>
            rw [hR] at h
            have h' : some (v + 1) = some 0 := h
            have : v + 1 = 0 := Option.some.inj h'
            omega

/-- `a` is the position at which the right factor begins: the last place carrying `1`. -/
def IsSplit (s : List Nat) (a : Nat) : Prop :=
  s[a]? = some 1 ∧ ∀ j, a < j → s[j]? ≠ some 1

theorem isSplit_unique {s : List Nat} {a b : Nat}
    (ha : IsSplit s a) (hb : IsSplit s b) : a = b := by
  by_contra hne
  rcases Nat.lt_or_ge a b with h | h
  · exact ha.2 b h hb.1
  · exact hb.2 a (by omega) ha.1

theorem isSplit_node (L R : Tree) : IsSplit (rseq (node L R)) (rseq L).length := by
  constructor
  · rw [rseq_node_getElem?, if_neg (by omega)]
    have : (rseq L).length - (rseq L).length = 0 := by omega
    rw [this, rseq_head_getElem?]
    rfl
  · intro j hj hcon
    rw [rseq_node_getElem?, if_neg (by omega)] at hcon
    cases hR : (rseq R)[j - (rseq L).length]? with
    | none => rw [hR] at hcon; exact absurd hcon.symm (Option.some_ne_none 1)
    | some v =>
        rw [hR] at hcon
        have h' : some (v + 1) = some 1 := hcon
        have hv : v = 0 := by
          have := Option.some.inj h'
          omega
        subst hv
        have := rseq_zero_iff R hR
        omega

theorem map_succ_injective : ∀ {s t : List Nat},
    s.map (· + 1) = t.map (· + 1) → s = t
  | [], [], _ => rfl
  | [], _ :: _, h => by exact absurd h (by simp)
  | _ :: _, [], h => by exact absurd h (by simp)
  | a :: s, b :: t, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      have hab : a = b := by omega
      rw [hab, map_succ_injective h.2]

/-- **The right-depth sequence determines the tree** (2.8 of Csákány–Waldhauser). -/
theorem rseq_injective : ∀ {T U : Tree}, rseq T = rseq U → T = U
  | leaf, leaf, _ => rfl
  | leaf, node L' R', h => by
      have h1 : (rseq leaf).length = 1 := rfl
      have h2 : (rseq (node L' R')).length = (rseq L').length + (rseq R').length := by
        show (rseq L' ++ (rseq R').map (· + 1)).length = _
        simp
      have := rseq_length_pos L'
      have := rseq_length_pos R'
      rw [h] at h1
      omega
  | node L R, leaf, h => by
      have h1 : (rseq leaf).length = 1 := rfl
      have h2 : (rseq (node L R)).length = (rseq L).length + (rseq R).length := by
        show (rseq L ++ (rseq R).map (· + 1)).length = _
        simp
      have := rseq_length_pos L
      have := rseq_length_pos R
      rw [← h] at h1
      omega
  | node L R, node L' R', h => by
      have h1 := isSplit_node L R
      have h2 := isSplit_node L' R'
      rw [h] at h1
      have hLL : (rseq L).length = (rseq L').length := isSplit_unique h1 h2
      have hsplit : rseq L ++ (rseq R).map (· + 1)
          = rseq L' ++ (rseq R').map (· + 1) := h
      obtain ⟨hL, hR⟩ := List.append_inj hsplit hLL
      rw [rseq_injective hL, rseq_injective (map_succ_injective hR)]

/-! ## The local form of a cover (Lemma 4.5) -/

theorem rseq_root_move (A B R : Tree) :
    rseq (node A (graftLeft B R))
      = (rseq (node (node A B) R)).set (rseq (node A B)).length 2 := by
  obtain ⟨t, ht⟩ := rseq_cons R
  have hT : rseq (node (node A B) R)
      = (rseq A ++ (rseq B).map (· + 1)) ++ (1 :: t.map (· + 1)) := by
    show (rseq (node A B)) ++ (rseq R).map (· + 1) = _
    rw [ht]
    show (rseq A ++ (rseq B).map (· + 1)) ++ (0 :: t).map (· + 1) = _
    simp
  have hT' : rseq (node A (graftLeft B R))
      = (rseq A ++ (rseq B).map (· + 1)) ++ (2 :: t.map (· + 1)) := by
    show rseq A ++ (rseq (graftLeft B R)).map (· + 1) = _
    rw [rseq_graftLeft, ht]
    simp
  have hlen : (rseq (node A B)).length = (rseq A ++ (rseq B).map (· + 1)).length := rfl
  rw [hT, hT', hlen, List.set_append_right _ _ (Nat.le_refl _)]
  simp

/-- **The Stanley covering move in the local form of Lemma 4.5.**  Inside a common
context, `(A·B)·R` becomes `A·(B grafted onto the leftmost leaf of R)`.  Writing
`R = L_D(c)` for the factorisation of `R` along its leftmost leaf, this is
`((A·B)·L_D(c)) ↦ (A·L_D(B·c))`. -/
inductive StRot : Tree → Tree → Prop
  | root (A B R : Tree) : StRot (node (node A B) R) (node A (graftLeft B R))
  | left {L L' : Tree} (R : Tree) : StRot L L' → StRot (node L R) (node L' R)
  | right (L : Tree) {R R' : Tree} : StRot R R' → StRot (node L R) (node L R')

theorem raisesOne_of_stRot : ∀ {T U : Tree}, StRot T U → RaisesOne T U
  | _, _, .root A B R =>
      ⟨(rseq (node A B)).length, 1, (isSplit_node (node A B) R).1, rseq_root_move A B R⟩
  | _, _, .left (L := L) (L' := L') R h => by
      obtain ⟨i, x, hx, hL⟩ := raisesOne_of_stRot h
      have hi : i < (rseq L).length := lt_length_of_getElem? hx
      refine ⟨i, x, ?_, ?_⟩
      · rw [rseq_node_getElem?, if_pos hi]; exact hx
      · show rseq L' ++ (rseq R).map (· + 1) = _
        rw [hL]
        show _ = ((rseq L ++ (rseq R).map (· + 1))).set i (x + 1)
        rw [List.set_append_left _ _ hi]
  | _, _, .right L (R := R) (R' := R') h => by
      obtain ⟨i, x, hx, hR⟩ := raisesOne_of_stRot h
      have hi : i < (rseq R).length := lt_length_of_getElem? hx
      refine ⟨(rseq L).length + i, x + 1, ?_, ?_⟩
      · rw [rseq_node_getElem?, if_neg (by omega)]
        have he : (rseq L).length + i - (rseq L).length = i := by omega
        rw [he, hx]
        rfl
      · show rseq L ++ (rseq R').map (· + 1) = _
        rw [hR, List.map_set]
        show _ = ((rseq L ++ (rseq R).map (· + 1))).set ((rseq L).length + i) (x + 1 + 1)
        rw [List.set_append_right _ _ (by omega)]
        have he : (rseq L).length + i - (rseq L).length = i := by omega
        rw [he]

/-- Whenever the raise at `i+1` is legal, it is a local move. -/
theorem stRot_raise : ∀ (T : Tree) {i x y : Nat},
    (rseq T)[i]? = some y → (rseq T)[i + 1]? = some x → x ≤ y →
    StRot T (raise T (i + 1))
  | leaf, i, x, y, _, hx, _ => by
      have hn : (rseq leaf)[i + 1]? = none := by
        show ([0] : List Nat)[i + 1]? = none
        cases i <;> rfl
      rw [hn] at hx
      exact absurd hx.symm (Option.some_ne_none x)
  | node L R, i, x, y, hy, hx, hxy => by
      have hLlen : (rseq L).length = L.numLeaves := rseq_length L
      have hLpos := rseq_length_pos L
      rw [rseq_node_getElem?] at hx hy
      by_cases h1 : i + 1 < (rseq L).length
      · have h0 : i < (rseq L).length := by omega
        rw [if_pos h1] at hx
        rw [if_pos h0] at hy
        rw [raise_left (by omega)]
        exact StRot.left R (stRot_raise L hy hx hxy)
      · by_cases h0 : i < (rseq L).length
        · -- the junction: `L` must be a node
          have hia : i + 1 = (rseq L).length := by omega
          rw [if_neg h1] at hx
          have he : i + 1 - (rseq L).length = 0 := by omega
          rw [he, rseq_head_getElem?] at hx
          have hx1 : x = 1 := by
            have h' : some (0 + 1) = some x := hx
            exact (Option.some.inj h').symm
          rw [if_pos h0] at hy
          cases L with
          | leaf =>
              have hone : (rseq leaf).length = 1 := rfl
              have hi0 : i = 0 := by omega
              subst hi0
              have h' : some 0 = some y := hy
              have hy0 : y = 0 := (Option.some.inj h').symm
              exact absurd hxy (by omega)
          | node A B =>
              have hAB : (rseq (node A B)).length = (node A B).numLeaves :=
                rseq_length (node A B)
              rw [raise_boundary A B R (by omega)]
              exact StRot.root A B R
        · rw [if_neg h1] at hx
          rw [if_neg h0] at hy
          have hk : i + 1 - (rseq L).length = (i - (rseq L).length) + 1 := by omega
          rw [hk] at hx
          cases hxr : (rseq R)[(i - (rseq L).length) + 1]? with
          | none =>
              rw [hxr] at hx
              exact absurd hx.symm (Option.some_ne_none x)
          | some x' =>
              cases hyr : (rseq R)[i - (rseq L).length]? with
              | none =>
                  rw [hyr] at hy
                  exact absurd hy.symm (Option.some_ne_none y)
              | some y' =>
                  rw [hxr] at hx
                  rw [hyr] at hy
                  have hx1 : x = x' + 1 := by
                    have h' : some (x' + 1) = some x := hx
                    exact (Option.some.inj h').symm
                  have hy1 : y = y' + 1 := by
                    have h' : some (y' + 1) = some y := hy
                    exact (Option.some.inj h').symm
                  rw [raise_right (by omega), ← hLlen, hk]
                  exact StRot.right L (stRot_raise R hyr hxr (by omega))

theorem stRot_of_raisesOne {T U : Tree} (h : RaisesOne T U) : StRot T U := by
  obtain ⟨i, x, hx, hU⟩ := h
  have hi := lt_length_of_getElem? hx
  -- the raised index is not the first one
  have hi0 : i ≠ 0 := by
    intro hcon
    subst hcon
    have h1 : (rseq U)[0]? = some (x + 1) := by
      rw [hU]; exact List.getElem?_set_self (by omega)
    rw [rseq_head_getElem? U] at h1
    have := Option.some.inj h1
    omega
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hm : m < (rseq T).length := by omega
  have hTm : (rseq T)[m]? = some ((rseq T)[m]'hm) := List.getElem?_eq_getElem hm
  -- legality, read off from the sequence of `U`
  have hUm : (rseq U)[m]? = some ((rseq T)[m]'hm) := by
    rw [hU, List.getElem?_set_ne (by omega)]; exact hTm
  have hUk : (rseq U)[m + 1]? = some (x + 1) := by
    rw [hU]; exact List.getElem?_set_self (by omega)
  have hstep := rseq_step U hUk hUm
  have hlegal : x ≤ (rseq T)[m]'hm := by omega
  have hV : rseq (raise T (m + 1)) = (rseq T).set (m + 1) (x + 1) :=
    rseq_raise T hTm hx hlegal
  have : U = raise T (m + 1) := rseq_injective (by rw [hU, hV])
  rw [this]
  exact stRot_raise T hTm hx hlegal

/-- **Lemma 4.5 as an equivalence.**  The local move is exactly a step that raises one
right depth by one; with `stCover_iff_raisesOne`, it is exactly a cover. -/
theorem stRot_iff_raisesOne {T U : Tree} : StRot T U ↔ RaisesOne T U :=
  ⟨raisesOne_of_stRot, stRot_of_raisesOne⟩

/-- **Lemma 4.4 in tree form.**  The covers of the Stanley order are exactly the local
moves of Lemma 4.5. -/
theorem stCover_iff_stRot {T U : Tree} : StCover T U ↔ StRot T U :=
  stCover_iff_raisesOne.trans stRot_iff_raisesOne.symm

/-! ## The move seen in the word (Lemma 4.4) -/

theorem wword_graftLeft (B : Tree) : ∀ R : Tree,
    wword (graftLeft B R) = wword R ++ (true :: false :: wword B)
  | leaf => by
      show true :: (wword leaf ++ (false :: wword B)) = _
      simp [wword]
  | node P Q => by
      have ih := wword_graftLeft B P
      show true :: (wword Q ++ (false :: wword (graftLeft B P))) = _
      rw [ih]
      show _ = (true :: (wword Q ++ (false :: wword P))) ++ (true :: false :: wword B)
      simp

/-- **Definition of the move at the level of words**: one occurrence of `DU` becomes
`UD`. -/
def SwapDU (T U : Tree) : Prop :=
  ∃ p s : List Step,
    wword T = p ++ (false :: true :: s) ∧ wword U = p ++ (true :: false :: s)

theorem swapDU_of_stRot : ∀ {T U : Tree}, StRot T U → SwapDU T U
  | _, _, .root A B R => by
      refine ⟨true :: wword R, wword B ++ (false :: wword A), ?_, ?_⟩
      · show true :: (wword R ++ (false :: wword (node A B))) = _
        show true :: (wword R ++ (false :: (true :: (wword B ++ (false :: wword A))))) = _
        simp
      · show true :: (wword (graftLeft B R) ++ (false :: wword A)) = _
        rw [wword_graftLeft]
        simp
  | _, _, .left (L := L) (L' := L') R h => by
      obtain ⟨p, s, h1, h2⟩ := swapDU_of_stRot h
      refine ⟨true :: (wword R ++ (false :: p)), s, ?_, ?_⟩
      · show true :: (wword R ++ (false :: wword L)) = _
        rw [h1]; simp
      · show true :: (wword R ++ (false :: wword L')) = _
        rw [h2]; simp
  | _, _, .right L (R := R) (R' := R') h => by
      obtain ⟨p, s, h1, h2⟩ := swapDU_of_stRot h
      refine ⟨true :: p, s ++ (false :: wword L), ?_, ?_⟩
      · show true :: (wword R ++ (false :: wword L)) = _
        rw [h1]; simp
      · show true :: (wword R' ++ (false :: wword L)) = _
        rw [h2]; simp

/-! ## The word determines the tree -/

/-- Positions of the up-steps of a word, counted from `k`. -/
def upPosFrom : Nat → List Step → List Nat
  | _, [] => []
  | k, true :: w => k :: upPosFrom (k + 1) w
  | k, false :: w => upPosFrom (k + 1) w

theorem upPosFrom_shift : ∀ (w : List Step) (k d : Nat),
    upPosFrom (k + d) w = (upPosFrom k w).map (· + d)
  | [], _, _ => rfl
  | true :: w, k, d => by
      have he : k + d + 1 = (k + 1) + d := by omega
      show (k + d) :: upPosFrom (k + d + 1) w = _
      rw [he, upPosFrom_shift w (k + 1) d]
      show _ = ((k :: upPosFrom (k + 1) w).map (· + d))
      simp
  | false :: w, k, d => by
      have he : k + d + 1 = (k + 1) + d := by omega
      show upPosFrom (k + d + 1) w = _
      rw [he, upPosFrom_shift w (k + 1) d]
      rfl

theorem upPosFrom_append : ∀ (w1 w2 : List Step) (k : Nat),
    upPosFrom k (w1 ++ w2) = upPosFrom k w1 ++ upPosFrom (k + w1.length) w2
  | [], w2, k => by
      show upPosFrom k w2 = [] ++ upPosFrom (k + 0) w2
      simp
  | true :: w1, w2, k => by
      have ih := upPosFrom_append w1 w2 (k + 1)
      have he : k + 1 + w1.length = k + (true :: w1).length := by simp; omega
      show k :: upPosFrom (k + 1) (w1 ++ w2) = _
      rw [ih, he]
      show _ = (k :: upPosFrom (k + 1) w1) ++ upPosFrom (k + (true :: w1).length) w2
      simp
  | false :: w1, w2, k => by
      have ih := upPosFrom_append w1 w2 (k + 1)
      have he : k + 1 + w1.length = k + (false :: w1).length := by simp; omega
      show upPosFrom (k + 1) (w1 ++ w2) = _
      rw [ih, he]
      rfl

theorem upPosFrom_qword : ∀ T : Tree, upPosFrom 1 (qword T) = upPos T
  | leaf => rfl
  | node L R => by
      have ihL := upPosFrom_qword L
      have ihR := upPosFrom_qword R
      have hq : qword (node L R) = qword L ++ (true :: (qword R ++ [false])) := rfl
      have hshift : upPosFrom (1 + (1 + (qword L).length)) (qword R)
          = (upPos R).map (· + (1 + (qword L).length)) := by
        rw [upPosFrom_shift (qword R) 1 (1 + (qword L).length), ihR]
      rw [hq, upPosFrom_append]
      show upPosFrom 1 (qword L)
          ++ ((1 + (qword L).length) :: upPosFrom (1 + (qword L).length + 1) (qword R ++ [false]))
          = _
      rw [upPosFrom_append]
      have he : 1 + (qword L).length + 1 = 1 + (1 + (qword L).length) := by omega
      rw [he, hshift, ihL]
      show _ = upPos L ++ (((qword L).length + 1) ::
        (upPos R).map (· + ((qword L).length + 1)))
      have hc : ∀ k : Nat, upPosFrom k ([false] : List Step) = [] := by
        intro k; rfl
      rw [hc]
      have h1 : 1 + (qword L).length = (qword L).length + 1 := by omega
      rw [h1]
      simp

theorem qword_injective : ∀ {T U : Tree}, qword T = qword U → T = U := by
  intro T U h
  have hp : upPos T = upPos U := by rw [← upPosFrom_qword T, ← upPosFrom_qword U, h]
  have hlen : (upHeights T).length = (upHeights U).length := by
    rw [← upPos_length T, ← upPos_length U, hp]
  have hh : upHeights T = upHeights U := by
    refine List.ext_getElem hlen ?_
    intro j hj hj'
    have hpT : j < (upPos T).length := by rw [upPos_length T]; exact hj
    have hpU : j < (upPos U).length := by rw [upPos_length U]; exact hj'
    have e1 := upPos_add_upHeights T j hpT hj
    have e2 := upPos_add_upHeights U j hpU hj'
    have e3 : (upPos T)[j]'hpT = (upPos U)[j]'hpU := by
      simp only [hp]
    omega
  have hr : rseq T = rseq U := by
    obtain ⟨tT, hT⟩ := rseq_cons T
    obtain ⟨tU, hU⟩ := rseq_cons U
    rw [upHeights_eq_rseq_tail T, upHeights_eq_rseq_tail U, hT, hU] at hh
    simp only [List.tail_cons] at hh
    rw [hT, hU, hh]
  exact rseq_injective hr

theorem barW_barW (w : List Step) : barW (barW w) = w := by
  show (((w.map (!·)).reverse.map (!·)).reverse) = w
  have hid : ((fun x => !x) ∘ fun x => !x) = (id : Step → Step) := by
    funext b; cases b <;> rfl
  simp [hid]

theorem wword_injective {T U : Tree} (h : wword T = wword U) : T = U := by
  rw [wword_eq_barW_qword T, wword_eq_barW_qword U] at h
  have : barW (barW (qword T)) = barW (barW (qword U)) := by rw [h]
  rw [barW_barW, barW_barW] at this
  exact qword_injective this

/-- **Every `DU` in the word is a local move.**  This is the converse half of the proof
of Lemma 4.4: given an occurrence of `DU` in `w T`, the tree obtained by swapping it is
again a tree, namely the one produced by the corresponding move. -/
theorem exists_stRot_of_swap : ∀ (T : Tree) (p s : List Step),
    wword T = p ++ (false :: true :: s) →
    ∃ V, StRot T V ∧ wword V = p ++ (true :: false :: s)
  | leaf, p, s, h => by
      have hlen : (wword leaf).length = 0 := rfl
      rw [h] at hlen
      simp at hlen
  | node L R, p, s, h => by
      have hT : wword (node L R) = true :: (wword R ++ (false :: wword L)) := rfl
      rw [hT] at h
      cases p with
      | nil =>
          rw [List.nil_append] at h
          exact absurd h (by simp)
      | cons a p1 =>
          rw [List.cons_append] at h
          injection h with ha hrest
          subst ha
          rcases List.append_eq_append_iff.mp hrest with ⟨a1, hp1, hL⟩ | ⟨c1, hR, hs⟩
          · cases a1 with
            | nil =>
                rw [List.nil_append] at hL
                injection hL with _ hL2
                cases L with
                | leaf =>
                    have hnil : ([] : List Step) = true :: s := hL2
                    exact absurd hnil (by simp)
                | node A B =>
                    have hAB : wword (node A B)
                        = true :: (wword B ++ (false :: wword A)) := rfl
                    rw [hAB] at hL2
                    injection hL2 with _ hs2
                    refine ⟨node A (graftLeft B R), StRot.root A B R, ?_⟩
                    show true :: (wword (graftLeft B R) ++ (false :: wword A)) = _
                    rw [wword_graftLeft]
                    rw [List.append_nil] at hp1
                    subst hp1
                    subst hs2
                    simp
            | cons b a2 =>
                injection hL with hb hL2
                subst hb
                obtain ⟨L2, hrot, hL2b⟩ := exists_stRot_of_swap L a2 s hL2
                refine ⟨node L2 R, StRot.left R hrot, ?_⟩
                show true :: (wword R ++ (false :: wword L2)) = _
                rw [hL2b, hp1]
                simp
          · cases c1 with
            | nil =>
                rw [List.append_nil] at hR
                rw [List.nil_append] at hs
                injection hs with _ hs2
                cases L with
                | leaf =>
                    have hnil : true :: s = ([] : List Step) := hs2
                    exact absurd hnil (by simp)
                | node A B =>
                    have hAB : wword (node A B)
                        = true :: (wword B ++ (false :: wword A)) := rfl
                    rw [hAB] at hs2
                    injection hs2 with _ hs3
                    refine ⟨node A (graftLeft B R), StRot.root A B R, ?_⟩
                    show true :: (wword (graftLeft B R) ++ (false :: wword A)) = _
                    subst hs3
                    rw [wword_graftLeft, ← hR]
                    simp
            | cons b c2 =>
                injection hs with hb hs2
                subst hb
                cases c2 with
                | nil =>
                    have hcon : (true :: s) = ([] : List Step) ++ (false :: wword L) := hs2
                    rw [List.nil_append] at hcon
                    injection hcon with h1 _
                    exact absurd h1 (by decide)
                | cons d c3 =>
                    injection hs2 with hd hs3
                    subst hd
                    obtain ⟨R2, hrot, hR2⟩ := exists_stRot_of_swap R p1 c3 hR
                    refine ⟨node L R2, StRot.right L hrot, ?_⟩
                    subst hs3
                    show true :: (wword R2 ++ (false :: wword L)) = _
                    rw [hR2]
                    simp

theorem stRot_of_swapDU {T U : Tree} (h : SwapDU T U) : StRot T U := by
  obtain ⟨p, s, h1, h2⟩ := h
  obtain ⟨V, hrot, hV⟩ := exists_stRot_of_swap T p s h1
  have hUV : U = V := wword_injective (by rw [h2, hV])
  rw [hUV]
  exact hrot

theorem swapDU_iff_stRot {T U : Tree} : SwapDU T U ↔ StRot T U :=
  ⟨stRot_of_swapDU, swapDU_of_stRot⟩

/-- **Lemma 4.4.**  `T ⋖ U` in the Stanley order exactly when `w U` is obtained from
`w T` by replacing one occurrence of `DU` by `UD`. -/
theorem stCover_iff_swapDU {T U : Tree} : StCover T U ↔ SwapDU T U :=
  stCover_iff_stRot.trans swapDU_iff_stRot.symm

/-! ## The order is generated by its covers -/

theorem list_sum_le : ∀ (a b : List Nat), a.length = b.length →
    (∀ (i x y : Nat), a[i]? = some x → b[i]? = some y → x ≤ y) → a.sum ≤ b.sum
  | [], [], _, _ => Nat.le_refl 0
  | [], y :: b, hl, _ => by
      have h0 : (0 : Nat) = b.length + 1 := hl
      omega
  | x :: a, [], hl, _ => by
      have h0 : a.length + 1 = (0 : Nat) := hl
      omega
  | x :: a, y :: b, hl, hle => by
      have h0 : x ≤ y := hle 0 x y rfl rfl
      have hl' : a.length = b.length := by
        have hh : a.length + 1 = b.length + 1 := hl
        omega
      have ih := list_sum_le a b hl' (fun i p q hp hq => hle (i + 1) p q hp hq)
      have e1 : (x :: a).sum = x + a.sum := List.sum_cons
      have e2 : (y :: b).sum = y + b.sum := List.sum_cons
      omega

theorem list_eq_of_le_of_sum : ∀ (a b : List Nat), a.length = b.length →
    (∀ (i x y : Nat), a[i]? = some x → b[i]? = some y → x ≤ y) → a.sum = b.sum → a = b
  | [], [], _, _, _ => rfl
  | [], y :: b, hl, _, _ => by
      have h0 : (0 : Nat) = b.length + 1 := hl
      omega
  | x :: a, [], hl, _, _ => by
      have h0 : a.length + 1 = (0 : Nat) := hl
      omega
  | x :: a, y :: b, hl, hle, hs => by
      have h0 : x ≤ y := hle 0 x y rfl rfl
      have hl' : a.length = b.length := by
        have hh : a.length + 1 = b.length + 1 := hl
        omega
      have hsub := list_sum_le a b hl' (fun i p q hp hq => hle (i + 1) p q hp hq)
      have e1 : (x :: a).sum = x + a.sum := List.sum_cons
      have e2 : (y :: b).sum = y + b.sum := List.sum_cons
      have hxy : x = y := by omega
      have hab : a.sum = b.sum := by omega
      have ih := list_eq_of_le_of_sum a b hl' (fun i p q hp hq => hle (i + 1) p q hp hq) hab
      rw [hxy, ih]

theorem sum_set_succ : ∀ (l : List Nat) (i x : Nat), l[i]? = some x →
    (l.set i (x + 1)).sum = l.sum + 1
  | [], i, x, h => by
      have hn : ([] : List Nat)[i]? = none := by cases i <;> rfl
      rw [hn] at h
      exact absurd h.symm (Option.some_ne_none x)
  | a :: t, 0, x, h => by
      have hax : a = x := Option.some.inj h
      subst hax
      show ((a + 1) :: t).sum = (a :: t).sum + 1
      rw [List.sum_cons, List.sum_cons]
      omega
  | a :: t, i + 1, x, h => by
      have ih := sum_set_succ t i x h
      show (a :: t.set i (x + 1)).sum = (a :: t).sum + 1
      rw [List.sum_cons, List.sum_cons, ih]
      omega

theorem rseq_sum_le {T U : Tree} (h : stanleyLe T U) : (rseq T).sum ≤ (rseq U).sum := by
  obtain ⟨hl, hc⟩ := stanleyLe_iff_getElem?.mp h
  exact list_sum_le _ _ hl hc

/-- One step up: below `U` and not equal to it, `T` has a cover that is still below `U`. -/
theorem exists_stRot_step {T U : Tree} (h : stanleyLe T U) (hne : rseq T ≠ rseq U) :
    ∃ V, StRot T V ∧ stanleyLe V U ∧ (rseq V).sum = (rseq T).sum + 1 := by
  obtain ⟨hlen, hc⟩ := stanleyLe_iff_getElem?.mp h
  cases hd : firstDiff (rseq T) (rseq U) with
  | none => exact absurd (firstDiff_none hd) hne
  | some k =>
      have hnek := firstDiff_ne hd
      have hlt := firstDiff_lt hd
      have hk : k < (rseq T).length := by
        by_contra hcon
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)] at hnek
        exact hnek rfl
      have hk' : k < (rseq U).length := by omega
      have hTk : (rseq T)[k]? = some ((rseq T)[k]'hk) := List.getElem?_eq_getElem hk
      have hUk : (rseq U)[k]? = some ((rseq U)[k]'hk') := List.getElem?_eq_getElem hk'
      have hab : (rseq T)[k]'hk < (rseq U)[k]'hk' := by
        have hle := hc k _ _ hTk hUk
        have hne2 : (rseq T)[k]'hk ≠ (rseq U)[k]'hk' := by
          intro hcon
          exact hnek (by rw [hTk, hUk, hcon])
        omega
      have hk0 : k ≠ 0 := by
        intro hcon
        subst hcon
        rw [rseq_head_getElem? T, rseq_head_getElem? U] at hnek
        exact hnek rfl
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hm : m < (rseq T).length := by omega
      have hTm : (rseq T)[m]? = some ((rseq T)[m]'hm) := List.getElem?_eq_getElem hm
      have hUm : (rseq U)[m]? = some ((rseq T)[m]'hm) := by
        rw [← hlt m (by omega)]; exact hTm
      have hstep := rseq_step U hUk hUm
      have hlegal : (rseq T)[m + 1]'hk ≤ (rseq T)[m]'hm := by omega
      refine ⟨raise T (m + 1), stRot_raise T hTm hTk hlegal, ?_, ?_⟩
      · have hVseq := rseq_raise T hTm hTk hlegal
        refine stanleyLe_iff_getElem?.mpr ⟨by rw [hVseq, List.length_set]; omega, ?_⟩
        intro j a b ha hb
        by_cases hj : j = m + 1
        · subst hj
          rw [hVseq, List.getElem?_set_self (by omega)] at ha
          rw [hUk] at hb
          have ea : a = (rseq T)[m + 1]'hk + 1 := (Option.some.inj ha).symm
          have eb : b = (rseq U)[m + 1]'hk' := (Option.some.inj hb).symm
          omega
        · rw [hVseq, List.getElem?_set_ne (Ne.symm hj)] at ha
          exact hc j a b ha hb
      · rw [rseq_raise T hTm hTk hlegal]
        exact sum_set_succ _ _ _ hTk

theorem reflTransGen_stRot_aux : ∀ (n : Nat) (T U : Tree),
    (rseq U).sum - (rseq T).sum ≤ n → stanleyLe T U →
    Relation.ReflTransGen StRot T U
  | 0, T, U, hn, h => by
      have hle := rseq_sum_le h
      obtain ⟨hlen, hc⟩ := stanleyLe_iff_getElem?.mp h
      have hsum : (rseq T).sum = (rseq U).sum := by omega
      have : rseq T = rseq U := list_eq_of_le_of_sum _ _ hlen hc hsum
      rw [rseq_injective this]
  | n + 1, T, U, hn, h => by
      by_cases heq : rseq T = rseq U
      · rw [rseq_injective heq]
      · obtain ⟨V, hrot, hVU, hsum⟩ := exists_stRot_step h heq
        have hnext : (rseq U).sum - (rseq V).sum ≤ n := by
          have := rseq_sum_le h
          omega
        exact Relation.ReflTransGen.head hrot (reflTransGen_stRot_aux n V U hnext hVU)

/-- **The Stanley order is the reflexive-transitive closure of its covers.**  With
`stCover_iff_stRot` this says that `T ≤ U` exactly when `U` is reached from `T` by a
finite chain of the local moves of Lemma 4.5. -/
theorem reflTransGen_stRot_of_stanleyLe {T U : Tree} (h : stanleyLe T U) :
    Relation.ReflTransGen StRot T U :=
  reflTransGen_stRot_aux ((rseq U).sum - (rseq T).sum) T U (Nat.le_refl _) h

/-- The converse: a chain of covers stays inside the order. -/
theorem stanleyLe_of_reflTransGen_stRot : ∀ {T U : Tree},
    Relation.ReflTransGen StRot T U → stanleyLe T U := by
  intro T U h
  induction h with
  | refl => exact stanleyLe_of_rseq_eq rfl
  | tail _ hstep ih =>
      exact stanleyLe_trans ih (stCover_of_raisesOne (raisesOne_of_stRot hstep)).1

theorem stanleyLe_iff_reflTransGen_stRot {T U : Tree} :
    stanleyLe T U ↔ Relation.ReflTransGen StRot T U :=
  ⟨reflTransGen_stRot_of_stanleyLe, stanleyLe_of_reflTransGen_stRot⟩

/-! ## Witnesses

An equivalence is worthless if nothing satisfies either side, and a characterisation of
covers is worthless if every comparison is a cover.  Both are checked here. -/

/-- `((a·a)·a) ⋖ (a·(a·a))`: covers exist. -/
theorem stCover_three :
    StCover (node (node leaf leaf) leaf) (node leaf (node leaf leaf)) :=
  stCover_iff_stRot.mpr (StRot.root leaf leaf leaf)

theorem wword_three_lower :
    wword (node (node leaf leaf) leaf) = [true, false, true, false] := rfl

theorem wword_three_upper :
    wword (node leaf (node leaf leaf)) = [true, true, false, false] := rfl

/-- And the comparison really is a `DU ↦ UD` swap, as Lemma 4.4 says: `UDUD ↦ UUDD`. -/
theorem swapDU_three :
    SwapDU (node (node leaf leaf) leaf) (node leaf (node leaf leaf)) :=
  stCover_iff_swapDU.mp stCover_three

/-- The bottom of the four-leaf Stanley order. -/
def bot4 : Tree := node (node (node leaf leaf) leaf) leaf
/-- The top of the four-leaf Stanley order. -/
def top4 : Tree := node leaf (node leaf (node leaf leaf))

theorem rseq_bot4 : rseq bot4 = [0, 1, 1, 1] := rfl
theorem rseq_top4 : rseq top4 = [0, 1, 2, 3] := rfl

theorem stanleyLe_bot4_top4 : stanleyLe bot4 top4 := by
  refine stanleyLe_iff_getElem?.mpr ⟨rfl, ?_⟩
  intro i x y hx hy
  rw [rseq_bot4] at hx
  rw [rseq_top4] at hy
  match i with
  | 0 =>
      have e1 : x = 0 := (Option.some.inj hx).symm
      have e2 : y = 0 := (Option.some.inj hy).symm
      omega
  | 1 =>
      have e1 : x = 1 := (Option.some.inj hx).symm
      have e2 : y = 1 := (Option.some.inj hy).symm
      omega
  | 2 =>
      have e1 : x = 1 := (Option.some.inj hx).symm
      have e2 : y = 2 := (Option.some.inj hy).symm
      omega
  | 3 =>
      have e1 : x = 1 := (Option.some.inj hx).symm
      have e2 : y = 3 := (Option.some.inj hy).symm
      omega
  | (n + 4) =>
      have hn : ([0, 1, 1, 1] : List Nat)[n + 4]? = none := by
        cases n <;> rfl
      rw [hn] at hx
      exact absurd hx.symm (Option.some_ne_none x)

/-- **Not every comparison is a cover.**  The bottom and the top of the four-leaf
Stanley order are comparable, but they differ in two coordinates, and a cover changes
exactly one. -/
theorem not_stCover_bot4_top4 : ¬ StCover bot4 top4 := by
  intro h
  obtain ⟨i, x, hx, hU⟩ := stCover_iff_raisesOne.mp h
  have h2 : (rseq top4)[2]? = some 2 := rfl
  have h3 : (rseq top4)[3]? = some 3 := rfl
  have g2 : (rseq bot4)[2]? = some 1 := rfl
  have g3 : (rseq bot4)[3]? = some 1 := rfl
  by_cases hi2 : i = 2
  · subst hi2
    rw [hU, List.getElem?_set_ne (by omega), g3] at h3
    have := Option.some.inj h3
    omega
  · rw [hU, List.getElem?_set_ne hi2, g2] at h2
    have := Option.some.inj h2
    omega

end Tree
end ChowStanley
