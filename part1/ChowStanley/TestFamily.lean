import ChowStanley.Main

/-!
# The uniform finite test family

Section 9 of the paper: the uniform bound on `K_i(T)` and the finite test family.
The direction formalised is the substantive one — if the displayed inequalities hold
then `T ≤_St U`. The converse is the inclusion of Chow, which the paper cites.
-/

namespace ChowStanley
namespace Tower

/-- `2z ≤ 2^z` for `z ≥ 2`. -/
theorem two_mul_le_two_pow : ∀ z : Nat, 2 ≤ z → 2 * z ≤ 2 ^ z := by
  intro z
  induction z with
  | zero => omega
  | succ z ih =>
      intro _
      rcases Nat.lt_or_ge z 2 with h | h
      · have hz : z = 0 ∨ z = 1 := by omega
        rcases hz with rfl | rfl
        · decide
        · decide
      · have hz := ih h
        have h2 : (2:Nat) ≤ 2 ^ z := by
          calc (2:Nat) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ z := Nat.pow_le_pow_right (by omega) (by omega)
        have hsplit : (2:Nat) ^ (z + 1) = 2 ^ z + 2 ^ z := by ring
        omega

/-- `F h 2 ^ 2 ≤ 2 ^ (F h 2)`. -/
theorem F_sq_le : ∀ h : Nat, F h 2 ^ 2 ≤ 2 ^ F h 2
  | 0 => by decide
  | (h + 1) => by
      have hw : 2 ≤ F h 2 := two_le_F (by omega) h
      have hb : F (h + 1) 2 = 2 ^ F h 2 := rfl
      rw [hb]
      calc (2 ^ F h 2) ^ 2 = 2 ^ (F h 2 * 2) := by rw [← pow_mul]
        _ = 2 ^ (2 * F h 2) := by rw [Nat.mul_comm]
        _ ≤ 2 ^ (2 ^ F h 2) := Nat.pow_le_pow_right (by omega) (two_mul_le_two_pow _ hw)

/-- `F h 2 · F h 2 ≤ F (h+1) 2`. -/
theorem F_sq_le' (h : Nat) : F h 2 * F h 2 ≤ F (h + 1) 2 := by
  have := F_sq_le h
  calc F h 2 * F h 2 = F h 2 ^ 2 := by ring
    _ ≤ 2 ^ F h 2 := this
    _ = F (h + 1) 2 := rfl

/-- **Lemma 9.1(i)**: `F p 2 · F q 2 ≤ F (p+q+1) 2`. -/
theorem F_mul_le (p q : Nat) : F p 2 * F q 2 ≤ F (p + q + 1) 2 := by
  rcases Nat.le_total p q with hpq | hpq
  · calc F p 2 * F q 2 ≤ F q 2 * F q 2 :=
          Nat.mul_le_mul_right _ (F_mono_height (by omega) hpq)
      _ ≤ F (q + 1) 2 := F_sq_le' q
      _ ≤ F (p + q + 1) 2 := F_mono_height (by omega) (by omega)
  · calc F p 2 * F q 2 ≤ F p 2 * F p 2 :=
          Nat.mul_le_mul_left _ (F_mono_height (by omega) hpq)
      _ ≤ F (p + 1) 2 := F_sq_le' p
      _ ≤ F (p + q + 1) 2 := F_mono_height (by omega) (by omega)

/-- **Lemma 9.1(ii)**: `(F p 2) ^ (F q 2) ≤ F (p+q+1) 2`. -/
theorem F_pow_F_le (p q : Nat) : F p 2 ^ F q 2 ≤ F (p + q + 1) 2 := by
  cases p with
  | zero =>
      have h0 : F 0 2 = 2 := rfl
      have hidx : (0:Nat) + q + 1 = q + 1 := by omega
      rw [h0, hidx]
      exact le_of_eq rfl
  | succ p =>
      have hb : F (p + 1) 2 = 2 ^ F p 2 := rfl
      have hidx : p + 1 + q + 1 = p + q + 2 := by omega
      rw [hidx, hb]
      calc (2 ^ F p 2) ^ F q 2 = 2 ^ (F p 2 * F q 2) := by rw [← pow_mul]
        _ ≤ 2 ^ (F (p + q + 1) 2) := Nat.pow_le_pow_right (by omega) (F_mul_le p q)
        _ = F (p + q + 2) 2 := rfl

end Tower

namespace Tree

theorem one_le_numLeaves : ∀ T : Tree, 1 ≤ T.numLeaves
  | leaf => Nat.le_refl 1
  | node L R => by
      have h1 := one_le_numLeaves L
      have h2 := one_le_numLeaves R
      have h' : (node L R).numLeaves = L.numLeaves + R.numLeaves := rfl
      omega

/-- **Lemma 9.2**: a tree with `k+1` leaves has all-`2` value at most `F k 2`. -/
theorem two_le_F : ∀ (T : Tree) (k : Nat), T.numLeaves = k + 1 → T.two ≤ Tower.F k 2
  | leaf, k, hk => by
      have hk0 : k = 0 := by
        have h' : (1:Nat) = k + 1 := hk
        omega
      subst hk0; exact le_of_eq rfl
  | node L R, k, hk => by
      obtain ⟨p, hp⟩ : ∃ p, L.numLeaves = p + 1 :=
        ⟨L.numLeaves - 1, by have := one_le_numLeaves L; omega⟩
      obtain ⟨q, hq⟩ : ∃ q, R.numLeaves = q + 1 :=
        ⟨R.numLeaves - 1, by have := one_le_numLeaves R; omega⟩
      have hk' : k = p + q + 1 := by
        have h' : L.numLeaves + R.numLeaves = k + 1 := hk
        omega
      subst hk'
      have hL := two_le_F L p hp
      have hR := two_le_F R q hq
      have hFp : 2 ≤ Tower.F p 2 := Tower.two_le_F (by omega) p
      calc (node L R).two = L.two ^ R.two := rfl
        _ ≤ (Tower.F p 2) ^ R.two := Nat.pow_le_pow_left hL _
        _ ≤ (Tower.F p 2) ^ (Tower.F q 2) := Nat.pow_le_pow_right (by omega) hR
        _ ≤ Tower.F (p + q + 1) 2 := Tower.F_pow_F_le p q

end Tree
end ChowStanley

namespace ChowStanley

namespace Tree

theorem rseq_cons : ∀ T : Tree, ∃ t, T.rseq = 0 :: t
  | leaf => ⟨[], rfl⟩
  | node L R => by
      obtain ⟨t, ht⟩ := rseq_cons L
      exact ⟨t ++ R.rseq.map (· + 1), by simp [rseq, ht]⟩

/-- **Lemma 2.7**: the first two right depths are `0` and `1`, for every tree. -/
theorem rseq_cons_two : ∀ (T : Tree), 2 ≤ T.numLeaves → ∃ t, T.rseq = 0 :: 1 :: t
  | leaf, h => by
      have h' : (2:Nat) ≤ 1 := h
      exact absurd h' (by decide)
  | node L R, _ => by
      cases L with
      | leaf =>
          obtain ⟨t, ht⟩ := rseq_cons R
          exact ⟨t.map (· + 1), by simp [rseq, ht]⟩
      | node A B =>
          have h2 : 2 ≤ (node A B).numLeaves := by
            have hA := one_le_numLeaves A
            have hB := one_le_numLeaves B
            have h' : (node A B).numLeaves = A.numLeaves + B.numLeaves := rfl
            omega
          obtain ⟨u, hu⟩ := rseq_cons_two (node A B) h2
          exact ⟨u ++ R.rseq.map (· + 1), by
            show (node A B).rseq ++ (R.rseq.map (· + 1)) = 0 :: 1 :: (u ++ _)
            rw [hu]; simp⟩

end Tree

namespace PTree

/-- The number of leaves in the sibling subtrees along the path to the hole. -/
def sibLeaves : PTree → Nat
  | hole => 0
  | left P R => P.sibLeaves + R.numLeaves
  | right L P => P.sibLeaves + L.numLeaves

theorem sibLeaves_succ : ∀ P : PTree, P.sibLeaves + 1 = P.tree.numLeaves
  | hole => rfl
  | left P R => by
      have hp := sibLeaves_succ P
      have h1 : (left P R).sibLeaves = P.sibLeaves + R.numLeaves := rfl
      have h2 : (left P R).tree.numLeaves = P.tree.numLeaves + R.numLeaves := rfl
      omega
  | right L P => by
      have hp := sibLeaves_succ P
      have h1 : (right L P).sibLeaves = P.sibLeaves + L.numLeaves := rfl
      have h2 : (right L P).tree.numLeaves = L.numLeaves + P.tree.numLeaves := rfl
      omega

theorem K_eq_one_of_sibLeaves_zero : ∀ P : PTree, P.sibLeaves = 0 → P.K = 1
  | hole, _ => rfl
  | left P R, h => by
      have hR := Tree.one_le_numLeaves R
      have h' : P.sibLeaves + R.numLeaves = 0 := h
      omega
  | right L P, h => by
      have hL := Tree.one_le_numLeaves L
      have h' : P.sibLeaves + L.numLeaves = 0 := h
      omega

/-- **Lemma 9.3**: `K_i(T) ≤ F_{n-2}(2)`, in the form `sibLeaves = m+1 → K ≤ F m 2`. -/
theorem K_le : ∀ (P : PTree) (m : Nat), P.sibLeaves = m + 1 → P.K ≤ Tower.F m 2
  | hole, m, h => by
      have h' : (0:Nat) = m + 1 := h
      omega
  | left P R, m, h => by
      obtain ⟨q, hq⟩ : ∃ q, R.numLeaves = q + 1 :=
        ⟨R.numLeaves - 1, by have := Tree.one_le_numLeaves R; omega⟩
      have hR : R.two ≤ Tower.F q 2 := Tree.two_le_F R q hq
      cases hs : P.sibLeaves with
      | zero =>
          have hK1 : P.K = 1 := K_eq_one_of_sibLeaves_zero P hs
          have hm : m = q := by
            have h' : P.sibLeaves + R.numLeaves = m + 1 := h
            omega
          subst hm; simpa [K, hK1] using hR
      | succ s =>
          have hP := K_le P s hs
          have hm : m = s + q + 1 := by
            have h' : P.sibLeaves + R.numLeaves = m + 1 := h
            omega
          subst hm
          calc (left P R).K = P.K * R.two := rfl
            _ ≤ Tower.F s 2 * Tower.F q 2 := Nat.mul_le_mul hP hR
            _ ≤ Tower.F (s + q + 1) 2 := Tower.F_mul_le s q
  | right L P, m, h => by
      obtain ⟨q, hq⟩ : ∃ q, L.numLeaves = q + 1 :=
        ⟨L.numLeaves - 1, by have := Tree.one_le_numLeaves L; omega⟩
      have hL : L.two ≤ Tower.F q 2 := Tree.two_le_F L q hq
      cases hs : P.sibLeaves with
      | zero =>
          have hK1 : P.K = 1 := K_eq_one_of_sibLeaves_zero P hs
          have hm : m = q := by
            have h' : P.sibLeaves + L.numLeaves = m + 1 := h
            omega
          subst hm; simpa [K, hK1] using hL
      | succ s =>
          have hP := K_le P s hs
          have hm : m = s + q + 1 := by
            have h' : P.sibLeaves + L.numLeaves = m + 1 := h
            omega
          subst hm
          calc (right L P).K = P.K * L.two := rfl
            _ ≤ Tower.F s 2 * Tower.F q 2 := Nat.mul_le_mul hP hL
            _ ≤ Tower.F (s + q + 1) 2 := Tower.F_mul_le s q

end PTree
end ChowStanley

namespace ChowStanley

/-- The uniform threshold `M_n = 2 F_{n-2}(2)^2` of Corollary 1.3. -/
def Mn (n : Nat) : Nat := 2 * (Tower.F (n - 2) 2) ^ 2

theorem two_le_Mn (n : Nat) : 2 ≤ Mn n := by
  have h := Tower.two_le_F (by omega : (2:Nat) ≤ 2) (n - 2)
  have : 1 ≤ (Tower.F (n - 2) 2) ^ 2 := by
    calc (1:Nat) = 1 ^ 2 := by norm_num
      _ ≤ (Tower.F (n - 2) 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hMn : Mn n = 2 * (Tower.F (n - 2) 2) ^ 2 := rfl
  omega

/-- Separation with any uniform bound on `K`, not only with `K = K_i(U)`. -/
theorem PTree.separation_of_le {P Q : PTree} (h : Q.rdepth < P.rdepth)
    {K : Nat} (hK1 : 1 ≤ K) (hK : Q.K ≤ K) :
    Q.val (2 * K ^ 2) < P.val (2 * K ^ 2) := by
  set M := 2 * K ^ 2 with hM
  have hKsq : 1 ≤ K ^ 2 := by
    calc (1:Nat) = 1 ^ 2 := by norm_num
      _ ≤ K ^ 2 := Nat.pow_le_pow_left hK1 2
  have h2M : 2 ≤ M := by omega
  have hup : Q.val M ≤ Tower.F Q.rdepth (M ^ Q.K) := PTree.val_le_F_rdepth h2M Q
  have hlo : Tower.F P.rdepth M ≤ P.val M := PTree.F_rdepth_le_val h2M P
  have hthr : M ^ K < 2 ^ M := Tower.threshold hK1
  have hmono : M ^ Q.K ≤ M ^ K := Nat.pow_le_pow_right (by omega) hK
  have hstrict : Tower.F Q.rdepth (M ^ Q.K) < Tower.F Q.rdepth (2 ^ M) :=
    Tower.F_strictMono_arg (by omega) _
  have heq : Tower.F Q.rdepth (2 ^ M) = Tower.F (Q.rdepth + 1) M :=
    (Tower.F_succ_arg Q.rdepth M).symm
  have hh : Tower.F (Q.rdepth + 1) M ≤ Tower.F P.rdepth M :=
    Tower.F_mono_height h2M h
  calc Q.val M ≤ Tower.F Q.rdepth (M ^ Q.K) := hup
    _ < Tower.F Q.rdepth (2 ^ M) := hstrict
    _ = Tower.F (Q.rdepth + 1) M := heq
    _ ≤ Tower.F P.rdepth M := hh
    _ ≤ P.val M := hlo

namespace Tree

/-- **Corollary 1.3**, the substantive direction: if the `n-2` displayed inequalities
hold then `T ≤_St U`.  The assignments are indexed `2 ≤ i < n` here, matching
`3 ≤ i ≤ n` in the paper's 1-based numbering. -/
theorem stanleyLe_of_testFamily {T U : Tree}
    (hn : T.numLeaves = U.numLeaves) (hn2 : 2 ≤ T.numLeaves)
    (h : ∀ i, 2 ≤ i → i < T.numLeaves →
      T.ev (sepAssign T.numLeaves i (Mn T.numLeaves))
        ≤ U.ev (sepAssign T.numLeaves i (Mn T.numLeaves))) :
    stanleyLe T U := by
  refine ⟨by simp [rseq_length, hn], ?_⟩
  intro i hi hi'
  by_contra hcon
  have hlt : U.rseq[i]'hi' < T.rseq[i]'hi := by omega
  have hiT : i < T.numLeaves := by simpa [rseq_length] using hi
  -- 添字 0,1 では両者の右深さが一致するので i ≥ 2
  have hi2 : 2 ≤ i := by
    by_contra hlt2
    obtain ⟨tT, hT2⟩ := rseq_cons_two T hn2
    obtain ⟨tU, hU2⟩ := rseq_cons_two U (by omega)
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · have e1 : T.rseq[0]'hi = 0 := by simp [hT2]
      have e2 : U.rseq[0]'hi' = 0 := by simp [hU2]
      omega
    · have e1 : T.rseq[1]'hi = 1 := by simp [hT2]
      have e2 : U.rseq[1]'hi' = 1 := by simp [hU2]
      omega
  -- 右深さの比較を pointed tree に移す
  have hpT : i < T.points.length := by simpa [points_length] using hiT
  have hpU : i < U.points.length := by simpa [points_length, hn] using hiT
  set P := T.points[i]'hpT with hP
  set Q := U.points[i]'hpU with hQ
  have hdT : P.rdepth = T.rseq[i]'hi := rdepth_points_getElem T i _
  have hdU : Q.rdepth = U.rseq[i]'hi' := rdepth_points_getElem U i _
  have hrd : Q.rdepth < P.rdepth := by rw [hdT, hdU]; exact hlt
  -- K の一様上界
  have hsib : Q.sibLeaves = (T.numLeaves - 2) + 1 := by
    have := PTree.sibLeaves_succ Q
    have htree : Q.tree = U := mem_points_tree U Q (by simp [hQ])
    rw [htree] at this; omega
  have hKle : Q.K ≤ Tower.F (T.numLeaves - 2) 2 := PTree.K_le Q _ hsib
  have hK1 : 1 ≤ Tower.F (T.numLeaves - 2) 2 := by
    have := Tower.two_le_F (by omega : (2:Nat) ≤ 2) (T.numLeaves - 2); omega
  have hsep : Q.val (Mn T.numLeaves) < P.val (Mn T.numLeaves) :=
    PTree.separation_of_le hrd hK1 hKle
  -- 割り当てでの評価に戻す
  have hMT : T.ev (sepAssign T.numLeaves i (Mn T.numLeaves)) = P.val (Mn T.numLeaves) :=
    ev_set T i _ hiT
  have hMU : U.ev (sepAssign T.numLeaves i (Mn T.numLeaves)) = Q.val (Mn T.numLeaves) := by
    rw [hn]; exact ev_set U i _ (by omega)
  have := h i hi2 hiT
  rw [hMT, hMU] at this
  omega

end Tree
end ChowStanley
