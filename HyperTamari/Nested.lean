import HyperTamari.General

/-!
# The strict nested bound

For every rank `r ≥ 4`, every `x ≥ 2` and all `y, z ≥ 1`,
$$H_r\bigl(H_r(x,y),z\bigr) \;<\; H_r(x,\,y+z).$$

This is Theorem I of S. Saibian, *A theorem for Knuth-arrows* (2014), and in its non-strict
form Lemma 4.8 of Leonardis, d'Atri and Caldarola (2022). The proof of the latter in its
published version assumes a base `A ≥ 3` and leaves `A = 2` to the reader, while the
Stanley order needs the bound at `x = 2` (a leaf labelled `2`). The proof below covers
every `x ≥ 2` and is the one given in the appendix of the paper.

* Rank 4 (`nested_rank4`). Put `W = H₄(x, y-1)` and `T = H₄(x, y) = x^W`. The invariant
  `W · (H₄(T, z) + 1) ≤ H₄(x, y+z)` holds at `z = 1` because `W (T+1) < T² ≤ x^T`, and it
  is preserved because `x^W ≥ W + 1`.
* Rank `s + 1` from rank `s ≥ 4` (`nested_step`). With `W = H_{s+1}(x, y-1)` and
  `T = H_{s+1}(x, y) = H_s(x, W)`, the invariant is `W + H_{s+1}(T, z) < H_{s+1}(x, y+z)`.
  The step uses the bound at rank `s` once, and `H_{s-1}(x, v) ≥ 2v`.

Only the non-strict bound at rank `s` is used in the step.
-/

namespace HyperTamari

/-! ## Two elementary inequalities -/

/-- `n + 1 ≤ x ^ n` for `x ≥ 2`. -/
theorem succ_le_pow {x : Nat} (hx : 2 ≤ x) : ∀ n : Nat, n + 1 ≤ x ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : x ^ n * 2 ≤ x ^ n * x := Nat.mul_le_mul_left _ hx
      rw [pow_succ]
      omega

/-- `1 ≤ H_r(x, n)` for every `n`, when `x ≥ 2` and `r ≥ 3`. -/
theorem one_le_hyper {x : Nat} (hx : 2 ≤ x) {r : Nat} (hr : 3 ≤ r) (n : Nat) :
    1 ≤ hyper r x n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
    simp
  · have := two_le_hyper hx (show 2 ≤ r by omega) hn
    omega

/-! ## Rank four -/

/-- The base of the rank-four invariant: `W · (x^W + 1) ≤ x^(x^W)` for `x ≥ 2`, `W ≥ 1`. -/
theorem nested4_base {x : Nat} (hx : 2 ≤ x) {W : Nat} (hW : 1 ≤ W) :
    W * (x ^ W + 1) ≤ x ^ (x ^ W) := by
  have hWT : W + 1 ≤ x ^ W := succ_le_pow hx W
  -- `W (T + 1) < T · T`
  have h1 : (W + 1) * (x ^ W + 1) ≤ x ^ W * (x ^ W + 1) := Nat.mul_le_mul_right _ hWT
  have e1 : (W + 1) * (x ^ W + 1) = W * x ^ W + W + x ^ W + 1 := by ring
  have e2 : x ^ W * (x ^ W + 1) = x ^ W * x ^ W + x ^ W := by ring
  have e3 : W * (x ^ W + 1) = W * x ^ W + W := by ring
  -- `T · T = x^(W+W) ≤ x^T`, since `2W ≤ 2^W ≤ x^W`
  have h2 : W + W ≤ x ^ W := by
    have a := two_mul_le_two_pow hW
    have b : 2 ^ W ≤ x ^ W := Nat.pow_le_pow_left hx W
    omega
  have h3 : x ^ W * x ^ W ≤ x ^ (x ^ W) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) h2
  rw [e1, e2] at h1
  rw [e3]
  omega

/-- The rank-four invariant, in terms of `tet`: with `W = x↑↑y'` and `T = x↑↑(y'+1)`,
`W · (T↑↑z + 1) ≤ x↑↑(y'+1+z)` for all `z ≥ 1`. -/
theorem nested4_aux {x : Nat} (hx : 2 ≤ x) (y' : Nat) :
    ∀ z : Nat, 1 ≤ z →
      tet x y' * (tet (tet x (y' + 1)) z + 1) ≤ tet x (y' + 1 + z) := by
  have hW : 1 ≤ tet x y' := one_le_tet hx y'
  have hT : 2 ≤ tet x (y' + 1) := by
    have := base_le_tet hx (n := y' + 1) (by omega); omega
  intro z hz
  induction z with
  | zero => omega
  | succ z ih =>
      rcases Nat.eq_zero_or_pos z with rfl | hz'
      · -- `z = 1`: the base inequality
        have e1 : tet (tet x (y' + 1)) (0 + 1) = tet x (y' + 1) := by
          rw [tet_succ, tet_zero, pow_one]
        have e2 : tet x (y' + 1 + (0 + 1)) = x ^ (x ^ tet x y') := by
          rw [show y' + 1 + (0 + 1) = y' + 1 + 1 from rfl, tet_succ, tet_succ]
        rw [e1, e2, tet_succ]
        exact nested4_base hx hW
      · have hIH := ih hz'
        set W := tet x y' with hWdef
        set T := tet x (y' + 1) with hTdef
        set h := tet T z with hhdef
        set M := tet x (y' + 1 + z) with hMdef
        have hh : 1 ≤ h := one_le_tet hT z
        have hTW : T = x ^ W := by rw [hTdef, tet_succ]
        -- the left-hand side is `x^(W h)`
        have eL : tet T (z + 1) = x ^ (W * h) := by
          rw [tet_succ, ← hhdef, hTW, ← pow_mul]
        have eR : tet x (y' + 1 + (z + 1)) = x ^ M := by
          rw [show y' + 1 + (z + 1) = y' + 1 + z + 1 from by omega, tet_succ]
        rw [eL, eR]
        set P := x ^ (W * h) with hPdef
        have f1 : W + 1 ≤ x ^ W := succ_le_pow hx W
        have f2 : x ^ W ≤ P := by
          have : W ≤ W * h := Nat.le_mul_of_pos_right W hh
          exact Nat.pow_le_pow_right (by omega) this
        have f3 : P * (W + 1) ≤ P * x ^ W := Nat.mul_le_mul_left _ f1
        have f4 : P * x ^ W = x ^ (W * h + W) := by rw [hPdef, ← pow_add]
        have f5 : x ^ (W * h + W) ≤ x ^ M := by
          have e : W * (h + 1) = W * h + W := by ring
          exact Nat.pow_le_pow_right (by omega) (by rw [← e]; exact hIH)
        have e3 : W * (P + 1) = P * W + W := by ring
        have e4 : P * (W + 1) = P * W + P := by ring
        rw [e3]
        rw [e4] at f3
        omega

/-- **The strict nested bound at rank four.** -/
theorem nested_rank4 {x y z : Nat} (hx : 2 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    hyper 4 (hyper 4 x y) z < hyper 4 x (y + z) := by
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  simp only [← tet_eq_hyper4]
  have key := nested4_aux hx y' z hz
  have hW : 1 ≤ tet x y' := one_le_tet hx y'
  have h1 : 1 * (tet (tet x (y' + 1)) z + 1) ≤ tet x y' * (tet (tet x (y' + 1)) z + 1) :=
    Nat.mul_le_mul_right _ hW
  omega

/-! ## From rank `s` to rank `s + 1` -/

/-- The inductive step. If the non-strict nested bound holds at rank `s ≥ 4`, then at rank
`s + 1`, with `W = H_{s+1}(x, y')` and `T = H_{s+1}(x, y'+1)`,
`W + H_{s+1}(T, z) < H_{s+1}(x, y'+1+z)` for all `z ≥ 1`. -/
theorem nested_step {s : Nat} (hs : 4 ≤ s)
    (prev : ∀ x y z : Nat, 2 ≤ x → 1 ≤ y → 1 ≤ z →
      hyper s (hyper s x y) z ≤ hyper s x (y + z))
    {x : Nat} (hx : 2 ≤ x) (y' : Nat) :
    ∀ z : Nat, 1 ≤ z →
      hyper (s + 1) x y' + hyper (s + 1) (hyper (s + 1) x (y' + 1)) z
        < hyper (s + 1) x (y' + 1 + z) := by
  have hW : 1 ≤ hyper (s + 1) x y' := one_le_hyper hx (by omega) y'
  have hTW : hyper (s + 1) x (y' + 1) = hyper s x (hyper (s + 1) x y') := hyper_succ s x y'
  have hT : 2 ≤ hyper (s + 1) x (y' + 1) := two_le_hyper hx (by omega) (by omega)
  intro z hz
  induction z with
  | zero => omega
  | succ z ih =>
      rcases Nat.eq_zero_or_pos z with rfl | hz'
      · -- `z = 1`: `W + T < 2T ≤ x·T ≤ H_s(x, T)`
        rw [hyper_one_arg (show 2 ≤ s + 1 by omega)]
        rw [show y' + 1 + (0 + 1) = y' + 1 + 1 from rfl, hyper_succ s x (y' + 1)]
        set W := hyper (s + 1) x y'
        set T := hyper (s + 1) x (y' + 1)
        have a : W + 1 ≤ T := by rw [hTW]; exact succ_le_hyper hx (by omega) hW
        have b : hyper 2 x T ≤ hyper s x T := two_le_rank_hyper hx (by omega) (by omega)
        have c : 2 * T ≤ x * T := Nat.mul_le_mul_right _ hx
        rw [hyper_two] at b
        omega
      · have hIH := ih hz'
        set W := hyper (s + 1) x y' with hWdef
        set T := hyper (s + 1) x (y' + 1) with hTdef
        set h := hyper (s + 1) T z with hhdef
        set M := hyper (s + 1) x (y' + 1 + z) with hMdef
        have hh : 2 ≤ h := two_le_hyper hT (by omega) hz'
        have eL : hyper (s + 1) T (z + 1) = hyper s T h := hyper_succ s T z
        have eR : hyper (s + 1) x (y' + 1 + (z + 1)) = hyper s x M := by
          rw [show y' + 1 + (z + 1) = y' + 1 + z + 1 from by omega, hyper_succ]
        rw [eL, eR]
        -- `M = m + 1` with `W + h ≤ m`
        obtain ⟨m, hm⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
        have hWh : W + h ≤ m := by omega
        -- `H_s(T, h) ≤ H_s(x, W + h) ≤ H_s(x, m)`
        have g1 : hyper s T h ≤ hyper s x (W + h) := by
          have := prev x W h hx hW (by omega)
          rwa [← hTW] at this
        have g2 : hyper s x (W + h) ≤ hyper s x m :=
          hyper_mono_arg hx (by omega) (by omega) hWh
        -- `H_s(x, m + 1) = H_{s-1}(x, V) ≥ 2V` with `V = H_s(x, m) ≥ m > W`
        obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
        rw [hm, hyper_succ]
        set V := hyper (u + 1) x m with hVdef
        have g3 : m ≤ V := self_le_hyper hx (by omega) (by omega)
        have g4 : hyper 2 x V ≤ hyper u x V := two_le_rank_hyper hx (by omega) (by omega)
        have g5 : 2 * V ≤ x * V := Nat.mul_le_mul_right _ hx
        rw [hyper_two] at g4
        omega

/-! ## Every rank -/

/-- **The strict nested bound at every rank `t + 4`.** -/
theorem nested_strict : ∀ t x y z : Nat, 2 ≤ x → 1 ≤ y → 1 ≤ z →
    hyper (t + 4) (hyper (t + 4) x y) z < hyper (t + 4) x (y + z)
  | 0, _, _, _, hx, hy, hz => nested_rank4 hx hy hz
  | t + 1, x, y, z, hx, hy, hz => by
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      have key := nested_step (s := t + 4) (by omega)
        (fun a b c ha hb hc => Nat.le_of_lt (nested_strict t a b c ha hb hc)) hx y' z hz
      have hW : 1 ≤ hyper (t + 4 + 1) x y' := one_le_hyper hx (by omega) y'
      show hyper (t + 4 + 1) (hyper (t + 4 + 1) x (y' + 1)) z
        < hyper (t + 4 + 1) x (y' + 1 + z)
      omega

/-- **Theorem (strict nested bound).** For `r ≥ 4`, `x ≥ 2` and `y, z ≥ 1`,
`H_r(H_r(x, y), z) < H_r(x, y + z)`. -/
theorem nested_bound_strict {r : Nat} (hr : 4 ≤ r) {x y z : Nat}
    (hx : 2 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    hyper r (hyper r x y) z < hyper r x (y + z) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 4 := ⟨r - 4, by omega⟩
  exact nested_strict t x y z hx hy hz

/-- The non-strict form (Lemma 4.8 of Leonardis–d'Atri–Caldarola, here for every `x ≥ 2`). -/
theorem nested_bound {r : Nat} (hr : 4 ≤ r) {x y z : Nat}
    (hx : 2 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    hyper r (hyper r x y) z ≤ hyper r x (y + z) :=
  Nat.le_of_lt (nested_bound_strict hr hx hy hz)

/-- The bound fails at rank three: `(3^3)^3 = 3^9 > 3^6`. -/
theorem nested_bound_fails_rank3 :
    ¬ (hyper 3 (hyper 3 3 3) 3 ≤ hyper 3 3 (3 + 3)) := by
  rw [hyper_three, hyper_three, hyper_three]
  decide

/-- An instance with base `2`: `(2↑↑2)↑↑3 < 2↑↑5`. At these arguments the last step of the
published proof of Lemma 4.6 of Leonardis–d'Atri–Caldarola would need `3↑↑2 ≤ 2↑↑3`,
which is false (`27 > 16`). -/
theorem nested_bound_two_instance :
    hyper 4 (hyper 4 2 2) 3 < hyper 4 2 (2 + 3) :=
  nested_bound_strict (by omega) (by omega) (by omega) (by omega)

end HyperTamari

#print axioms HyperTamari.succ_le_pow
#print axioms HyperTamari.one_le_hyper
#print axioms HyperTamari.nested4_base
#print axioms HyperTamari.nested4_aux
#print axioms HyperTamari.nested_rank4
#print axioms HyperTamari.nested_step
#print axioms HyperTamari.nested_strict
#print axioms HyperTamari.nested_bound_strict
#print axioms HyperTamari.nested_bound
#print axioms HyperTamari.nested_bound_fails_rank3
#print axioms HyperTamari.nested_bound_two_instance
