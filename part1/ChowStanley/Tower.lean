import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-!
# Towers of twos, and the absorption inequalities

This file is the arithmetic layer of

  *The evaluation order of iterated exponentiation is the Stanley order*.

It defines `F h t` (a tower of `h` twos capped by `t`) and proves, over `Nat`:

* `Tower.succ_le_two_pow`  `c + 1 ≤ 2 ^ c`                       (Lemma 5.2, first part)
* `Tower.mul_le_pow`       `1 ≤ c → 2 ≤ y → c * y ≤ y ^ c`       (Lemma 5.2, second part)
* `Tower.F_pow_le`         `F h z ^ c ≤ F h (z ^ c)`             (Lemma 5.3, absorption)
* `Tower.pow_le_two_pow`   `c ^ y ≤ 2 ^ (y ^ c)`                 (Lemma 5.4, base absorption)
* `Tower.threshold`        `(2 * K ^ 2) ^ K < 2 ^ (2 * K ^ 2)`   (Lemma 8.1)

Everything is elementary and is proved by induction; nothing here is new.
-/

namespace ChowStanley
namespace Tower

/-- `F 0 t = t` and `F (h+1) t = 2 ^ F h t`: a tower of `h` twos capped by `t`. -/
def F : Nat → Nat → Nat
  | 0,       t => t
  | (h + 1), t => 2 ^ F h t

@[simp] theorem F_zero (t : Nat) : F 0 t = t := rfl
@[simp] theorem F_succ (h t : Nat) : F (h + 1) t = 2 ^ F h t := rfl

/-! ### Elementary facts about powers of two -/

/-- `c + 1 ≤ 2 ^ c`, i.e. `c ≤ 2 ^ (c-1)` for `c ≥ 1`.  Lemma 5.2, first part. -/
theorem succ_le_two_pow : ∀ c : Nat, c + 1 ≤ 2 ^ c
  | 0 => by decide
  | (c + 1) => by
      have ih := succ_le_two_pow c
      have hpos : 1 ≤ 2 ^ c := Nat.one_le_two_pow
      calc c + 1 + 1 ≤ 2 ^ c + 2 ^ c := by omega
        _ = 2 ^ (c + 1) := by ring

/-- `a < b → 2 ^ a < 2 ^ b`, proved without `Nat.pow_lt_pow_right`. -/
theorem two_pow_lt_two_pow {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b := by
  have h1 : 2 ^ a < 2 ^ (a + 1) := by
    have : (0 : Nat) < 2 ^ a := Nat.two_pow_pos a
    have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    omega
  have h2 : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) h
  omega

/-- `1 ≤ c → 2 ≤ y → c * y ≤ y ^ c`.  Lemma 5.2, second part. -/
theorem mul_le_pow {c y : Nat} (hc : 1 ≤ c) (hy : 2 ≤ y) : c * y ≤ y ^ c := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  have h1 : d + 1 ≤ 2 ^ d := succ_le_two_pow d
  have h2 : 2 ^ d ≤ y ^ d := Nat.pow_le_pow_left hy d
  calc (d + 1) * y ≤ (y ^ d) * y := Nat.mul_le_mul_right y (le_trans h1 h2)
    _ = y ^ (d + 1) := by ring

/-! ### Basic monotonicity of `F` -/

/-- `F (h+1) t = F h (2 ^ t)`: raising the argument and raising the height agree. -/
theorem F_succ_arg : ∀ (h t : Nat), F (h + 1) t = F h (2 ^ t)
  | 0,       _ => rfl
  | (h + 1), t => by
      show 2 ^ F (h + 1) t = 2 ^ F h (2 ^ t)
      rw [F_succ_arg h t]

theorem two_le_F {t : Nat} (ht : 2 ≤ t) : ∀ h, 2 ≤ F h t
  | 0 => ht
  | (h + 1) => by
      have ih := two_le_F ht h
      have : (2:Nat) ^ 1 ≤ 2 ^ F h t := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this

theorem F_mono_arg {a b : Nat} (hab : a ≤ b) : ∀ h, F h a ≤ F h b
  | 0 => hab
  | (h + 1) => Nat.pow_le_pow_right (by omega) (F_mono_arg hab h)

theorem F_strictMono_arg {a b : Nat} (hab : a < b) : ∀ h, F h a < F h b
  | 0 => hab
  | (h + 1) => two_pow_lt_two_pow (F_strictMono_arg hab h)

/-- `F h t ≤ F (h+1) t` for `2 ≤ t`. -/
theorem F_le_F_succ {t : Nat} (ht : 2 ≤ t) (h : Nat) : F h t ≤ F (h + 1) t := by
  have h2 : 2 ≤ F h t := two_le_F ht h
  have : F h t + 1 ≤ 2 ^ F h t := succ_le_two_pow (F h t)
  simpa [F_succ] using Nat.le_of_lt (by omega : F h t < 2 ^ F h t)

theorem F_mono_height {t : Nat} (ht : 2 ≤ t) {h k : Nat} (hk : h ≤ k) : F h t ≤ F k t := by
  induction k with
  | zero => simp [Nat.le_zero.mp hk]
  | succ k ih =>
      rcases Nat.lt_or_ge h (k + 1) with hlt | hge
      · exact le_trans (ih (by omega)) (F_le_F_succ ht k)
      · have : h = k + 1 := by omega
        simp [this]

/-! ### The two absorption lemmas -/

/-- **Absorption** (Lemma 5.3): a power outside a tower can be pushed into its argument. -/
theorem F_pow_le {z c : Nat} (hz : 2 ≤ z) (hc : 1 ≤ c) : ∀ h, F h z ^ c ≤ F h (z ^ c)
  | 0 => by simp
  | (h + 1) => by
      have ih := F_pow_le hz hc h
      have hFz : 2 ≤ F h z := two_le_F hz h
      have step1 : c * F h z ≤ (F h z) ^ c := mul_le_pow hc hFz
      have step2 : (F h z) ^ c ≤ F h (z ^ c) := ih
      have : (2:Nat) ^ (c * F h z) ≤ 2 ^ (F h (z ^ c)) :=
        Nat.pow_le_pow_right (by omega) (le_trans step1 step2)
      calc F (h + 1) z ^ c = (2 ^ F h z) ^ c := rfl
        _ = 2 ^ (F h z * c) := by rw [← pow_mul]
        _ = 2 ^ (c * F h z) := by rw [Nat.mul_comm]
        _ ≤ 2 ^ (F h (z ^ c)) := this
        _ = F (h + 1) (z ^ c) := rfl

/-- **Absorbing the base** (Lemma 5.4): `c ^ y ≤ 2 ^ (y ^ c)` for `c, y ≥ 2`. -/
theorem pow_le_two_pow {c y : Nat} (hc : 2 ≤ c) (hy : 2 ≤ y) : c ^ y ≤ 2 ^ (y ^ c) := by
  have h1 : c ≤ 2 ^ c := le_trans (by omega) (succ_le_two_pow c)
  have h2 : c ^ y ≤ (2 ^ c) ^ y := Nat.pow_le_pow_left h1 y
  have h3 : c * y ≤ y ^ c := mul_le_pow (by omega) hy
  calc c ^ y ≤ (2 ^ c) ^ y := h2
    _ = 2 ^ (c * y) := by rw [← pow_mul]
    _ ≤ 2 ^ (y ^ c) := Nat.pow_le_pow_right (by omega) h3

/-! ### The threshold -/

/-- **Threshold** (Lemma 8.1): with `M = 2 K²` one has `M ^ K < 2 ^ M`. -/
theorem threshold {K : Nat} (hK : 1 ≤ K) : (2 * K ^ 2) ^ K < 2 ^ (2 * K ^ 2) := by
  obtain ⟨d, rfl⟩ : ∃ d, K = d + 1 := ⟨K - 1, by omega⟩
  have hd : d + 1 ≤ 2 ^ d := succ_le_two_pow d
  -- 2 * K² ≤ 2 ^ (2d+1)
  have hsq : (d + 1) ^ 2 ≤ (2 ^ d) ^ 2 := Nat.pow_le_pow_left hd 2
  have hM : 2 * (d + 1) ^ 2 ≤ 2 ^ (2 * d + 1) := by
    have : (2 ^ d) ^ 2 = 2 ^ (2 * d) := by rw [← pow_mul, Nat.mul_comm]
    calc 2 * (d + 1) ^ 2 ≤ 2 * (2 ^ d) ^ 2 := by omega
      _ = 2 * 2 ^ (2 * d) := by rw [this]
      _ = 2 ^ (2 * d + 1) := by ring
  -- したがって M^K ≤ 2^((2d+1)(d+1)) < 2^(2(d+1)²)
  have hexp : (2 * d + 1) * (d + 1) < 2 * (d + 1) ^ 2 := by ring_nf; omega
  calc (2 * (d + 1) ^ 2) ^ (d + 1)
      ≤ (2 ^ (2 * d + 1)) ^ (d + 1) := Nat.pow_le_pow_left hM (d + 1)
    _ = 2 ^ ((2 * d + 1) * (d + 1)) := by rw [← pow_mul]
    _ < 2 ^ (2 * (d + 1) ^ 2) := two_pow_lt_two_pow hexp

end Tower
end ChowStanley
