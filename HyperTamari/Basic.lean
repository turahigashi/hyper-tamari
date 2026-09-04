import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-
# 超演算の括弧付けと Tamari 順序

本ファイルは Hyperoperation–Tamari 不等式の**定式化・領域の確定・rank 3 の完全解**を機械検証する。

## 先行研究（2026-09-04 の照合）

* **既知（folklore）** rank 3 の $(x^y)^z\le x^{y^z}$ と「right comb が最大」。
* **既知** B. Csákány, T. Waldhauser,
  *Associative spectra of binary operations*（arXiv:1102.2124）§3.4
  「指数演算は **Catalan** である」＝**相異なる括弧付けは相異なる値**を与える
  （ただし葉に**相異なる素数**を置く場合）。
  彼らが扱うのは「**いくつ**異なる値が出るか」であって「**どういう順序**か」ではない。
* **見つからなかった** 値の順序が **Tamari 順序と整合**すること、および全 rank への一般化。
  （これは新規性の証明ではない。）

## 本ファイルが確定させること

`hyper r` を Goodstein の超演算（`hyper 1 = +`, `hyper 2 = *`, `hyper 3 = ^`）とするとき、

* (HT) `hyper r (hyper r x y) z ≤ hyper r x (hyper r y z)` の**領域**は `x ≥ 1, y ≥ 2`。
* rank 3 では **等号の条件が完全に決まる**：`y*z = y^z` ⟺ `(y,z) = (2,2)`（`y,z ≥ 2` の下で）。
  ⇒ **rank 3 の評価は Tamari 被覆に沿って厳密単調ではない**。
-/

namespace HyperTamari

/-- **Goodstein の超演算**。`hyper 1 = (+)`, `hyper 2 = (*)`, `hyper 3 = (^)`,
`hyper 4 = tetration`。 -/
def hyper : Nat → Nat → Nat → Nat
  | 0,      _, b     => b + 1
  | 1,      a, 0     => a
  | 2,      _, 0     => 0
  | (_ + 3), _, 0    => 1
  | (n + 1), a, (b + 1) => hyper n a (hyper (n + 1) a b)

@[simp] theorem hyper_zero (a b : Nat) : hyper 0 a b = b + 1 := by simp [hyper]
@[simp] theorem hyper_one_zero (a : Nat) : hyper 1 a 0 = a := by simp [hyper]
@[simp] theorem hyper_two_zero (a : Nat) : hyper 2 a 0 = 0 := by simp [hyper]
@[simp] theorem hyper_succ_succ_zero (n a : Nat) : hyper (n + 3) a 0 = 1 := by simp [hyper]
@[simp] theorem hyper_succ (n a b : Nat) :
    hyper (n + 1) a (b + 1) = hyper n a (hyper (n + 1) a b) := by simp [hyper]

/-! ## 階数 1,2,3 が +, *, ^ と一致することを機械検証する（規約の固定） -/

theorem hyper_one (a b : Nat) : hyper 1 a b = a + b := by
  induction b with
  | zero => simp
  | succ b ih => rw [hyper_succ, ih, hyper_zero]; omega

theorem hyper_two (a b : Nat) : hyper 2 a b = a * b := by
  induction b with
  | zero => simp
  | succ b ih => rw [hyper_succ, ih, hyper_one]; ring

theorem hyper_three (a b : Nat) : hyper 3 a b = a ^ b := by
  induction b with
  | zero => simp
  | succ b ih => rw [hyper_succ, ih, hyper_two, pow_succ]; ring

/-! ## rank 3 の完全解

$(x^y)^z = x^{yz}$ なので、rank 3 の (HT) は**指数の比較 $yz \le y^z$ に還元する**。
等号の条件まで完全に決まる。 -/

/-- $y\ge2$、$z\ge1$ ならば $y \le y^z$。 -/
theorem self_le_pow_of_one_le {y : Nat} (hy : 2 ≤ y) {z : Nat} (hz : 1 ≤ z) : y ≤ y ^ z := by
  calc y = y ^ 1 := (pow_one y).symm
  _ ≤ y ^ z := Nat.pow_le_pow_right (by omega) hz

/-- $y\ge2$ ならば $yz \le y^z$。 -/
theorem mul_le_pow_of_two_le {y : Nat} (hy : 2 ≤ y) (z : Nat) : y * z ≤ y ^ z := by
  induction z with
  | zero => simp
  | succ z ih =>
      rcases Nat.eq_zero_or_pos z with rfl | hz
      · simp
      · have h1 : y ≤ y ^ z := self_le_pow_of_one_le hy hz
        have h2 : y ^ z * 2 ≤ y ^ z * y := Nat.mul_le_mul_left _ hy
        calc y * (z + 1) = y * z + y := by ring
        _ ≤ y ^ z + y ^ z := Nat.add_le_add ih h1
        _ ≤ y ^ z * y := by omega
        _ = y ^ (z + 1) := (pow_succ y z).symm

/-- $y\ge2$、$z\ge3$ ならば **厳密に** $yz < y^z$。 -/
theorem mul_lt_pow_of_three_le {y : Nat} (hy : 2 ≤ y) :
    ∀ z, 3 ≤ z → y * z < y ^ z := by
  intro z
  induction z with
  | zero => omega
  | succ z ih =>
      intro hz
      rcases Nat.lt_or_ge z 3 with h3 | h3
      · -- z + 1 = 3、すなわち z = 2
        have hz2 : z = 2 := by omega
        subst hz2
        have h4 : (4 : Nat) ≤ y ^ 2 := by
          calc (4 : Nat) = 2 ^ 2 := by norm_num
          _ ≤ y ^ 2 := Nat.pow_le_pow_left hy 2
        have hy0 : 0 < y := by omega
        calc y * 3 < y * 4 := by omega
        _ ≤ y * y ^ 2 := Nat.mul_le_mul_left _ h4
        _ = y ^ 3 := by ring
      · have hlt := ih h3
        have h1 : y ≤ y ^ z := self_le_pow_of_one_le hy (by omega)
        have h2 : y ^ z * 2 ≤ y ^ z * y := Nat.mul_le_mul_left _ hy
        calc y * (z + 1) = y * z + y := by ring
        _ < y ^ z + y ^ z := by omega
        _ ≤ y ^ z * y := by omega
        _ = y ^ (z + 1) := (pow_succ y z).symm

/-- $y\ge2$ のとき $yz = y^z$ となるのは **$z=1$ または $(y,z)=(2,2)$ に限る**。 -/
theorem mul_eq_pow_iff {y z : Nat} (hy : 2 ≤ y) :
    y * z = y ^ z ↔ z = 1 ∨ (y = 2 ∧ z = 2) := by
  constructor
  · intro h
    match z with
    | 0 => simp at h
    | 1 => exact Or.inl rfl
    | 2 =>
        refine Or.inr ⟨?_, rfl⟩
        have h' : y * 2 = y * y := by
          rw [h]; ring
        have hy0 : 0 < y := by omega
        exact (Nat.eq_of_mul_eq_mul_left hy0 h').symm
    | (n + 3) =>
        exfalso
        have := mul_lt_pow_of_three_le hy (n + 3) (by omega)
        omega
  · rintro (rfl | ⟨rfl, rfl⟩)
    · simp
    · norm_num

/-- **rank 3 の (HT)**（`hyper 3 = (^)`）。 -/
theorem ht_rank3 {x y : Nat} (hx : 1 ≤ x) (hy : 2 ≤ y) (z : Nat) :
    hyper 3 (hyper 3 x y) z ≤ hyper 3 x (hyper 3 y z) := by
  simp only [hyper_three]
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hx (mul_le_pow_of_two_le hy z)

/-! ### choice を使わない補助補題

Mathlib の `Nat.pow_lt_pow_right` と `Nat.pow_right_injective` は
`Classical.choice` に依存する。ここでは同じ主張を `Nat.pow_lt_pow_succ`
（公理ゼロ）からの帰納で構成的に組み直し、開発全体から choice を除く。 -/

/-- `Nat.pow_lt_pow_right` の choice を使わない版。 -/
theorem pow_lt_pow_right' {b : Nat} (hb : 1 < b) : ∀ {m n : Nat}, m < n → b ^ m < b ^ n := by
  intro m n h
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge m n with hmn | hmn
      · exact lt_trans (ih hmn) (Nat.pow_lt_pow_succ hb)
      · have : m = n := by omega
        subst this
        exact Nat.pow_lt_pow_succ hb

/-- `Nat.pow_right_injective` の choice を使わない版。 -/
theorem pow_right_injective' {b : Nat} (hb : 2 ≤ b) {m n : Nat} (h : b ^ m = b ^ n) : m = n := by
  rcases Nat.lt_trichotomy m n with hmn | hmn | hmn
  · exact absurd h (Nat.ne_of_lt (pow_lt_pow_right' (by omega) hmn))
  · exact hmn
  · exact absurd h.symm (Nat.ne_of_lt (pow_lt_pow_right' (by omega) hmn))

/-- **rank 3 の等号は完全に決まる**：$x\ge2,\;y\ge2$ のとき
$(x^y)^z = x^{y^z}$ ⟺ $z=1$ または $(y,z)=(2,2)$。 -/
theorem ht_rank3_eq_iff {x y z : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    hyper 3 (hyper 3 x y) z = hyper 3 x (hyper 3 y z) ↔ z = 1 ∨ (y = 2 ∧ z = 2) := by
  simp only [hyper_three]
  rw [← pow_mul]
  constructor
  · intro h
    exact (mul_eq_pow_iff hy).mp (pow_right_injective' hx h)
  · intro h
    rw [(mul_eq_pow_iff hy).mpr h]

/-- 具体的な等号の証人：$(x^2)^2 = x^{2^2}$。 -/
theorem ht_rank3_equality_witness (x : Nat) :
    hyper 3 (hyper 3 x 2) 2 = hyper 3 x (hyper 3 2 2) := by
  simp only [hyper_three]
  norm_num
  ring

/-! ## Tamari 側：二分木・右回転・評価

Tamari 順序は**右回転** $((AB)C)\to(A(BC))$ で生成される（[Tamari 1962]、
論理化は [Zeilberger 2019]）。ここでは根での右回転に限って、
rank 3 の評価が**単調だが厳密でない**ことを機械検証する。 -/

/-- 葉が 1 種類の二分木（括弧付け）。 -/
inductive BTree where
  | leaf : BTree
  | node : BTree → BTree → BTree
  deriving DecidableEq, Repr

namespace BTree

/-- 葉の個数。 -/
def leaves : BTree → Nat
  | leaf => 1
  | node l r => l.leaves + r.leaves

/-- 全葉に `a` を置き、内部節点で `hyper rk` を適用した評価。 -/
def eval (rk a : Nat) : BTree → Nat
  | leaf => a
  | node l r => hyper rk (eval rk a l) (eval rk a r)

@[simp] theorem eval_leaf (rk a : Nat) : eval rk a leaf = a := rfl
@[simp] theorem eval_node (rk a : Nat) (l r : BTree) :
    eval rk a (node l r) = hyper rk (eval rk a l) (eval rk a r) := rfl

/-- 根での右回転 $((AB)C)\to(A(BC))$。Tamari 被覆の生成元。 -/
def rotR : BTree → Option BTree
  | node (node a b) c => some (node a (node b c))
  | _ => none

end BTree

/-- $a\ge2$ なら、rank 3 の評価はどの木でも $\ge 2$。 -/
theorem two_le_eval_rank3 {a : Nat} (ha : 2 ≤ a) : ∀ T : BTree, 2 ≤ BTree.eval 3 a T := by
  intro T
  induction T with
  | leaf => simpa using ha
  | node l r ihl ihr =>
      simp only [BTree.eval_node, hyper_three]
      calc (2 : Nat) = 2 ^ 1 := by norm_num
      _ ≤ BTree.eval 3 a l ^ 1 := Nat.pow_le_pow_left ihl 1
      _ ≤ BTree.eval 3 a l ^ BTree.eval 3 a r :=
            Nat.pow_le_pow_right (by omega) (by omega)

/-- **根の右回転は rank 3 の評価を減少させない**（Tamari 被覆に沿う単調性）。 -/
theorem rotR_mono_rank3 {a : Nat} (ha : 2 ≤ a) {T U : BTree}
    (h : BTree.rotR T = some U) : BTree.eval 3 a T ≤ BTree.eval 3 a U := by
  match T, h with
  | BTree.node (BTree.node p q) c, h =>
      simp only [BTree.rotR, Option.some.injEq] at h
      subst h
      simp only [BTree.eval_node]
      exact ht_rank3 (by have := two_le_eval_rank3 ha p; omega)
                     (two_le_eval_rank3 ha q) _

/-- **rank 3 では厳密単調性が破れる**：Tamari 被覆
$((aa)a)a \lessdot (aa)(aa)$ の両端で **値が一致する**（$a=2$ で共に $256$）。 -/
theorem rank3_rotation_not_strict :
    BTree.rotR (BTree.node (BTree.node (BTree.node BTree.leaf BTree.leaf) BTree.leaf) BTree.leaf)
      = some (BTree.node (BTree.node BTree.leaf BTree.leaf) (BTree.node BTree.leaf BTree.leaf))
    ∧ BTree.eval 3 2 (BTree.node (BTree.node (BTree.node BTree.leaf BTree.leaf) BTree.leaf) BTree.leaf)
      = BTree.eval 3 2 (BTree.node (BTree.node BTree.leaf BTree.leaf) (BTree.node BTree.leaf BTree.leaf))
    ∧ (BTree.node (BTree.node (BTree.node BTree.leaf BTree.leaf) BTree.leaf) BTree.leaf)
      ≠ (BTree.node (BTree.node BTree.leaf BTree.leaf) (BTree.node BTree.leaf BTree.leaf)) := by
  refine ⟨rfl, ?_, by simp⟩
  simp only [BTree.eval_node, BTree.eval_leaf, hyper_three]
  norm_num

/-- 参考：その共通の値は $256$。 -/
theorem rank3_collision_value :
    BTree.eval 3 2 (BTree.node (BTree.node (BTree.node BTree.leaf BTree.leaf) BTree.leaf) BTree.leaf) = 256 := by
  simp only [BTree.eval_node, BTree.eval_leaf, hyper_three]
  norm_num

/-- 四葉の五つの括弧付けの値（rank 3、$a=2$）：
$((aa)a)a=(a(aa))a=(aa)(aa)=256$、$a((aa)a)=a(a(aa))=65536$（論文 Example 3.3）。 -/
theorem rank3_five_values :
    BTree.eval 3 2 (BTree.node (BTree.node (BTree.node BTree.leaf BTree.leaf) BTree.leaf) BTree.leaf) = 256
    ∧ BTree.eval 3 2 (BTree.node (BTree.node BTree.leaf (BTree.node BTree.leaf BTree.leaf)) BTree.leaf) = 256
    ∧ BTree.eval 3 2 (BTree.node (BTree.node BTree.leaf BTree.leaf) (BTree.node BTree.leaf BTree.leaf)) = 256
    ∧ BTree.eval 3 2 (BTree.node BTree.leaf (BTree.node (BTree.node BTree.leaf BTree.leaf) BTree.leaf)) = 65536
    ∧ BTree.eval 3 2 (BTree.node BTree.leaf (BTree.node BTree.leaf (BTree.node BTree.leaf BTree.leaf))) = 65536 := by
  simp only [BTree.eval_node, BTree.eval_leaf, hyper_three]
  norm_num

/-! ## 領域が鋭いこと（$y\ge2$ は落とせない） -/

/-- **$y=1$ は (HT) を壊す**：$(x^1)^z = x^z$ だが $x^{1^z} = x$。 -/
theorem ht_needs_two_le_y :
    hyper 3 (hyper 3 3 1) 3 = 27 ∧ hyper 3 3 (hyper 3 1 3) = 3 := by
  simp only [hyper_three]; norm_num

/-- rank 4（テトレーション）の値の確認：$2\uparrow\uparrow4 = 65536$。 -/
theorem tetration_two_four : hyper 4 2 4 = 65536 := by
  have h0 : hyper 4 2 0 = 1 := by simp
  have h1 : hyper 4 2 1 = 2 := by rw [hyper_succ, h0, hyper_three]; norm_num
  have h2 : hyper 4 2 2 = 4 := by rw [hyper_succ, h1, hyper_three]; norm_num
  have h3 : hyper 4 2 3 = 16 := by rw [hyper_succ, h2, hyper_three]; norm_num
  rw [hyper_succ, h3, hyper_three]; norm_num

/-- rank 4 の最小事例で (HT) が**厳密**であること：
$(2\uparrow\uparrow2)\uparrow\uparrow2 = 256 < 65536 = 2\uparrow\uparrow(2\uparrow\uparrow2)$。 -/
theorem ht_rank4_strict_smallest :
    hyper 4 (hyper 4 2 2) 2 < hyper 4 2 (hyper 4 2 2) := by
  have h2 : hyper 4 2 2 = 4 := by
    have h0 : hyper 4 2 0 = 1 := hyper_succ_succ_zero 1 2
    have h1 : hyper 4 2 1 = 2 := by rw [hyper_succ, h0, hyper_three]; norm_num
    rw [hyper_succ, h1, hyper_three]; norm_num
  have hL : hyper 4 4 2 = 256 := by
    have h0 : hyper 4 4 0 = 1 := hyper_succ_succ_zero 1 4
    have h1 : hyper 4 4 1 = 4 := by rw [hyper_succ, h0, hyper_three]; norm_num
    rw [hyper_succ, h1, hyper_three]; norm_num
  rw [h2, hL, tetration_two_four]
  omega

/-! ## 一般階数について

本ファイルは rank 3 と rank 4 の最小事例までを扱う。一般階数 $r\ge3$ の (HT)、
(SUM$_r$)、階数についての単調性、$r\ge4$ での厳密性（等号の完全分類）は
`HyperTamari/General.lean` で証明する（`ht_general`, `sum_lemma`, `hyper_rank_mono`,
`ht_strict_general`, `equality_classification`）。rank 3 との差は `mul_eq_pow_iff` が示す
等号 $(y,z)=(2,2)$ の存在に対応する。 -/

end HyperTamari



#print axioms HyperTamari.pow_lt_pow_right'
#print axioms HyperTamari.pow_right_injective'
#print axioms HyperTamari.mul_le_pow_of_two_le
#print axioms HyperTamari.mul_eq_pow_iff
#print axioms HyperTamari.ht_rank3
#print axioms HyperTamari.ht_rank3_eq_iff
#print axioms HyperTamari.ht_rank3_equality_witness
#print axioms HyperTamari.two_le_eval_rank3
#print axioms HyperTamari.rotR_mono_rank3
#print axioms HyperTamari.rank3_rotation_not_strict
#print axioms HyperTamari.rank3_collision_value
#print axioms HyperTamari.rank3_five_values
#print axioms HyperTamari.BTree.eval_leaf
#print axioms HyperTamari.BTree.eval_node
#print axioms HyperTamari.self_le_pow_of_one_le
#print axioms HyperTamari.mul_lt_pow_of_three_le
#print axioms HyperTamari.ht_needs_two_le_y
#print axioms HyperTamari.tetration_two_four
#print axioms HyperTamari.ht_rank4_strict_smallest
#print axioms HyperTamari.hyper_zero
#print axioms HyperTamari.hyper_one_zero
#print axioms HyperTamari.hyper_two_zero
#print axioms HyperTamari.hyper_succ_succ_zero
#print axioms HyperTamari.hyper_succ
#print axioms HyperTamari.hyper_one
#print axioms HyperTamari.hyper_two
#print axioms HyperTamari.hyper_three
