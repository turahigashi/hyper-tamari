import HyperTamari.Basic

/-
# rank 4（テトレーション）の Hyperoperation–Tamari 不等式

本ファイルの目標＝**folklore の rank 3 を超えた最初の場合**を完全に証明する。

> **定理** $x\ge2,\;y\ge2$ のとき $(x\uparrow\uparrow y)\uparrow\uparrow z \;\le\; x\uparrow\uparrow(y\uparrow\uparrow z)$。
> さらに $z\ge2$ なら**厳密**。

これが rank 3 との**二分法**を確定させる：
rank 3 では $(y,z)=(2,2)$ で**等号**が起きる（`ht_rank3_eq_iff`）が、
rank 4 では $z\ge2$ で**常に厳密**。理由は
**潰す法則 $(x^y)^z=x^{yz}$ が 4 階以上に存在しない**こと。

## 証明の骨格（$z$ の帰納）

`tet A (z+1) = A ^ tet A z` から始め、帰納法の仮定で `tet A z ≤ tet x m`（`m := tet y z`）へ移し、
`A = x ^ tet x y'` を使って底を `x` に揃えると、指数の比較

  `tet x y' * tet x m ≤ tet x (y^m - 1)`

に落ちる。左辺は `tet x y' ≤ tet x m` で `(tet x m)^2` に抑えられ、
**二乗補題** `(tet x m)^2 ≤ tet x (m+1)` と
**指数の下界** `m + 2 ≤ y^m` で右辺に収まる。
-/

namespace HyperTamari

/-- テトレーション（構造的再帰版）。`hyper 4` と一致することを下で証明する。 -/
def tet (x : Nat) : Nat → Nat
  | 0 => 1
  | (n + 1) => x ^ tet x n

@[simp] theorem tet_zero (x : Nat) : tet x 0 = 1 := rfl
@[simp] theorem tet_succ (x n : Nat) : tet x (n + 1) = x ^ tet x n := rfl

/-- `tet` は `hyper 4` と一致する（規約の接続）。 -/
theorem tet_eq_hyper4 (x n : Nat) : tet x n = hyper 4 x n := by
  induction n with
  | zero => simp
  | succ n ih => rw [tet_succ, ih, hyper_succ, hyper_three]

/-! ## 基本補題 -/

/-- $x\ge2,\;n\ge1$ なら $x \le x\uparrow\uparrow n$。 -/
theorem base_le_tet {x : Nat} (hx : 2 ≤ x) : ∀ {n : Nat}, 1 ≤ n → x ≤ tet x n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · simp
      · have h := ih hn'
        rw [tet_succ]
        calc x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ tet x n := Nat.pow_le_pow_right (by omega) (by omega)

/-- $x\ge2$ なら $x\uparrow\uparrow n \ge 1$。 -/
theorem one_le_tet {x : Nat} (hx : 2 ≤ x) (n : Nat) : 1 ≤ tet x n := by
  induction n with
  | zero => simp
  | succ n ih => rw [tet_succ]; exact Nat.one_le_pow _ _ (by omega)

/-- `tet x ·` は狭義単調（$x\ge2$）。 -/
theorem tet_lt_succ {x : Nat} (hx : 2 ≤ x) (n : Nat) : tet x n < tet x (n + 1) := by
  induction n with
  | zero => simp; omega
  | succ n ih =>
      rw [tet_succ, tet_succ]
      exact pow_lt_pow_right' (by omega) ih

theorem tet_strictMono {x : Nat} (hx : 2 ≤ x) {m n : Nat} (h : m < n) :
    tet x m < tet x n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge m n with hmn | hmn
      · exact lt_trans (ih hmn) (tet_lt_succ hx n)
      · have : m = n := by omega
        subst this
        exact tet_lt_succ hx m

theorem tet_mono {x : Nat} (hx : 2 ≤ x) {m n : Nat} (h : m ≤ n) :
    tet x m ≤ tet x n := by
  rcases Nat.eq_or_lt_of_le h with rfl | h'
  · exact le_refl _
  · exact (tet_strictMono hx h').le

/-! ## 鍵となる二つの補題 -/

/-- $2t \le 2^t$（$t\ge1$）。 -/
theorem two_mul_le_two_pow : ∀ {t : Nat}, 1 ≤ t → 2 * t ≤ 2 ^ t := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
      rcases Nat.eq_zero_or_pos t with rfl | ht'
      · decide
      · have h := ih ht'
        have h1 : (2 : Nat) ≤ 2 ^ t := by
          calc (2 : Nat) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht'
        calc 2 * (t + 1) = 2 * t + 2 := by ring
        _ ≤ 2 ^ t + 2 ^ t := by omega
        _ = 2 ^ (t + 1) := by ring

/-- **二乗補題**：$x\ge2,\;m\ge1$ のとき $(x\uparrow\uparrow m)^2 \le x\uparrow\uparrow(m+1)$。 -/
theorem sq_tet_le {x : Nat} (hx : 2 ≤ x) : ∀ {m : Nat}, 1 ≤ m →
    (tet x m) ^ 2 ≤ tet x (m + 1) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm'
      · -- m + 1 = 1
        simp only [tet_succ, tet_zero, pow_one]
        exact Nat.pow_le_pow_right (by omega) hx
      · -- 一般段：`(x^t)^2 = x^(2t) ≤ x^(x^t)`
        have ht1 : 1 ≤ tet x m := one_le_tet hx m
        have key : 2 * tet x m ≤ x ^ tet x m := by
          calc 2 * tet x m ≤ 2 ^ tet x m := two_mul_le_two_pow ht1
          _ ≤ x ^ tet x m := Nat.pow_le_pow_left hx _
        calc (tet x (m + 1)) ^ 2 = (x ^ tet x m) ^ 2 := by rw [tet_succ]
        _ = x ^ (tet x m * 2) := by rw [← pow_mul]
        _ = x ^ (2 * tet x m) := by rw [Nat.mul_comm]
        _ ≤ x ^ (x ^ tet x m) := Nat.pow_le_pow_right (by omega) key
        _ = tet x (m + 2) := by rw [tet_succ, tet_succ]

/-- 直接の不等式 $t^2 \le x^t$ は一般には**偽**：$(x,t)=(2,3)$ で $9 > 8$。
だから二乗補題 `sq_tet_le` は帰納的な形で述べる必要がある（論文 Remark 4.2）。 -/
theorem sq_le_pow_fails : ¬ (∀ x t : Nat, 2 ≤ x → 1 ≤ t → t ^ 2 ≤ x ^ t) := by
  intro h
  have h23 : 3 ^ 2 ≤ 2 ^ 3 := h 2 3 (by decide) (by decide)
  exact absurd h23 (by decide)

/-- 反例の証人そのもの：$2^3 < 3^2$。 -/
theorem two_pow_three_lt_three_sq : 2 ^ 3 < 3 ^ 2 := by decide

/-- **指数の下界**：$y\ge2,\;m\ge2$ のとき $m + 2 \le y^m$。 -/
theorem add_two_le_pow {y : Nat} (hy : 2 ≤ y) : ∀ {m : Nat}, 2 ≤ m → m + 2 ≤ y ^ m := by
  intro m hm
  have h2 : ∀ k : Nat, 2 ≤ k → k + 2 ≤ 2 ^ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · have : k = 1 := by omega
          subst this; decide
        · have h := ih hk2
          have h1 : (1 : Nat) ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
          calc k + 1 + 2 = (k + 2) + 1 := by ring
          _ ≤ 2 ^ k + 2 ^ k := by omega
          _ = 2 ^ (k + 1) := by ring
  calc m + 2 ≤ 2 ^ m := h2 m hm
  _ ≤ y ^ m := Nat.pow_le_pow_left hy m

/-! ## 主定理（rank 4） -/

/-- **Hyperoperation–Tamari 不等式・rank 4**
$$(x\uparrow\uparrow y)\uparrow\uparrow z \;\le\; x\uparrow\uparrow(y\uparrow\uparrow z)
\qquad (x\ge2,\;y\ge2).$$

rank 3 と違い**潰す法則 $(x^y)^z=x^{yz}$ がない**ので、証明は
$z$ の帰納＋**二乗補題**＋**指数の下界**で進む。
$z=1$ を独立の基底に置く必要がある（$z=0\to1$ では帰納法の仮定が緩みすぎる）。 -/
theorem tet_ht {x y : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    ∀ z, tet (tet x y) z ≤ tet x (tet y z) := by
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  have hy' : 1 ≤ y' := by omega
  intro z
  induction z with
  | zero =>
      simp only [tet_zero, tet_succ, pow_one]
      omega
  | succ z ih =>
      rcases Nat.eq_zero_or_pos z with rfl | hz
      · -- z = 0：両辺とも `tet x (y'+1)`（等号）
        simp only [tet_zero, tet_succ, pow_one]
        exact le_refl _
      · -- z ≥ 1
        have hm2 : 2 ≤ tet (y' + 1) z := le_trans hy (base_le_tet hy hz)
        have hA1 : 1 ≤ tet x (y' + 1) := one_le_tet hx _
        have hy'm : y' ≤ tet (y' + 1) z := by
          have := base_le_tet hy hz
          omega
        have hpow : tet (y' + 1) z + 2 ≤ (y' + 1) ^ (tet (y' + 1) z) :=
          add_two_le_pow hy hm2
        obtain ⟨k, hk⟩ : ∃ k, (y' + 1) ^ (tet (y' + 1) z) = k + 1 :=
          ⟨(y' + 1) ^ (tet (y' + 1) z) - 1, by omega⟩
        have hmk : tet (y' + 1) z + 1 ≤ k := by omega
        calc tet (tet x (y' + 1)) (z + 1)
            = (tet x (y' + 1)) ^ (tet (tet x (y' + 1)) z) := tet_succ _ _
          _ ≤ (tet x (y' + 1)) ^ (tet x (tet (y' + 1) z)) :=
              Nat.pow_le_pow_right hA1 ih
          _ = (x ^ tet x y') ^ (tet x (tet (y' + 1) z)) := by rw [tet_succ]
          _ = x ^ (tet x y' * tet x (tet (y' + 1) z)) := by rw [← pow_mul]
          _ ≤ x ^ (tet x (tet (y' + 1) z) * tet x (tet (y' + 1) z)) :=
              Nat.pow_le_pow_right (by omega)
                (Nat.mul_le_mul (tet_mono hx hy'm) (le_refl _))
          _ = x ^ ((tet x (tet (y' + 1) z)) ^ 2) := by rw [pow_two]
          _ ≤ x ^ (tet x (tet (y' + 1) z + 1)) :=
              Nat.pow_le_pow_right (by omega) (sq_tet_le hx (by omega))
          _ ≤ x ^ (tet x k) :=
              Nat.pow_le_pow_right (by omega) (tet_mono hx hmk)
          _ = tet x (k + 1) := (tet_succ x k).symm
          _ = tet x ((y' + 1) ^ (tet (y' + 1) z)) := by rw [hk]
          _ = tet x (tet (y' + 1) (z + 1)) := by rw [tet_succ]

/-! ## 厳密性（rank 3 との二分法の芯） -/

/-- $y\ge2,\;m\ge3$ のとき $m+3 \le y^m$。 -/
theorem add_three_le_pow {y : Nat} (hy : 2 ≤ y) : ∀ {m : Nat}, 3 ≤ m → m + 3 ≤ y ^ m := by
  intro m hm
  have h2 : ∀ k : Nat, 3 ≤ k → k + 3 ≤ 2 ^ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
        rcases Nat.lt_or_ge k 3 with hk3 | hk3
        · have : k = 2 := by omega
          subst this; decide
        · have h := ih hk3
          have h1 : (1 : Nat) ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
          calc k + 1 + 3 = (k + 3) + 1 := by ring
          _ ≤ 2 ^ k + 2 ^ k := by omega
          _ = 2 ^ (k + 1) := by ring
  calc m + 3 ≤ 2 ^ m := h2 m hm
  _ ≤ y ^ m := Nat.pow_le_pow_left hy m

/-- $y\ge2,\;w\ge2$ のとき $3 \le y\uparrow\uparrow w$（実は $\ge4$）。 -/
theorem three_le_tet {y : Nat} (hy : 2 ≤ y) {w : Nat} (hw : 2 ≤ w) : 3 ≤ tet y w := by
  have h2 : 4 ≤ tet y 2 := by
    simp only [tet_succ, tet_zero, pow_one]
    calc (4 : Nat) = 2 ^ 2 := by norm_num
    _ ≤ y ^ 2 := Nat.pow_le_pow_left hy 2
    _ ≤ y ^ y := Nat.pow_le_pow_right (by omega) hy
  have := tet_mono hy hw
  omega

/-- **rank 4 では (HT) は厳密**（$y\uparrow\uparrow w \ge 3$ のとき）。
rank 3 では $(y,z)=(2,2)$ で等号が起きた（`ht_rank3_eq_iff`）が、
rank 4 には**潰す法則がない**のでここが厳密になる。 -/
theorem tet_ht_strict {x y : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) {w : Nat}
    (hm3 : 3 ≤ tet y w) :
    tet (tet x y) (w + 1) < tet x (tet y (w + 1)) := by
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  have hz : 1 ≤ w := by
    rcases Nat.eq_zero_or_pos w with rfl | h
    · rw [tet_zero] at hm3; omega
    · exact h
  have hm2 : 2 ≤ tet (y' + 1) w := by omega
  have hA1 : 1 ≤ tet x (y' + 1) := one_le_tet hx _
  have hy'm : y' ≤ tet (y' + 1) w := by
    have := base_le_tet hy hz; omega
  have hpow : tet (y' + 1) w + 3 ≤ (y' + 1) ^ (tet (y' + 1) w) := add_three_le_pow hy hm3
  obtain ⟨k, hk⟩ : ∃ k, (y' + 1) ^ (tet (y' + 1) w) = k + 1 :=
    ⟨(y' + 1) ^ (tet (y' + 1) w) - 1, by omega⟩
  have hmk : tet (y' + 1) w + 1 < k := by omega
  calc tet (tet x (y' + 1)) (w + 1)
      = (tet x (y' + 1)) ^ (tet (tet x (y' + 1)) w) := tet_succ _ _
    _ ≤ (tet x (y' + 1)) ^ (tet x (tet (y' + 1) w)) :=
        Nat.pow_le_pow_right hA1 (tet_ht hx hy w)
    _ = (x ^ tet x y') ^ (tet x (tet (y' + 1) w)) := by rw [tet_succ]
    _ = x ^ (tet x y' * tet x (tet (y' + 1) w)) := by rw [← pow_mul]
    _ ≤ x ^ (tet x (tet (y' + 1) w) * tet x (tet (y' + 1) w)) :=
        Nat.pow_le_pow_right (by omega)
          (Nat.mul_le_mul (tet_mono hx hy'm) (le_refl _))
    _ = x ^ ((tet x (tet (y' + 1) w)) ^ 2) := by rw [pow_two]
    _ ≤ x ^ (tet x (tet (y' + 1) w + 1)) :=
        Nat.pow_le_pow_right (by omega) (sq_tet_le hx (by omega))
    _ < x ^ (tet x k) :=
        pow_lt_pow_right' (by omega) (tet_strictMono hx hmk)
    _ = tet x (k + 1) := (tet_succ x k).symm
    _ = tet x ((y' + 1) ^ (tet (y' + 1) w)) := by rw [hk]
    _ = tet x (tet (y' + 1) (w + 1)) := by rw [tet_succ]

/-- **系**：$z\ge3$ なら rank 4 の (HT) は厳密。 -/
theorem tet_ht_strict_of_three_le {x y z : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 3 ≤ z) :
    tet (tet x y) z < tet x (tet y z) := by
  obtain ⟨w, rfl⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
  exact tet_ht_strict hx hy (three_le_tet hy (by omega))

/-- **残った場合の証人**：$z=2,\;y=2,\;x=2$ でも厳密（$256 < 65536$）。 -/
theorem tet_ht_strict_witness_2_2_2 : tet (tet 2 2) 2 < tet 2 (tet 2 2) := by
  decide

/-! ## 二分法を `hyper` の言葉で述べる -/

/-- rank 4 の (HT) を `hyper` で。 -/
theorem ht_rank4 {x y : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) (z : Nat) :
    hyper 4 (hyper 4 x y) z ≤ hyper 4 x (hyper 4 y z) := by
  rw [← tet_eq_hyper4, ← tet_eq_hyper4, ← tet_eq_hyper4, ← tet_eq_hyper4]
  exact tet_ht hx hy z

/-- rank 4 の厳密性を `hyper` で（$z\ge3$）。 -/
theorem ht_rank4_strict {x y z : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 3 ≤ z) :
    hyper 4 (hyper 4 x y) z < hyper 4 x (hyper 4 y z) := by
  rw [← tet_eq_hyper4, ← tet_eq_hyper4, ← tet_eq_hyper4, ← tet_eq_hyper4]
  exact tet_ht_strict_of_three_le hx hy hz

/-- **二分法**：
* **rank 3** — $(x^2)^2 = x^{2^2}$ が**すべての $x$** で成り立つ（等号が実際に起きる）
* **rank 4** — $x,y\ge2,\;z\ge3$ では**常に厳密**

⇒ 評価が Tamari 被覆に沿って**厳密単調か否か**が、rank 3 と rank 4 で分かれる。
理由は**潰す法則 $(x^y)^z = x^{yz}$ が 4 階以上に存在しない**こと
（rank 3 の等号条件 `ht_rank3_eq_iff` はまさにこの法則から出ていた）。 -/
theorem rank3_vs_rank4_dichotomy :
    (∀ x : Nat, hyper 3 (hyper 3 x 2) 2 = hyper 3 x (hyper 3 2 2))
    ∧ (∀ x y z : Nat, 2 ≤ x → 2 ≤ y → 3 ≤ z →
         hyper 4 (hyper 4 x y) z < hyper 4 x (hyper 4 y z)) :=
  ⟨ht_rank3_equality_witness, fun _ _ _ hx hy hz => ht_rank4_strict hx hy hz⟩

end HyperTamari



#print axioms HyperTamari.tet_ht
#print axioms HyperTamari.add_three_le_pow
#print axioms HyperTamari.three_le_tet
#print axioms HyperTamari.tet_ht_strict
#print axioms HyperTamari.tet_ht_strict_of_three_le
#print axioms HyperTamari.tet_ht_strict_witness_2_2_2
#print axioms HyperTamari.ht_rank4
#print axioms HyperTamari.ht_rank4_strict
#print axioms HyperTamari.rank3_vs_rank4_dichotomy
#print axioms HyperTamari.tet_zero
#print axioms HyperTamari.tet_succ
#print axioms HyperTamari.tet_eq_hyper4
#print axioms HyperTamari.base_le_tet
#print axioms HyperTamari.one_le_tet
#print axioms HyperTamari.tet_lt_succ
#print axioms HyperTamari.tet_strictMono
#print axioms HyperTamari.tet_mono
#print axioms HyperTamari.two_mul_le_two_pow
#print axioms HyperTamari.sq_tet_le
#print axioms HyperTamari.add_two_le_pow
#print axioms HyperTamari.sq_le_pow_fails
#print axioms HyperTamari.two_pow_three_lt_three_sq

namespace HyperTamari

/-! ## Tamari 被覆（任意の節点での右回転）に沿う単調性

根での回転だけでは「left comb が最小・right comb が最大」は出ない。
Tamari 被覆は**任意の節点**での右回転なので、文脈についての帰納が要る。 -/

/-- Tamari の被覆関係：任意の節点での一回の右回転。 -/
inductive Rot : BTree → BTree → Prop where
  | root (a b c : BTree) : Rot (BTree.node (BTree.node a b) c) (BTree.node a (BTree.node b c))
  | left {l l' : BTree} (r : BTree) : Rot l l' → Rot (BTree.node l r) (BTree.node l' r)
  | right (l : BTree) {r r' : BTree} : Rot r r' → Rot (BTree.node l r) (BTree.node l r')

/-- $a\ge2$ なら rank 4 の評価もどの木でも $\ge 2$。 -/
theorem two_le_eval_rank4 {a : Nat} (ha : 2 ≤ a) : ∀ T : BTree, 2 ≤ BTree.eval 4 a T := by
  intro T
  induction T with
  | leaf => simpa using ha
  | node l r ihl ihr =>
      have hl := ihl
      have hr := ihr
      rw [BTree.eval_node, ← tet_eq_hyper4]
      calc (2 : Nat) ≤ BTree.eval 4 a l := hl
      _ ≤ tet (BTree.eval 4 a l) (BTree.eval 4 a r) :=
            base_le_tet hl (by omega)

/-- テトレーションは底についても単調。 -/
theorem tet_mono_base {x x' : Nat} (hx : 1 ≤ x) (h : x ≤ x') (n : Nat) :
    tet x n ≤ tet x' n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [tet_succ, tet_succ]
      calc x ^ tet x n ≤ x' ^ tet x n := Nat.pow_le_pow_left h _
      _ ≤ x' ^ tet x' n := Nat.pow_le_pow_right (by omega) ih

/-- **rank 3：Tamari 被覆に沿って評価は減少しない**（任意の節点での回転）。 -/
theorem Rot.eval_le_rank3 {a : Nat} (ha : 2 ≤ a) {T U : BTree} (h : Rot T U) :
    BTree.eval 3 a T ≤ BTree.eval 3 a U := by
  induction h with
  | root p q c =>
      simp only [BTree.eval_node]
      exact ht_rank3 (by have := two_le_eval_rank3 ha p; omega) (two_le_eval_rank3 ha q) _
  | left r _ ih =>
      simp only [BTree.eval_node, hyper_three]
      exact Nat.pow_le_pow_left ih _
  | right l _ ih =>
      simp only [BTree.eval_node, hyper_three]
      exact Nat.pow_le_pow_right (by have := two_le_eval_rank3 ha l; omega) ih

/-- **rank 4：Tamari 被覆に沿って評価は減少しない**。 -/
theorem Rot.eval_le_rank4 {a : Nat} (ha : 2 ≤ a) {T U : BTree} (h : Rot T U) :
    BTree.eval 4 a T ≤ BTree.eval 4 a U := by
  induction h with
  | root p q c =>
      simp only [BTree.eval_node]
      exact ht_rank4 (two_le_eval_rank4 ha p) (two_le_eval_rank4 ha q) _
  | @left l l' r _ ih =>
      simp only [BTree.eval_node, ← tet_eq_hyper4]
      have := two_le_eval_rank4 ha l
      exact tet_mono_base (by omega) ih _
  | right l _ ih =>
      simp only [BTree.eval_node, ← tet_eq_hyper4]
      exact tet_mono (by have := two_le_eval_rank4 ha l; omega) ih

/-- rank 4 では被覆に沿って**厳密**とは限らない（根の回転で $z<3$ の場合が残る）
ことを明示するため、根の回転が厳密になる十分条件を切り出しておく。 -/
theorem Rot.root_lt_rank4 {a : Nat} (ha : 2 ≤ a) (p q c : BTree)
    (hc : 3 ≤ BTree.eval 4 a c) :
    BTree.eval 4 a (BTree.node (BTree.node p q) c)
      < BTree.eval 4 a (BTree.node p (BTree.node q c)) := by
  simp only [BTree.eval_node]
  exact ht_rank4_strict (two_le_eval_rank4 ha p) (two_le_eval_rank4 ha q) hc

end HyperTamari

#print axioms HyperTamari.two_le_eval_rank4
#print axioms HyperTamari.tet_mono_base
#print axioms HyperTamari.Rot.eval_le_rank3
#print axioms HyperTamari.Rot.eval_le_rank4
#print axioms HyperTamari.Rot.root_lt_rank4

namespace HyperTamari

/-- $r\ge2$ なら $H_r(x,1)=x$。 -/
theorem hyper_one_arg {r : Nat} (hr : 2 ≤ r) (x : Nat) : hyper r x 1 = x := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  induction s with
  | zero => simp [hyper_two]
  | succ s ih =>
      have : hyper (s + 3) x 0 = 1 := by simp
      calc hyper (s + 1 + 2) x 1 = hyper (s + 2) x (hyper (s + 3) x 0) := by
            rw [show s + 1 + 2 = s + 2 + 1 from by ring, hyper_succ]
      _ = hyper (s + 2) x 1 := by rw [this]
      _ = x := ih (by omega)


/-! ## right comb の閉形式 -/

/-- $n+1$ 葉の right comb。 -/
def rightComb : Nat → BTree
  | 0 => BTree.leaf
  | (n + 1) => BTree.node BTree.leaf (rightComb n)

/-- **right comb の値は一つ上の階数**：
$\mathrm{ev}_{r,a}(\text{right comb with } n{+}1 \text{ leaves}) = H_{r+1}(a,n{+}1)$。 -/
theorem eval_rightComb {r : Nat} (hr : 1 ≤ r) (a : Nat) :
    ∀ n : Nat, BTree.eval r a (rightComb n) = hyper (r + 1) a (n + 1) := by
  intro n
  induction n with
  | zero =>
      simp only [rightComb, BTree.eval_leaf]
      exact (hyper_one_arg (by omega) a).symm
  | succ n ih =>
      simp only [rightComb, BTree.eval_node, ih]
      exact (hyper_succ r a (n + 1)).symm

end HyperTamari

#print axioms HyperTamari.eval_rightComb
#print axioms HyperTamari.hyper_one_arg

namespace HyperTamari

/-! ## 定理 1.2 の厳密性に残るケース：$y=z=2$

一般論から残るのは $y=z=2$ かつ $x\ge2$ の**全体**であり、
$x=y=z=2$ の数値例だけでは足りない。実際に計算すると
\[
(x\uparrow\uparrow2)\uparrow\uparrow2=(x^x)^{x^x}=x^{\,x^{x+1}},\qquad
x\uparrow\uparrow(2\uparrow\uparrow2)=x\uparrow\uparrow4=x^{\,x^{x^x}}
\]
であり、$x\ge2$ では $x+1\lt x^x$ なので厳密。 -/

/-- $x\ge2$ なら $x+1 \lt x^x$。 -/
theorem succ_lt_pow_self {x : Nat} (hx : 2 ≤ x) : x + 1 < x ^ x := by
  have h2 : x ^ 2 ≤ x ^ x := Nat.pow_le_pow_right (by omega) hx
  have h3 : x * 2 ≤ x * x := Nat.mul_le_mul_left _ hx
  have h4 : x ^ 2 = x * x := by ring
  omega

/-- **$y=z=2$ での厳密性**（すべての $x\ge2$）。 -/
theorem tet_ht_strict_two_two {x : Nat} (hx : 2 ≤ x) :
    tet (tet x 2) 2 < tet x (tet 2 2) := by
  have e2 : tet x 2 = x ^ x := by simp
  have e22 : tet 2 2 = 4 := by norm_num [tet]
  have hxx : 2 ≤ x ^ x := by
    calc (2 : Nat) = 2 ^ 1 := by norm_num
    _ ≤ x ^ 1 := Nat.pow_le_pow_left hx 1
    _ ≤ x ^ x := Nat.pow_le_pow_right (by omega) (by omega)
  -- 左辺 = (x^x)^(x^x) = x^(x * x^x)
  have hL : tet (tet x 2) 2 = x ^ (x * x ^ x) := by
    rw [e2]
    simp only [tet_succ, tet_zero, pow_one]
    rw [← pow_mul]
  -- 右辺 = x↑↑4 = x^(x^(x^x))
  have hR : tet x (tet 2 2) = x ^ (x ^ (x ^ x)) := by
    rw [e22]
    simp only [tet_succ, tet_zero, pow_one]
  rw [hL, hR]
  refine pow_lt_pow_right' (by omega) ?_
  -- x * x^x = x^(x+1) < x^(x^x)
  calc x * x ^ x = x ^ (x + 1) := by rw [pow_succ]; ring
  _ < x ^ (x ^ x) := pow_lt_pow_right' (by omega) (succ_lt_pow_self hx)

/-- **定理 B の厳密性を $z\ge2$ に強化**。 -/
theorem tet_ht_strict_of_two_le {x y z : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) :
    tet (tet x y) z < tet x (tet y z) := by
  rcases Nat.eq_or_lt_of_le hz with hz2 | hz3
  · -- z = 2
    subst hz2
    rcases Nat.eq_or_lt_of_le hy with hy2 | hy3
    · -- y = 2
      subst hy2
      exact tet_ht_strict_two_two hx
    · -- y ≥ 3：一般論が使える（tet y 1 = y ≥ 3）
      have h1 : tet y 1 = y := by simp
      have : (3 : Nat) ≤ tet y 1 := by rw [h1]; omega
      exact tet_ht_strict hx hy this
  · exact tet_ht_strict_of_three_le hx hy (by omega)

/-- `hyper` の言葉で：$z\ge2$ なら rank 4 は厳密。 -/
theorem ht_rank4_strict_two {x y z : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) :
    hyper 4 (hyper 4 x y) z < hyper 4 x (hyper 4 y z) := by
  rw [← tet_eq_hyper4, ← tet_eq_hyper4, ← tet_eq_hyper4, ← tet_eq_hyper4]
  exact tet_ht_strict_of_two_le hx hy hz

end HyperTamari

#print axioms HyperTamari.succ_lt_pow_self
#print axioms HyperTamari.tet_ht_strict_two_two
#print axioms HyperTamari.tet_ht_strict_of_two_le
#print axioms HyperTamari.ht_rank4_strict_two
