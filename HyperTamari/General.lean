import HyperTamari.Tetration

/-
# 一般階数の Hyperoperation–Tamari 不等式

rank 3（`ht_rank3`）と rank 4（`tet_ht`）を個別に証明したが、
実は**一様な構造**がある。

## 証明の構造（本ファイルの核）

$$
\underbrace{H_{r-1}\big(H_r(x,a),\,H_r(x,b)\big)\;\le\;H_r(x,\;a+b)}_{(\mathrm{SUM}_r)}
$$

* **(SUM$_r$) は (HT$_{r-1}$) から $a$ の帰納で出る。基底 $a=1$ は等号**：
  $H_{r-1}(H_r(x,1),H_r(x,b)) = H_{r-1}(x,H_r(x,b)) = H_r(x,b+1)$。
  帰納段は $H_r(x,a{+}1)=H_{r-1}(x,H_r(x,a))$ に **(HT$_{r-1}$)** を当てて
  $H_{r-1}(x,\,H_{r-1}(H_r(x,a),H_r(x,b)))$ へ移し、帰納法の仮定で
  $H_{r-1}(x,H_r(x,a{+}b))=H_r(x,a{+}b{+}1)$ にちょうど着地する。

* **(HT$_r$) は (SUM$_r$) ＋ $y+m\le H_{r-1}(y,m)$ から $z$ の帰納で出る。**

⇒ **(HT$_3$) を基底に、$r$ について段階的に上がる**。
-/

namespace HyperTamari

/-! ## 基本の単調性（`hyper` は整礎再帰なので一つずつ積む） -/

/-- $x\ge2,\;r\ge2,\;n\ge1$ なら $n+1 \le H_r(x,n)$。 -/
theorem succ_le_hyper {x : Nat} (hx : 2 ≤ x) :
    ∀ {r : Nat}, 2 ≤ r → ∀ {n : Nat}, 1 ≤ n → n + 1 ≤ hyper r x n := by
  intro r hr
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  induction s with
  | zero =>
      intro n hn
      rw [hyper_two]
      calc n + 1 ≤ 2 * n := by omega
      _ ≤ x * n := Nat.mul_le_mul_right _ hx
  | succ s ih =>
      intro n hn
      induction n with
      | zero => omega
      | succ n ihn =>
          rcases Nat.eq_zero_or_pos n with rfl | hn'
          · rw [show s + 1 + 2 = s + 3 from by ring, hyper_one_arg (by omega)]
            omega
          · have hprev := ihn hn'
            have h1 : 1 ≤ hyper (s + 1 + 2) x n := by omega
            have := ih (by omega) h1
            rw [show s + 1 + 2 = s + 2 + 1 from by ring] at *
            rw [hyper_succ]
            omega

/-- $x\ge2,\;r\ge2,\;n\ge1$ なら $2 \le H_r(x,n)$。 -/
theorem two_le_hyper {x : Nat} (hx : 2 ≤ x) {r : Nat} (hr : 2 ≤ r) {n : Nat} (hn : 1 ≤ n) :
    2 ≤ hyper r x n := by
  have := succ_le_hyper hx hr hn; omega

/-- $x\ge2,\;r\ge1,\;v\ge1$ なら $v \le H_r(x,v)$。 -/
theorem self_le_hyper {x : Nat} (hx : 2 ≤ x) :
    ∀ {r : Nat}, 1 ≤ r → ∀ {v : Nat}, 1 ≤ v → v ≤ hyper r x v := by
  intro r hr v hv
  rcases Nat.lt_or_ge r 2 with h1 | h2
  · have : r = 1 := by omega
    subst this
    rw [hyper_one]; omega
  · have := succ_le_hyper hx h2 hv; omega

/-- 第二引数について一段の単調性（$x\ge2,\;r\ge2,\;n\ge1$）。 -/
theorem hyper_step_mono {x : Nat} (hx : 2 ≤ x) {r : Nat} (hr : 2 ≤ r) {n : Nat} (hn : 1 ≤ n) :
    hyper r x n ≤ hyper r x (n + 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hv : 1 ≤ hyper (s + 1) x n := by
    have := two_le_hyper hx hr hn; omega
  rw [hyper_succ]
  exact self_le_hyper hx (by omega) hv

/-- 第二引数について単調（$x\ge2,\;r\ge2$、引数は $\ge1$）。 -/
theorem hyper_mono_arg {x : Nat} (hx : 2 ≤ x) {r : Nat} (hr : 2 ≤ r) :
    ∀ {m n : Nat}, 1 ≤ m → m ≤ n → hyper r x m ≤ hyper r x n := by
  intro m n hm hmn
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
      · exact le_refl _
      · have hmn' : m ≤ n := by omega
        have h1 := ih hmn'
        have h2 : hyper r x n ≤ hyper r x (n + 1) :=
          hyper_step_mono hx hr (by omega)
        omega

/-- **階数についての単調性**（$x\ge2,\;r\ge2,\;n\ge1$）。 -/
theorem hyper_rank_mono {x : Nat} (hx : 2 ≤ x) {r : Nat} (hr : 2 ≤ r) :
    ∀ {n : Nat}, 1 ≤ n → hyper r x n ≤ hyper (r + 1) x n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · rw [hyper_one_arg hr, hyper_one_arg (by omega)]
      · have hIH := ih hn'
        have hstep : hyper r x n ≥ n + 1 := succ_le_hyper hx hr hn'
        obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
        show hyper (s + 1) x (n + 1) ≤ hyper (s + 2) x (n + 1)
        calc hyper (s + 1) x (n + 1)
            ≤ hyper (s + 1) x (hyper (s + 1) x n) :=
              hyper_mono_arg hx hr (by omega) (by omega)
          _ ≤ hyper (s + 1) x (hyper (s + 2) x n) :=
              hyper_mono_arg hx hr (by omega) hIH
          _ = hyper (s + 2) x (n + 1) := (hyper_succ (s + 1) x n).symm

/-- $H_2 \le H_r$（$r\ge2$）。 -/
theorem two_le_rank_hyper {x : Nat} (hx : 2 ≤ x) :
    ∀ {r : Nat}, 2 ≤ r → ∀ {n : Nat}, 1 ≤ n → hyper 2 x n ≤ hyper r x n := by
  intro r hr
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  induction s with
  | zero => intro n _; exact le_refl _
  | succ s ih =>
      intro n hn
      calc hyper 2 x n ≤ hyper (s + 2) x n := ih (by omega) hn
      _ ≤ hyper (s + 3) x n := hyper_rank_mono hx (by omega) hn

/-- **(ADD)**：$u,v\ge2,\;s\ge2$ なら $u+v \le H_s(u,v)$。 -/
theorem add_le_hyper {u v : Nat} (hu : 2 ≤ u) (hv : 2 ≤ v) {s : Nat} (hs : 2 ≤ s) :
    u + v ≤ hyper s u v := by
  calc u + v ≤ u * v := Nat.add_le_mul hu hv
  _ = hyper 2 u v := (hyper_two u v).symm
  _ ≤ hyper s u v := two_le_rank_hyper hu hs (by omega)

/-! ## (SUM$_r$) — (HT$_{r-1}$) から出る -/

/-- **(SUM$_{s+1}$)**：$H_s\bigl(H_{s+1}(x,a),H_{s+1}(x,b)\bigr)\le H_{s+1}(x,a+b)$。
基底 $a=1$ は**等号**：$H_s(x,H_{s+1}(x,b))=H_{s+1}(x,b+1)$。 -/
theorem sum_lemma {x : Nat} (hx : 2 ≤ x) {s : Nat} (hs : 2 ≤ s)
    (ht_prev : ∀ p q : Nat, 2 ≤ p → 2 ≤ q → ∀ w : Nat,
        hyper s (hyper s p q) w ≤ hyper s p (hyper s q w)) :
    ∀ a b : Nat, 1 ≤ a → 1 ≤ b →
      hyper s (hyper (s + 1) x a) (hyper (s + 1) x b) ≤ hyper (s + 1) x (a + b) := by
  intro a b ha hb
  induction a with
  | zero => omega
  | succ a ih =>
      rcases Nat.eq_zero_or_pos a with rfl | ha'
      · -- a = 1：等号
        rw [hyper_one_arg (show 2 ≤ s + 1 by omega)]
        rw [show 0 + 1 + b = b + 1 from by omega, hyper_succ]
      · have hIH := ih ha'
        have hqa : 2 ≤ hyper (s + 1) x a := two_le_hyper hx (by omega) ha'
        have hqb : 1 ≤ hyper (s + 1) x b := by
          have := two_le_hyper hx (show 2 ≤ s + 1 by omega) hb; omega
        have hinner : 1 ≤ hyper s (hyper (s + 1) x a) (hyper (s + 1) x b) := by
          have := two_le_hyper (show 2 ≤ hyper (s + 1) x a from hqa) hs hqb; omega
        have hright : 1 ≤ hyper (s + 1) x (a + b) := by
          have := two_le_hyper hx (show 2 ≤ s + 1 by omega) (show 1 ≤ a + b by omega); omega
        calc hyper s (hyper (s + 1) x (a + 1)) (hyper (s + 1) x b)
            = hyper s (hyper s x (hyper (s + 1) x a)) (hyper (s + 1) x b) := by
              rw [hyper_succ]
          _ ≤ hyper s x (hyper s (hyper (s + 1) x a) (hyper (s + 1) x b)) :=
              ht_prev x (hyper (s + 1) x a) hx hqa _
          _ ≤ hyper s x (hyper (s + 1) x (a + b)) :=
              hyper_mono_arg hx hs hinner hIH
          _ = hyper (s + 1) x (a + b + 1) := (hyper_succ s x (a + b)).symm
          _ = hyper (s + 1) x (a + 1 + b) := by rw [show a + b + 1 = a + 1 + b from by omega]

/-! ## 一般階数の主定理 -/

/-- **(HT$_r$) は全階数 $r\ge3$ で成り立つ**。
$$H_r\bigl(H_r(x,y),z\bigr)\ \le\ H_r\bigl(x,H_r(y,z)\bigr)\qquad(x\ge2,\;y\ge2).$$
$r=3$ を基底に、(SUM$_r$) を通して $r$ について上がる。 -/
theorem ht_general : ∀ t : Nat, ∀ x y : Nat, 2 ≤ x → 2 ≤ y → ∀ z : Nat,
    hyper (t + 3) (hyper (t + 3) x y) z ≤ hyper (t + 3) x (hyper (t + 3) y z) := by
  intro t
  induction t with
  | zero => intro x y hx hy z; exact ht_rank3 (by omega) hy z
  | succ t ih =>
      intro x y hx hy
      have hsum := sum_lemma (x := x) hx (s := t + 3) (by omega)
        (fun p q hp hq w => ih p q hp hq w)
      have hA : 2 ≤ hyper (t + 4) x y := two_le_hyper hx (by omega) (by omega)
      intro z
      induction z with
      | zero =>
          have h0 : hyper (t + 1 + 3) (hyper (t + 1 + 3) x y) 0 = 1 := by
            rw [show t + 1 + 3 = t + 1 + 3 from rfl]; simp
          rw [h0, show t + 1 + 3 = t + 4 from by ring]
          have : hyper (t + 4) y 0 = 1 := by simp
          rw [this, hyper_one_arg (by omega)]
          omega
      | succ z ihz =>
          rcases Nat.eq_zero_or_pos z with rfl | hz
          · -- z = 0：両辺とも `hyper (t+4) x y`
            rw [show t + 1 + 3 = t + 4 from by ring]
            simp only [Nat.zero_add]
            rw [hyper_one_arg (show 2 ≤ t + 4 by omega) (hyper (t + 4) x y),
                hyper_one_arg (show 2 ≤ t + 4 by omega) y]
          · rw [show t + 1 + 3 = t + 4 from by ring] at *
            have hm : 2 ≤ hyper (t + 4) y z := two_le_hyper hy (by omega) hz
            have hym : 1 ≤ y + hyper (t + 4) y z := by omega
            have hadd : y + hyper (t + 4) y z ≤ hyper (t + 3) y (hyper (t + 4) y z) :=
              add_le_hyper hy hm (by omega)
            have hAz : 1 ≤ hyper (t + 4) (hyper (t + 4) x y) z := by
              have := two_le_hyper hA (show 2 ≤ t + 4 by omega) hz; omega
            calc hyper (t + 4) (hyper (t + 4) x y) (z + 1)
                = hyper (t + 3) (hyper (t + 4) x y)
                    (hyper (t + 4) (hyper (t + 4) x y) z) := hyper_succ _ _ _
              _ ≤ hyper (t + 3) (hyper (t + 4) x y)
                    (hyper (t + 4) x (hyper (t + 4) y z)) :=
                  hyper_mono_arg hA (by omega) hAz ihz
              _ ≤ hyper (t + 4) x (y + hyper (t + 4) y z) :=
                  hsum y (hyper (t + 4) y z) (by omega) (by omega)
              _ ≤ hyper (t + 4) x (hyper (t + 3) y (hyper (t + 4) y z)) :=
                  hyper_mono_arg hx (by omega) hym hadd
              _ = hyper (t + 4) x (hyper (t + 4) y (z + 1)) := by
                  rw [hyper_succ]

/-! ## 第一引数（底）についての単調性 と 全階数の Tamari 単調性

要旨は全階数の Tamari 単調性を主張しているのに、素朴な形の命題は
$r\in\{3,4\}$ に限定されていた。原因は**底についての単調性が一般階数で無かった**こと。
ここでそれを証明し、要旨に本文を合わせる。 -/

/-- 第二引数の単調性（$r\ge1$ 版）。 -/
theorem hyper_mono_arg' {x : Nat} (hx : 2 ≤ x) {r : Nat} (hr : 1 ≤ r) {m n : Nat}
    (hm : 1 ≤ m) (hmn : m ≤ n) : hyper r x m ≤ hyper r x n := by
  rcases Nat.lt_or_ge r 2 with h | h
  · have hr1 : r = 1 := by omega
    subst hr1
    rw [hyper_one, hyper_one]; omega
  · exact hyper_mono_arg hx h hm hmn

/-- **底についての単調性**：$2\le x\le x'$、$r\ge1$、$n\ge1$ なら
$H_r(x,n)\le H_r(x',n)$。階数と引数の二重帰納。 -/
theorem hyper_mono_base {x x' : Nat} (hx : 2 ≤ x) (hxx : x ≤ x') (s : Nat) :
    ∀ n : Nat, 1 ≤ n → hyper (s + 1) x n ≤ hyper (s + 1) x' n := by
  induction s with
  | zero =>
      intro n _
      rw [hyper_one, hyper_one]; omega
  | succ s ih =>
      intro n
      induction n with
      | zero => intro h; omega
      | succ n ihn =>
          intro _
          rcases Nat.eq_zero_or_pos n with rfl | hn'
          · rw [hyper_one_arg (show 2 ≤ s + 1 + 1 by omega),
                hyper_one_arg (show 2 ≤ s + 1 + 1 by omega)]
            exact hxx
          · have hIHn := ihn hn'
            have h1 : 1 ≤ hyper (s + 1 + 1) x n := by
              have := two_le_hyper hx (show 2 ≤ s + 1 + 1 by omega) hn'; omega
            have hx' : 2 ≤ x' := by omega
            rw [hyper_succ, hyper_succ]
            calc hyper (s + 1) x (hyper (s + 1 + 1) x n)
                ≤ hyper (s + 1) x' (hyper (s + 1 + 1) x n) := ih _ h1
              _ ≤ hyper (s + 1) x' (hyper (s + 1 + 1) x' n) :=
                  hyper_mono_arg' hx' (by omega) h1 hIHn

/-- $a\ge2$、$r\ge2$ なら評価はどの木でも $\ge2$。 -/
theorem two_le_eval {a : Nat} (ha : 2 ≤ a) {r : Nat} (hr : 2 ≤ r) :
    ∀ T : BTree, 2 ≤ BTree.eval r a T := by
  intro T
  induction T with
  | leaf => simpa using ha
  | node l rt ihl ihr =>
      rw [BTree.eval_node]
      exact two_le_hyper ihl hr (by omega)

/-- **全階数の Tamari 単調性**：$a\ge2$、$r\ge3$ のとき、
任意の節点での右回転（Tamari 被覆）は評価を減少させない。 -/
theorem Rot.eval_le {a : Nat} (ha : 2 ≤ a) {t : Nat} {T U : BTree} (h : Rot T U) :
    BTree.eval (t + 3) a T ≤ BTree.eval (t + 3) a U := by
  induction h with
  | root p q c =>
      simp only [BTree.eval_node]
      exact ht_general t _ _ (two_le_eval ha (by omega) p) (two_le_eval ha (by omega) q) _
  | @left l l' r _ ih =>
      simp only [BTree.eval_node]
      exact hyper_mono_base (two_le_eval ha (show 2 ≤ t + 3 by omega) l) ih (t + 2) _
        (by have := two_le_eval ha (show 2 ≤ t + 3 by omega) r; omega)
  | @right l r r' _ ih =>
      simp only [BTree.eval_node]
      exact hyper_mono_arg (two_le_eval ha (show 2 ≤ t + 3 by omega) l) (by omega)
        (by have := two_le_eval ha (show 2 ≤ t + 3 by omega) r; omega) ih

/-! ## 「高階では何でも爆発するから自明」ではないこと

この不等式は二つの座標が逆向きに競争している比較である。
左辺では第一引数が \(x\mapsto H_r(x,y)\gt x\) と大きくなり、
右辺では第二引数が \(z\mapsto H_r(y,z)\) と大きくなる。
「\(H_r\) は増加だから当然」という型の命題ではない。

さらに決定的なのは、**小さい引数のところに階数で爆発しない退化が残る**ことである。 -/

/-- **$H_r(2,2)=4$ が全階数 $r\ge2$ で成り立つ**。
$H_r(2,2)=H_{r-1}(2,H_r(2,1))=H_{r-1}(2,2)$ と降りて $H_2(2,2)=4$ に着く。
⇒ 階数をいくら上げても**ここは 4 のまま**であり、
「高階では何でも巨大になる」という直感は誤り。 -/
theorem hyper_two_two {r : Nat} (hr : 2 ≤ r) : hyper r 2 2 = 4 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  induction s with
  | zero => rw [hyper_two]
  | succ s ih =>
      have h1 : hyper (s + 1 + 2) 2 1 = 2 := hyper_one_arg (by omega) 2
      calc hyper (s + 1 + 2) 2 2
          = hyper (s + 2) 2 (hyper (s + 1 + 2) 2 1) := by
            rw [show s + 1 + 2 = s + 2 + 1 from by ring, hyper_succ]
        _ = hyper (s + 2) 2 2 := by rw [h1]
        _ = 4 := ih (by omega)

/-- 仮定 $y\ge2$ の鋭さ：$y=1$ にすると**全階数 $r\ge3$ で破れる**。
$H_r(x,1)=x$ かつ $H_r(1,z)=1$ なので、左辺は $H_r(x,z)$、右辺は $x$ になる。
$r=2$ では成り立たない（$H_2(1,z)=z$）。 -/
theorem hyper_one_base {r : Nat} (hr : 3 ≤ r) (z : Nat) : hyper r 1 z = 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
  induction z with
  | zero => simp
  | succ z ih =>
      rw [show s + 3 = s + 2 + 1 from by ring, hyper_succ]
      rw [show s + 2 + 1 = s + 3 from by ring, ih]
      exact hyper_one_arg (by omega) 1

/-! ## 等号の完全分類へ：$r\ge4$ なら $z\ge2$ で常に厳密

これが取れると
「rank 3 には唯一の非自明な等号 $(y,z)=(2,2)$ があり、rank 4 以後は消える」
という**相転移**が定理になる。

鍵は二つ：
1. (ADD) の**厳密版** $u+v\lt H_s(u,v)$ は $u,v\ge2$ かつ「どちらかが $\ge3$」で成り立つ。
   等号は**ちょうど $u=v=2$** のとき（$2+2=4=2\cdot2=H_s(2,2)$、`hyper_two_two`）。
2. 残る $y=z=2$ の場合は、$H_r(2,2)=4$ を使って**一階下の厳密性へ還元**できる。 -/

/-- 第二引数について**厳密**単調（$x\ge2$、$r\ge2$、$n\ge1$）。 -/
theorem hyper_lt_step {x : Nat} (hx : 2 ≤ x) {r : Nat} (hr : 2 ≤ r) {n : Nat} (hn : 1 ≤ n) :
    hyper r x n < hyper r x (n + 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have hv : 1 ≤ hyper (s + 2) x n := by
    have := two_le_hyper hx hr hn; omega
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · -- rank 2
    rw [hyper_two, hyper_two]
    have hxpos : 0 < x := by omega
    have : x * n < x * (n + 1) := by rw [Nat.mul_succ]; omega
    exact this
  · have key : hyper (s + 2) x (n + 1) = hyper (s + 1) x (hyper (s + 2) x n) :=
      hyper_succ (s + 1) x n
    rw [key]
    have := succ_le_hyper hx (show 2 ≤ s + 1 by omega) hv
    omega

/-- 第二引数について**厳密**単調（一般形）。 -/
theorem hyper_lt_arg {x : Nat} (hx : 2 ≤ x) {r : Nat} (hr : 2 ≤ r) {m n : Nat}
    (hm : 1 ≤ m) (hmn : m < n) : hyper r x m < hyper r x n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge m n with h | h
      · exact lt_trans (ih h) (hyper_lt_step hx hr (by omega))
      · have : m = n := by omega
        subst this
        exact hyper_lt_step hx hr hm

/-- **第一引数（底）についての厳密単調性**：$2\le x<x'$、$n\ge1$ なら
$H_{s+1}(x,n) < H_{s+1}(x',n)$。`hyper_mono_base` の厳密版で、
Tamari 被覆の左部分木を親へ持ち上げるのに使う。 -/
theorem hyper_lt_base {x x' : Nat} (hx : 2 ≤ x) (hxx : x < x') (s : Nat) :
    ∀ n : Nat, 1 ≤ n → hyper (s + 1) x n < hyper (s + 1) x' n := by
  induction s with
  | zero =>
      intro n _
      rw [hyper_one, hyper_one]; omega
  | succ s ih =>
      intro n
      induction n with
      | zero => intro h; omega
      | succ n ihn =>
          intro _
          rcases Nat.eq_zero_or_pos n with rfl | hn'
          · rw [hyper_one_arg (show 2 ≤ s + 1 + 1 by omega),
                hyper_one_arg (show 2 ≤ s + 1 + 1 by omega)]
            exact hxx
          · have hIHn := ihn hn'
            have h1 : 1 ≤ hyper (s + 1 + 1) x n := by
              have := two_le_hyper hx (show 2 ≤ s + 1 + 1 by omega) hn'; omega
            have hx' : 2 ≤ x' := by omega
            rw [hyper_succ, hyper_succ]
            calc hyper (s + 1) x (hyper (s + 1 + 1) x n)
                < hyper (s + 1) x' (hyper (s + 1 + 1) x n) := ih _ h1
              _ ≤ hyper (s + 1) x' (hyper (s + 1 + 1) x' n) :=
                  hyper_mono_arg' hx' (by omega) h1 (le_of_lt hIHn)

/-- **(ADD) の厳密版**：$u,v\ge2$ かつ $u\ge3$ または $v\ge3$ なら $u+v\lt H_s(u,v)$。 -/
theorem add_lt_hyper {u v : Nat} (hu : 2 ≤ u) (hv : 2 ≤ v) (h3 : 3 ≤ u ∨ 3 ≤ v)
    {s : Nat} (hs : 2 ≤ s) : u + v < hyper s u v := by
  have hmul : u + v < u * v := by
    obtain ⟨a, rfl⟩ : ∃ a, u = a + 2 := ⟨u - 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = b + 2 := ⟨v - 2, by omega⟩
    have hexp : (a + 2) * (b + 2) = a * b + 2 * a + 2 * b + 4 := by ring
    have hab : 1 ≤ a ∨ 1 ≤ b := by rcases h3 with h | h <;> omega
    rw [hexp]
    have hk : 0 ≤ a * b := Nat.zero_le _
    omega
  calc u + v < u * v := hmul
  _ = hyper 2 u v := (hyper_two u v).symm
  _ ≤ hyper s u v := two_le_rank_hyper hu hs (by omega)

/-- **$r\ge4$ では $z\ge2$ で常に厳密**。 -/
theorem ht_strict_general : ∀ t : Nat, ∀ x y z : Nat, 2 ≤ x → 2 ≤ y → 2 ≤ z →
    hyper (t + 4) (hyper (t + 4) x y) z < hyper (t + 4) x (hyper (t + 4) y z) := by
  intro t
  induction t with
  | zero => intro x y z hx hy hz; exact ht_rank4_strict_two hx hy hz
  | succ t ih =>
      intro x y z hx hy hz
      -- 階数 r = t+5、その一階下を s = t+4 とおく
      have hxA : 2 ≤ hyper (t + 5) x y := two_le_hyper hx (by omega) (by omega)
      obtain ⟨w, rfl⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
      have hw : 1 ≤ w := by omega
      have hm : 2 ≤ hyper (t + 5) y w := two_le_hyper hy (by omega) hw
      by_cases hcase : 3 ≤ y ∨ 2 ≤ w
      · -- 場合 (a)：厳密な鎖が通る
        have hm3 : 3 ≤ y ∨ 3 ≤ hyper (t + 5) y w := by
          rcases hcase with h | h
          · exact Or.inl h
          · refine Or.inr ?_
            have : hyper (t + 5) y 2 ≤ hyper (t + 5) y w := hyper_mono_arg hy (by omega) (by omega) h
            have h22 : 4 ≤ hyper (t + 5) y 2 := by
              have e : hyper (t + 5) y 1 = y := hyper_one_arg (by omega) y
              have : hyper (t + 5) y 2 = hyper (t + 4) y (hyper (t + 5) y 1) := by
                rw [show t + 5 = t + 4 + 1 from by ring, hyper_succ]
              rw [this, e]
              have := add_le_hyper hy hy (show 2 ≤ t + 4 by omega)
              omega
            omega
        have hsum := sum_lemma (x := x) hx (s := t + 4) (by omega)
          (fun p q hp hq v => ht_general (t + 1) p q hp hq v)
        have hAw : 1 ≤ hyper (t + 5) (hyper (t + 5) x y) w := by
          have := two_le_hyper hxA (show 2 ≤ t + 5 by omega) hw; omega
        have hstrict : y + hyper (t + 5) y w < hyper (t + 4) y (hyper (t + 5) y w) :=
          add_lt_hyper hy hm hm3 (by omega)
        calc hyper (t + 5) (hyper (t + 5) x y) (w + 1)
            = hyper (t + 4) (hyper (t + 5) x y)
                (hyper (t + 5) (hyper (t + 5) x y) w) := by
              rw [show t + 5 = t + 4 + 1 from by ring, hyper_succ]
          _ ≤ hyper (t + 4) (hyper (t + 5) x y)
                (hyper (t + 5) x (hyper (t + 5) y w)) :=
              hyper_mono_arg hxA (by omega) hAw
                (ht_general (t + 2) x y hx hy w)
          _ ≤ hyper (t + 5) x (y + hyper (t + 5) y w) :=
              hsum y (hyper (t + 5) y w) (by omega) (by omega)
          _ < hyper (t + 5) x (hyper (t + 4) y (hyper (t + 5) y w)) :=
              hyper_lt_arg hx (by omega) (by omega) hstrict
          _ = hyper (t + 5) x (hyper (t + 5) y (w + 1)) := by
              rw [show t + 5 = t + 4 + 1 from by ring, hyper_succ]
      · -- 場合 (b)：y = 2 かつ w = 1（すなわち z = 2）。一階下の厳密性へ還元
        push Not at hcase
        obtain ⟨hy2, hw2⟩ := hcase
        have hy' : y = 2 := by omega
        have hw' : w = 1 := by omega
        subst hy'; subst hw'
        -- A := H_r(x,2) = H_s(x,x)
        have hx1 : hyper (t + 5) x 1 = x := hyper_one_arg (by omega) x
        have hA : hyper (t + 5) x 2 = hyper (t + 4) x x := by
          rw [show (2:Nat) = 1 + 1 from rfl,
              show t + 5 = t + 4 + 1 from by ring, hyper_succ]
          rw [show t + 4 + 1 = t + 5 from by ring, hx1]
        set A := hyper (t + 4) x x with hAdef
        have hA2 : 2 ≤ A := by
          have := add_le_hyper hx hx (show 2 ≤ t + 4 by omega); omega
        -- 左辺 = H_s(A,A)
        have hLHS : hyper (t + 5) (hyper (t + 5) x 2) (1 + 1) = hyper (t + 4) A A := by
          rw [hA]
          have h1 : hyper (t + 5) A 1 = A := hyper_one_arg (by omega) A
          rw [show (1:Nat) + 1 = 1 + 1 from rfl,
              show t + 5 = t + 4 + 1 from by ring, hyper_succ]
          rw [show t + 4 + 1 = t + 5 from by ring, h1]
        -- 右辺 = H_s(x, H_s(x,A))
        have h22 : hyper (t + 5) 2 (1 + 1) = 4 := by
          simpa using hyper_two_two (r := t + 5) (by omega)
        have hRHS : hyper (t + 5) x (hyper (t + 5) 2 (1 + 1))
                  = hyper (t + 4) x (hyper (t + 4) x A) := by
          rw [h22]
          have e3 : hyper (t + 5) x 3 = hyper (t + 4) x A := by
            rw [show (3:Nat) = 2 + 1 from rfl,
                show t + 5 = t + 4 + 1 from by ring, hyper_succ]
            rw [show t + 4 + 1 = t + 5 from by ring, hA]
          rw [show (4:Nat) = 3 + 1 from rfl,
              show t + 5 = t + 4 + 1 from by ring, hyper_succ]
          rw [show t + 4 + 1 = t + 5 from by ring, e3]
        rw [hLHS, hRHS]
        -- 一階下の厳密性を (x, x, A) に適用
        have := ih x x A hx hx hA2
        rw [← hAdef] at this
        exact this

/-! ## **題名の定理**：$r\ge4$ では任意の Tamari 被覆で評価が真に増加する -/

/-- **全階数 $r\ge4$ の Tamari 厳密単調性**：$a\ge2$ のとき、
任意の節点での右回転（Tamari 被覆）は評価を**真に増加**させる。
`Rot.eval_le` の厳密版であり、rank 3 との二分法を完成させる。 -/
theorem Rot.eval_lt {a : Nat} (ha : 2 ≤ a) {t : Nat} {T U : BTree} (h : Rot T U) :
    BTree.eval (t + 4) a T < BTree.eval (t + 4) a U := by
  induction h with
  | root p q c =>
      simp only [BTree.eval_node]
      exact ht_strict_general t _ _ _
        (two_le_eval ha (show 2 ≤ t + 4 by omega) p)
        (two_le_eval ha (show 2 ≤ t + 4 by omega) q)
        (two_le_eval ha (show 2 ≤ t + 4 by omega) c)
  | @left l l' r _ ih =>
      simp only [BTree.eval_node]
      exact hyper_lt_base (two_le_eval ha (show 2 ≤ t + 4 by omega) l) ih (t + 3) _
        (by have := two_le_eval ha (show 2 ≤ t + 4 by omega) r; omega)
  | @right l r r' _ ih =>
      simp only [BTree.eval_node]
      exact hyper_lt_arg (two_le_eval ha (show 2 ≤ t + 4 by omega) l) (by omega)
        (by have := two_le_eval ha (show 2 ≤ t + 4 by omega) r; omega) ih

/-! ## Tamari 順序そのもの（被覆の反射推移閉包）への持ち上げ

Tamari 順序は右回転被覆 `Rot` の反射推移閉包である。上の二定理は一回の被覆に
ついての言明なので、順序そのものについての言明へ持ち上げておく。 -/

/-- **Tamari 順序についての単調性**：$a\ge2$、$r\ge3$ のとき、評価は
被覆の反射推移閉包（＝Tamari 順序）に沿って減少しない。 -/
theorem Rot.eval_le_of_reflTransGen {a : Nat} (ha : 2 ≤ a) {t : Nat} {T U : BTree}
    (h : Relation.ReflTransGen Rot T U) :
    BTree.eval (t + 3) a T ≤ BTree.eval (t + 3) a U := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hstep ih => exact Nat.le_trans ih (Rot.eval_le ha hstep)

/-- **Tamari 順序についての厳密単調性**：$a\ge2$、$r\ge4$ のとき、評価は
被覆の推移閉包に沿って真に増加する。すなわち $T<U$（Tamari 順序）ならば
$\mathrm{ev}(T)<\mathrm{ev}(U)$。 -/
theorem Rot.eval_lt_of_transGen {a : Nat} (ha : 2 ≤ a) {t : Nat} {T U : BTree}
    (h : Relation.TransGen Rot T U) :
    BTree.eval (t + 4) a T < BTree.eval (t + 4) a U := by
  induction h with
  | single hstep => exact Rot.eval_lt ha hstep
  | tail _ hstep ih => exact Nat.lt_trans ih (Rot.eval_lt ha hstep)

/-- どの階数 $r\ge2$ でも $z=1$ は等号（両辺とも $H_r(x,y)$）。 -/
theorem ht_eq_at_one {r : Nat} (hr : 2 ≤ r) (x y : Nat) :
    hyper r (hyper r x y) 1 = hyper r x (hyper r y 1) := by
  rw [hyper_one_arg hr, hyper_one_arg hr]

/-- **$z=0$ では厳密**：$r\ge3$、$x\ge2$ なら
$H_r(H_r(x,y),0)=1 < x = H_r(x,H_r(y,0))$。
（「等号 ⟺ $z=1$」を閉じるには $z=0$ の場合が要る。） -/
theorem ht_lt_at_zero {r : Nat} (hr : 3 ≤ r) {x : Nat} (hx : 2 ≤ x) (y : Nat) :
    hyper r (hyper r x y) 0 < hyper r x (hyper r y 0) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
  rw [hyper_succ_succ_zero, hyper_succ_succ_zero, hyper_one_arg (show 2 ≤ s + 3 by omega)]
  omega

/-- **等号の完全分類（相転移）**

* **rank 3** — $z=1$ のほかに**唯一の非自明な等号** $(y,z)=(2,2)$ が存在する。
* **rank $\ge4$** — $z\ge2$ では**等号は決して起こらない**。したがって等号は $z=1$ に限る。

⇒ 半結合律そのものは全階数を貫いて存続するが、その**退化は rank 4 で消える**。
これは「高階ほど自明になる」のではなく、**rank 4 で性質が安定化する**という定理である。 -/
theorem equality_classification :
    (∀ x : Nat, hyper 3 (hyper 3 x 2) 2 = hyper 3 x (hyper 3 2 2))
    ∧ (∀ t x y z : Nat, 2 ≤ x → 2 ≤ y → 2 ≤ z →
         hyper (t + 4) (hyper (t + 4) x y) z ≠ hyper (t + 4) x (hyper (t + 4) y z))
    ∧ (∀ r x y : Nat, 2 ≤ r →
         hyper r (hyper r x y) 1 = hyper r x (hyper r y 1))
    ∧ (∀ r x y : Nat, 3 ≤ r → 2 ≤ x →
         hyper r (hyper r x y) 0 ≠ hyper r x (hyper r y 0)) :=
  ⟨ht_rank3_equality_witness,
   fun t x y z hx hy hz => Nat.ne_of_lt (ht_strict_general t x y z hx hy hz),
   fun _ x y hr => ht_eq_at_one hr x y,
   fun _ _ y hr hx => Nat.ne_of_lt (ht_lt_at_zero hr hx y)⟩


/-! ## 補遺：論文の言明と一対一に対応させるための宣言 -/

/-- **(ADD) の等号条件**（論文 Lemma 6.3 の後半）：$u,v\ge2$、$s\ge2$ のとき
$u+v=H_s(u,v)$ ⟺ $u=v=2$。 -/
theorem add_eq_hyper_iff {u v : Nat} (hu : 2 ≤ u) (hv : 2 ≤ v) {s : Nat} (hs : 2 ≤ s) :
    u + v = hyper s u v ↔ u = 2 ∧ v = 2 := by
  constructor
  · intro h
    rcases Nat.lt_or_ge u 3 with hu3 | hu3
    · rcases Nat.lt_or_ge v 3 with hv3 | hv3
      · exact ⟨by omega, by omega⟩
      · have := add_lt_hyper hu hv (Or.inr hv3) hs; omega
    · have := add_lt_hyper hu hv (Or.inl hu3) hs; omega
  · rintro ⟨rfl, rfl⟩
    rw [hyper_two_two hs]

/-- $x < H_r(x,y)$（$x\ge2$、$r\ge2$、$y\ge2$）：左辺の第一引数は真に増える（論文 Remark 1.8）。 -/
theorem self_lt_hyper {x : Nat} (hx : 2 ≤ x) {r : Nat} (hr : 2 ≤ r) {y : Nat} (hy : 2 ≤ y) :
    x < hyper r x y := by
  calc x = hyper r x 1 := (hyper_one_arg hr x).symm
  _ < hyper r x y := hyper_lt_arg hx hr (le_refl 1) (by omega)

/-- **仮定 $y\ge2$ の鋭さ（全称形）**：$r\ge3$、$x,z\ge2$ のとき $y=1$ は不等式を**反転**させる。
$H_r(x,1)=x$、$H_r(1,z)=1$ なので右辺は $x$、左辺は $H_r(x,z)>x$。 -/
theorem ht_reversed_at_y_one {r : Nat} (hr : 3 ≤ r) {x z : Nat} (hx : 2 ≤ x) (hz : 2 ≤ z) :
    hyper r x (hyper r 1 z) < hyper r (hyper r x 1) z := by
  rw [hyper_one_base hr, hyper_one_arg (show 2 ≤ r by omega)]
  exact self_lt_hyper hx (by omega) hz

/-- $x=1$ では両辺とも $1$（$r\ge3$）。 -/
theorem ht_eq_at_x_one {r : Nat} (hr : 3 ≤ r) (y z : Nat) :
    hyper r (hyper r 1 y) z = hyper r 1 (hyper r y z) := by
  simp only [hyper_one_base hr]

/-- **論文 Proposition 6.2(2) の単独形**：(SUM$_{s+1}$) と $u+v\le H_s(u,v)$ から
(HT$_{s+1}$) が出る（$z$ の帰納）。`ht_general` の帰納段はこの形の議論である。 -/
theorem ht_of_sum {x : Nat} (hx : 2 ≤ x) {s : Nat} (hs : 2 ≤ s)
    (hsum : ∀ a b : Nat, 1 ≤ a → 1 ≤ b →
      hyper s (hyper (s + 1) x a) (hyper (s + 1) x b) ≤ hyper (s + 1) x (a + b))
    (hadd : ∀ u v : Nat, 2 ≤ u → 2 ≤ v → u + v ≤ hyper s u v)
    {y : Nat} (hy : 2 ≤ y) :
    ∀ z : Nat, hyper (s + 1) (hyper (s + 1) x y) z ≤ hyper (s + 1) x (hyper (s + 1) y z) := by
  have hA : 2 ≤ hyper (s + 1) x y := two_le_hyper hx (by omega) (by omega)
  intro z
  induction z with
  | zero =>
      obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
      rw [show u + 2 + 1 = u + 3 from by ring]
      simp only [hyper_succ_succ_zero]
      rw [hyper_one_arg (show 2 ≤ u + 3 by omega)]
      omega
  | succ z ihz =>
      rcases Nat.eq_zero_or_pos z with rfl | hz
      · simp only [Nat.zero_add]
        rw [hyper_one_arg (show 2 ≤ s + 1 by omega) (hyper (s + 1) x y),
            hyper_one_arg (show 2 ≤ s + 1 by omega) y]
      · have hm : 2 ≤ hyper (s + 1) y z := two_le_hyper hy (by omega) hz
        have hym : 1 ≤ y + hyper (s + 1) y z := by omega
        have haddm : y + hyper (s + 1) y z ≤ hyper s y (hyper (s + 1) y z) := hadd y _ hy hm
        have hAz : 1 ≤ hyper (s + 1) (hyper (s + 1) x y) z := by
          have := two_le_hyper hA (show 2 ≤ s + 1 by omega) hz; omega
        calc hyper (s + 1) (hyper (s + 1) x y) (z + 1)
            = hyper s (hyper (s + 1) x y) (hyper (s + 1) (hyper (s + 1) x y) z) :=
              hyper_succ _ _ _
          _ ≤ hyper s (hyper (s + 1) x y) (hyper (s + 1) x (hyper (s + 1) y z)) :=
              hyper_mono_arg hA hs hAz ihz
          _ ≤ hyper (s + 1) x (y + hyper (s + 1) y z) :=
              hsum y (hyper (s + 1) y z) (by omega) (by omega)
          _ ≤ hyper (s + 1) x (hyper s y (hyper (s + 1) y z)) :=
              hyper_mono_arg hx (by omega) hym haddm
          _ = hyper (s + 1) x (hyper (s + 1) y (z + 1)) := by rw [hyper_succ]



end HyperTamari






#print axioms HyperTamari.succ_le_hyper
#print axioms HyperTamari.two_le_hyper
#print axioms HyperTamari.self_le_hyper
#print axioms HyperTamari.hyper_step_mono
#print axioms HyperTamari.hyper_mono_arg
#print axioms HyperTamari.hyper_rank_mono
#print axioms HyperTamari.two_le_rank_hyper
#print axioms HyperTamari.add_le_hyper
#print axioms HyperTamari.sum_lemma
#print axioms HyperTamari.ht_general
#print axioms HyperTamari.hyper_mono_arg'
#print axioms HyperTamari.hyper_mono_base
#print axioms HyperTamari.two_le_eval
#print axioms HyperTamari.Rot.eval_le
#print axioms HyperTamari.hyper_two_two
#print axioms HyperTamari.hyper_one_base
#print axioms HyperTamari.hyper_lt_step
#print axioms HyperTamari.hyper_lt_arg
#print axioms HyperTamari.add_lt_hyper
#print axioms HyperTamari.ht_strict_general
#print axioms HyperTamari.ht_eq_at_one
#print axioms HyperTamari.Rot.eval_le_of_reflTransGen
#print axioms HyperTamari.Rot.eval_lt_of_transGen
#print axioms HyperTamari.ht_lt_at_zero
#print axioms HyperTamari.hyper_lt_base
#print axioms HyperTamari.Rot.eval_lt
#print axioms HyperTamari.equality_classification
#print axioms HyperTamari.add_eq_hyper_iff
#print axioms HyperTamari.self_lt_hyper
#print axioms HyperTamari.ht_reversed_at_y_one
#print axioms HyperTamari.ht_eq_at_x_one
#print axioms HyperTamari.ht_of_sum
