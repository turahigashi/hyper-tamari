import HyperTamari.General

/-!
# 葉ごとに異なる値を許す評価

`BTree.eval` は木のすべての葉に同じ値 `a` を入れる。ここでは葉ごとに任意の値を
許す評価を定義し、Tamari 被覆に沿った単調性と、階数 4 以上での厳密性を示す。

本ファイルに新しい数学は要らない。局所不等式 `ht_general` / `ht_strict_general` も、
底と引数についての単調性 `hyper_lt_base` / `hyper_lt_arg` も、
もともと三つの独立変数について述べられているからである。必要なのは評価の器だけである。
-/

namespace HyperTamari

/-- 葉に値をもつ二分木。 -/
inductive LTree where
  | leaf (a : Nat) : LTree
  | node (l r : LTree) : LTree
  deriving Repr, DecidableEq

namespace LTree

/-- 階数 `rk` での評価。葉はその葉自身の値をとる。 -/
def eval (rk : Nat) : LTree → Nat
  | leaf a => a
  | node l r => hyper rk (eval rk l) (eval rk r)

@[simp] theorem eval_leaf (rk a : Nat) : eval rk (leaf a) = a := rfl
@[simp] theorem eval_node (rk : Nat) (l r : LTree) :
    eval rk (node l r) = hyper rk (eval rk l) (eval rk r) := rfl

/-- すべての葉の値が `2` 以上であること。 -/
def AllLeavesTwoLe : LTree → Prop
  | leaf a => 2 ≤ a
  | node l r => AllLeavesTwoLe l ∧ AllLeavesTwoLe r

/-- すべての葉が `2` 以上なら評価も `2` 以上（階数 `2` 以上）。 -/
theorem two_le_eval {rk : Nat} (hrk : 2 ≤ rk) :
    ∀ T : LTree, AllLeavesTwoLe T → 2 ≤ eval rk T := by
  intro T
  induction T with
  | leaf a => intro h; exact h
  | node l r ihl ihr =>
      intro h
      have hl := ihl h.1
      exact two_le_hyper hl hrk (by have := ihr h.2; omega)

end LTree

/-- 任意の節点での右回転（Tamari 被覆）。葉の値は動かさない。 -/
inductive LRot : LTree → LTree → Prop where
  | root (a b c : LTree) :
      LRot (LTree.node (LTree.node a b) c) (LTree.node a (LTree.node b c))
  | left {l l' : LTree} (r : LTree) : LRot l l' → LRot (LTree.node l r) (LTree.node l' r)
  | right (l : LTree) {r r' : LTree} : LRot r r' → LRot (LTree.node l r) (LTree.node l r')

/-- 回転は葉の重複度を変えないので、葉の条件は保たれる。 -/
theorem LRot.preserves {T U : LTree} (h : LRot T U) :
    LTree.AllLeavesTwoLe T → LTree.AllLeavesTwoLe U := by
  induction h with
  | root a b c => intro h; exact ⟨h.1.1, h.1.2, h.2⟩
  | left r _ ih => intro h; exact ⟨ih h.1, h.2⟩
  | right l _ ih => intro h; exact ⟨h.1, ih h.2⟩

/-- **変数葉の Tamari 単調性**：すべての葉が `2` 以上なら、階数 `r ≥ 3` で
右回転は評価を減少させない。 -/
theorem LRot.eval_le {t : Nat} {T U : LTree} (h : LRot T U)
    (hT : LTree.AllLeavesTwoLe T) :
    LTree.eval (t + 3) T ≤ LTree.eval (t + 3) U := by
  induction h with
  | root p q c =>
      simp only [LTree.eval_node]
      exact ht_general t _ _
        (LTree.two_le_eval (by omega) p hT.1.1)
        (LTree.two_le_eval (by omega) q hT.1.2) _
  | @left l l' r _ ih =>
      simp only [LTree.eval_node]
      exact hyper_mono_base (LTree.two_le_eval (show 2 ≤ t + 3 by omega) l hT.1)
        (ih hT.1) (t + 2) _
        (by have := LTree.two_le_eval (show 2 ≤ t + 3 by omega) r hT.2; omega)
  | @right l r r' _ ih =>
      simp only [LTree.eval_node]
      exact hyper_mono_arg (LTree.two_le_eval (show 2 ≤ t + 3 by omega) l hT.1)
        (by omega)
        (by have := LTree.two_le_eval (show 2 ≤ t + 3 by omega) r hT.2; omega)
        (ih hT.2)

/-- **変数葉の厳密 Tamari 単調性**：すべての葉が `2` 以上なら、階数 `r ≥ 4` で
右回転は評価を真に増加させる。 -/
theorem LRot.eval_lt {t : Nat} {T U : LTree} (h : LRot T U)
    (hT : LTree.AllLeavesTwoLe T) :
    LTree.eval (t + 4) T < LTree.eval (t + 4) U := by
  induction h with
  | root p q c =>
      simp only [LTree.eval_node]
      exact ht_strict_general t _ _ _
        (LTree.two_le_eval (show 2 ≤ t + 4 by omega) p hT.1.1)
        (LTree.two_le_eval (show 2 ≤ t + 4 by omega) q hT.1.2)
        (LTree.two_le_eval (show 2 ≤ t + 4 by omega) c hT.2)
  | @left l l' r _ ih =>
      simp only [LTree.eval_node]
      exact hyper_lt_base (LTree.two_le_eval (show 2 ≤ t + 4 by omega) l hT.1)
        (ih hT.1) (t + 3) _
        (by have := LTree.two_le_eval (show 2 ≤ t + 4 by omega) r hT.2; omega)
  | @right l r r' _ ih =>
      simp only [LTree.eval_node]
      exact hyper_lt_arg (LTree.two_le_eval (show 2 ≤ t + 4 by omega) l hT.1)
        (by omega)
        (by have := LTree.two_le_eval (show 2 ≤ t + 4 by omega) r hT.2; omega)
        (ih hT.2)

/-! ## Tamari 順序そのものへの持ち上げ -/

/-- 反射推移閉包に沿って葉の条件が保たれる。 -/
theorem LRot.preserves_star {T U : LTree} (h : Relation.ReflTransGen LRot T U) :
    LTree.AllLeavesTwoLe T → LTree.AllLeavesTwoLe U := by
  induction h with
  | refl => exact id
  | tail _ hstep ih => exact fun hT => hstep.preserves (ih hT)

/-- **変数葉・Tamari 順序についての単調性**（階数 `r ≥ 3`）。 -/
theorem LRot.eval_le_of_reflTransGen {t : Nat} {T U : LTree}
    (h : Relation.ReflTransGen LRot T U) (hT : LTree.AllLeavesTwoLe T) :
    LTree.eval (t + 3) T ≤ LTree.eval (t + 3) U := by
  induction h with
  | refl => exact Nat.le_refl _
  | @tail V W hTV hstep ih =>
      exact Nat.le_trans ih (hstep.eval_le (LRot.preserves_star hTV hT))

/-- **変数葉・Tamari 順序についての厳密単調性**（階数 `r ≥ 4`）。
これは Chow が階数 3 について与えた変数葉の単調性を、Goodstein 階層の
すべての階数へ拡張し、さらに階数 4 以上では厳密であることまで述べたものである。 -/
theorem LRot.eval_lt_of_transGen {t : Nat} {T U : LTree}
    (h : Relation.TransGen LRot T U) (hT : LTree.AllLeavesTwoLe T) :
    LTree.eval (t + 4) T < LTree.eval (t + 4) U := by
  induction h with
  | single hstep => exact hstep.eval_lt hT
  | @tail V W hTV hstep ih =>
      have hV : LTree.AllLeavesTwoLe V :=
        LRot.preserves_star hTV.to_reflTransGen hT
      exact Nat.lt_trans ih (hstep.eval_lt hV)

/-! ## 階数 3 における被覆の等号の完全分類

階数 3 の局所等号は非自明には $(y,z)=(2,2)$ のみである。一方、葉がすべて $2$ 以上の木では
内部節点の評価は $4$ 以上になる。したがって階数 3 の被覆で等号が起こるのは、回転される
二つの部分木がともに「ラベル $2$ の葉」であるときに限る。 -/

/-- 葉がすべて `2` 以上なら、**内部節点**の評価は階数 `3` 以上で `4` 以上。 -/
theorem LTree.four_le_eval_node {t : Nat} (l r : LTree)
    (h : LTree.AllLeavesTwoLe (LTree.node l r)) :
    4 ≤ LTree.eval (t + 3) (LTree.node l r) := by
  have hl : 2 ≤ LTree.eval (t + 3) l := LTree.two_le_eval (by omega) l h.1
  have hr : 2 ≤ LTree.eval (t + 3) r := LTree.two_le_eval (by omega) r h.2
  have h4 : hyper (t + 3) 2 2 = 4 := hyper_two_two (by omega)
  calc (4 : Nat) = hyper (t + 3) 2 2 := h4.symm
    _ ≤ hyper (t + 3) (LTree.eval (t + 3) l) 2 :=
        hyper_mono_base (le_refl 2) hl (t + 2) 2 (by omega)
    _ ≤ hyper (t + 3) (LTree.eval (t + 3) l) (LTree.eval (t + 3) r) :=
        hyper_mono_arg hl (by omega) (by omega) hr

/-- 葉がすべて `2` 以上の木の評価が `2` に等しいのは、その木が
ラベル `2` の葉であるときに限る（階数 `3` 以上）。 -/
theorem LTree.eval_eq_two_iff {t : Nat} (T : LTree) (h : LTree.AllLeavesTwoLe T) :
    LTree.eval (t + 3) T = 2 ↔ T = LTree.leaf 2 := by
  constructor
  · intro he
    cases T with
    | leaf a => simp only [LTree.eval_leaf] at he; subst he; rfl
    | node l r =>
        have := LTree.four_le_eval_node (t := t) l r h
        omega
  · intro he; subst he; rfl

/-- **階数 3 の被覆における等号の必要条件**：根での回転が等号になるのは、
回転される二つの部分木がともにラベル `2` の葉であるときに限る。 -/
theorem LRot.root_eq_rank3_iff (A B C : LTree)
    (h : LTree.AllLeavesTwoLe (LTree.node (LTree.node A B) C)) :
    LTree.eval 3 (LTree.node (LTree.node A B) C)
      = LTree.eval 3 (LTree.node A (LTree.node B C))
    ↔ (B = LTree.leaf 2 ∧ C = LTree.leaf 2) := by
  have hA : 2 ≤ LTree.eval 3 A := LTree.two_le_eval (by omega) A h.1.1
  have hB : 2 ≤ LTree.eval 3 B := LTree.two_le_eval (by omega) B h.1.2
  have hC : 2 ≤ LTree.eval 3 C := LTree.two_le_eval (by omega) C h.2
  simp only [LTree.eval_node]
  rw [ht_rank3_eq_iff hA hB]
  constructor
  · rintro (hz | ⟨hy, hz⟩)
    · omega
    · exact ⟨(LTree.eval_eq_two_iff (t := 0) B h.1.2).mp hy,
             (LTree.eval_eq_two_iff (t := 0) C h.2).mp hz⟩
  · rintro ⟨hB2, hC2⟩
    subst hB2; subst hC2
    exact Or.inr ⟨rfl, rfl⟩

/-- **階数 3 でも葉がすべて `3` 以上なら、根での回転は厳密**。 -/
theorem LRot.root_lt_rank3_of_three_le (A B C : LTree)
    (h : LTree.AllLeavesTwoLe (LTree.node (LTree.node A B) C))
    (hB : B ≠ LTree.leaf 2) :
    LTree.eval 3 (LTree.node (LTree.node A B) C)
      < LTree.eval 3 (LTree.node A (LTree.node B C)) := by
  have hle : LTree.eval 3 (LTree.node (LTree.node A B) C)
      ≤ LTree.eval 3 (LTree.node A (LTree.node B C)) :=
    (LRot.root A B C).eval_le (t := 0) h
  have hne : LTree.eval 3 (LTree.node (LTree.node A B) C)
      ≠ LTree.eval 3 (LTree.node A (LTree.node B C)) := by
    intro he
    exact hB ((LRot.root_eq_rank3_iff A B C h).mp he).1
  exact Nat.lt_of_le_of_ne hle hne

/-! ## 単一ラベルの場合の埋め込み

`BTree` の評価は、すべての葉に同じ値を置いた `LTree` の評価である。したがって
前節の結果は単一ラベルの場合を特別な場合として含む。 -/

/-- すべての葉に `a` を置いて `BTree` を `LTree` に写す。 -/
def ofBTree (a : Nat) : BTree → LTree
  | BTree.leaf => LTree.leaf a
  | BTree.node l r => LTree.node (ofBTree a l) (ofBTree a r)

@[simp] theorem eval_ofBTree (rk a : Nat) :
    ∀ T : BTree, LTree.eval rk (ofBTree a T) = BTree.eval rk a T := by
  intro T
  induction T with
  | leaf => rfl
  | node l r ihl ihr => simp only [ofBTree, LTree.eval_node, BTree.eval_node, ihl, ihr]

theorem allLeaves_ofBTree {a : Nat} (ha : 2 ≤ a) :
    ∀ T : BTree, LTree.AllLeavesTwoLe (ofBTree a T) := by
  intro T
  induction T with
  | leaf => exact ha
  | node l r ihl ihr => exact ⟨ihl, ihr⟩

theorem rot_ofBTree (a : Nat) {T U : BTree} (h : Rot T U) :
    LRot (ofBTree a T) (ofBTree a U) := by
  induction h with
  | root p q c => exact LRot.root _ _ _
  | left r _ ih => exact LRot.left _ ih
  | right l _ ih => exact LRot.right _ ih

/-- **単一ラベルの場合は特別な場合である**：`Rot.eval_lt` は `LRot.eval_lt` から従う。 -/
theorem Rot.eval_lt_of_var {a : Nat} (ha : 2 ≤ a) {t : Nat} {T U : BTree} (h : Rot T U) :
    BTree.eval (t + 4) a T < BTree.eval (t + 4) a U := by
  have := (rot_ofBTree a h).eval_lt (t := t) (allLeaves_ofBTree ha T)
  simpa using this

/-- **単一ラベルの単調性も特別な場合である**：`Rot.eval_le` は `LRot.eval_le` から従う。 -/
theorem Rot.eval_le_of_var {a : Nat} (ha : 2 ≤ a) {t : Nat} {T U : BTree} (h : Rot T U) :
    BTree.eval (t + 3) a T ≤ BTree.eval (t + 3) a U := by
  have := (rot_ofBTree a h).eval_le (t := t) (allLeaves_ofBTree ha T)
  simpa using this

/-- 単一ラベルの被覆関係の反射推移閉包は、変数葉版の反射推移閉包へ移る。 -/
theorem reflTransGen_ofBTree (a : Nat) {T U : BTree}
    (h : Relation.ReflTransGen Rot T U) :
    Relation.ReflTransGen LRot (ofBTree a T) (ofBTree a U) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail V W _ hstep ih => exact ih.tail (rot_ofBTree a hstep)

/-- 単一ラベルの被覆関係の推移閉包は、変数葉版の推移閉包へ移る。 -/
theorem transGen_ofBTree (a : Nat) {T U : BTree}
    (h : Relation.TransGen Rot T U) :
    Relation.TransGen LRot (ofBTree a T) (ofBTree a U) := by
  induction h with
  | single hstep => exact Relation.TransGen.single (rot_ofBTree a hstep)
  | @tail V W _ hstep ih => exact ih.tail (rot_ofBTree a hstep)

/-- **単一ラベル・Tamari 順序についての単調性は特別な場合である**。 -/
theorem Rot.eval_le_of_reflTransGen_of_var {a : Nat} (ha : 2 ≤ a) {t : Nat} {T U : BTree}
    (h : Relation.ReflTransGen Rot T U) :
    BTree.eval (t + 3) a T ≤ BTree.eval (t + 3) a U := by
  have := LRot.eval_le_of_reflTransGen (t := t) (reflTransGen_ofBTree a h)
    (allLeaves_ofBTree ha T)
  simpa using this

/-- **単一ラベル・Tamari 順序についての厳密単調性は特別な場合である**。 -/
theorem Rot.eval_lt_of_transGen_of_var {a : Nat} (ha : 2 ≤ a) {t : Nat} {T U : BTree}
    (h : Relation.TransGen Rot T U) :
    BTree.eval (t + 4) a T < BTree.eval (t + 4) a U := by
  have := LRot.eval_lt_of_transGen (t := t) (transGen_ofBTree a h)
    (allLeaves_ofBTree ha T)
  simpa using this

#print axioms HyperTamari.Rot.eval_le_of_var
#print axioms HyperTamari.reflTransGen_ofBTree
#print axioms HyperTamari.transGen_ofBTree
#print axioms HyperTamari.Rot.eval_le_of_reflTransGen_of_var
#print axioms HyperTamari.Rot.eval_lt_of_transGen_of_var

/-! ## 単一ラベルでの二分法

一様なラベル $a$ を入れた場合、階数 3 の等号は $a=2$ でしか起こりえない。 -/

/-- **一様ラベル $a\ge3$ なら階数 3 でも根の回転は厳密**。
$(y,z)=(2,2)$ という唯一の非自明な等号は、葉のラベルが $3$ 以上だと到達できない。 -/
theorem rank3_root_lt_of_three_le {a : Nat} (ha : 3 ≤ a) (A B C : BTree) :
    BTree.eval 3 a (BTree.node (BTree.node A B) C)
      < BTree.eval 3 a (BTree.node A (BTree.node B C)) := by
  have h2 : 2 ≤ a := by omega
  have hall := allLeaves_ofBTree h2 (BTree.node (BTree.node A B) C)
  have hB : ofBTree a B ≠ LTree.leaf 2 := by
    cases B with
    | leaf =>
        intro he
        rw [ofBTree] at he
        injection he with hh
        omega
    | node l r =>
        intro he
        rw [ofBTree] at he
        simp at he
  have := LRot.root_lt_rank3_of_three_le (ofBTree a A) (ofBTree a B) (ofBTree a C)
    hall hB
  simpa [ofBTree] using this

/-- **二分法（単一ラベル）**：階数 3 で一様ラベル $a\ge3$、または階数 $r\ge4$ なら、
根の回転はつねに厳密である。等号が起こりうるのは $(r,a)=(3,2)$ のときに限る。
$(3,2)$ ではそれが実際に起こる（`rank3_rotation_not_strict`）。 -/
theorem cover_strict_unless_rank3_two {a : Nat} (ha : 2 ≤ a) (r : Nat) (hr : 3 ≤ r)
    (hne : ¬(r = 3 ∧ a = 2)) (A B C : BTree) :
    BTree.eval r a (BTree.node (BTree.node A B) C)
      < BTree.eval r a (BTree.node A (BTree.node B C)) := by
  rcases Nat.lt_or_ge r 4 with h3 | h4
  · have hr3 : r = 3 := by omega
    subst hr3
    have ha3 : 3 ≤ a := by
      rcases Nat.lt_or_ge a 3 with h | h
      · exact absurd ⟨rfl, by omega⟩ hne
      · exact h
    exact rank3_root_lt_of_three_le ha3 A B C
  · obtain ⟨t, rfl⟩ : ∃ t, r = t + 4 := ⟨r - 4, by omega⟩
    exact (Rot.root A B C).eval_lt ha

end HyperTamari

#print axioms HyperTamari.LTree.four_le_eval_node
#print axioms HyperTamari.LTree.eval_eq_two_iff
#print axioms HyperTamari.LRot.root_eq_rank3_iff
#print axioms HyperTamari.LRot.root_lt_rank3_of_three_le
#print axioms HyperTamari.rank3_root_lt_of_three_le
#print axioms HyperTamari.cover_strict_unless_rank3_two
#print axioms HyperTamari.eval_ofBTree
#print axioms HyperTamari.allLeaves_ofBTree
#print axioms HyperTamari.rot_ofBTree
#print axioms HyperTamari.Rot.eval_lt_of_var
#print axioms HyperTamari.LRot.preserves_star
#print axioms HyperTamari.LRot.eval_le_of_reflTransGen
#print axioms HyperTamari.LRot.eval_lt_of_transGen
#print axioms HyperTamari.LTree.eval_leaf
#print axioms HyperTamari.LTree.eval_node
#print axioms HyperTamari.LTree.two_le_eval
#print axioms HyperTamari.LRot.preserves
#print axioms HyperTamari.LRot.eval_le
#print axioms HyperTamari.LRot.eval_lt
