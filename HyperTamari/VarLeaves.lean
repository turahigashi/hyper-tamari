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

end HyperTamari

#print axioms HyperTamari.eval_ofBTree
#print axioms HyperTamari.allLeaves_ofBTree
#print axioms HyperTamari.rot_ofBTree
#print axioms HyperTamari.Rot.eval_lt_of_var
#print axioms HyperTamari.LRot.preserves_star
#print axioms HyperTamari.LRot.eval_le_of_reflTransGen
#print axioms HyperTamari.LRot.eval_lt_of_transGen
#print axioms HyperTamari.LTree.two_le_eval
#print axioms HyperTamari.LRot.preserves
#print axioms HyperTamari.LRot.eval_le
#print axioms HyperTamari.LRot.eval_lt
