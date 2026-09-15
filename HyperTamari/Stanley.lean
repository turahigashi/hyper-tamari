import HyperTamari.VarLeaves
import HyperTamari.Nested

/-!
# The Stanley order at every rank

This file formalises Section 14 of

  *Evaluation orders on bracketings in the hyperoperation hierarchy*.

The Stanley covering relation, in its local tree form (Lemma 4.5 of the paper), is
`StRot`: at some node, `((A·B)·R)` becomes `(A·R')`, where `R'` is `R` with its leftmost
leaf `c` replaced by `(B·c)`.

The arithmetic input is the strict nested bound `H_r(H_r(x,y),z) < H_r(x,y+z)`
(Saibian's Theorem~I), which is proved for every `x ≥ 2` in `HyperTamari/Nested.lean` as
`nested_bound_strict`. Nothing is assumed.

Main result: `StRot.eval_lt` and its transitive closure `StRot.eval_lt_of_transGen` ---
evaluation is strictly increasing along the Stanley order at every rank `rk ≥ 4`.
-/

namespace HyperTamari
namespace LTree

/-- The label of the leftmost leaf. -/
def leftLeaf : LTree → Nat
  | leaf a => a
  | node l _ => leftLeaf l

/-- `graftLeft B R` is `R` with its leftmost leaf `c` replaced by the node `(B · c)`.
If `R = (((c·D₁)·D₂)⋯Dₘ)` then `graftLeft B R = ((((B·c)·D₁)·D₂)⋯Dₘ)`. -/
def graftLeft (B : LTree) : LTree → LTree
  | leaf c => node B (leaf c)
  | node l r => node (graftLeft B l) r

/-- `evalSubst rk R t` is the value of `R` when its leftmost leaf carries `t`.
This is the function called `G` in the paper. -/
def evalSubst (rk : Nat) : LTree → Nat → Nat
  | leaf _, t => t
  | node l r, t => hyper rk (evalSubst rk l t) (eval rk r)

@[simp] theorem evalSubst_leaf (rk a t : Nat) : evalSubst rk (leaf a) t = t := rfl
@[simp] theorem evalSubst_node (rk : Nat) (l r : LTree) (t : Nat) :
    evalSubst rk (node l r) t = hyper rk (evalSubst rk l t) (eval rk r) := rfl

/-- Evaluating is substituting the leftmost label. -/
theorem eval_eq_evalSubst (rk : Nat) : ∀ R : LTree, eval rk R = evalSubst rk R (leftLeaf R)
  | leaf _ => rfl
  | node l r => by simp [eval, evalSubst, leftLeaf, eval_eq_evalSubst rk l]

/-- Grafting on the left multiplies the leftmost value into the tree. -/
theorem eval_graftLeft (rk : Nat) (B : LTree) :
    ∀ R : LTree,
      eval rk (graftLeft B R) = evalSubst rk R (hyper rk (eval rk B) (leftLeaf R))
  | leaf c => by simp [graftLeft, eval, evalSubst, leftLeaf]
  | node l r => by simp [graftLeft, evalSubst, leftLeaf, eval_graftLeft rk B l]

theorem two_le_leftLeaf : ∀ R : LTree, AllLeavesTwoLe R → 2 ≤ leftLeaf R
  | leaf _, h => h
  | node l _, h => two_le_leftLeaf l h.1

theorem graftLeft_preserves (B : LTree) (hB : AllLeavesTwoLe B) :
    ∀ R : LTree, AllLeavesTwoLe R → AllLeavesTwoLe (graftLeft B R)
  | leaf _, h => ⟨hB, h⟩
  | node _ _, h => ⟨graftLeft_preserves B hB _ h.1, h.2⟩

theorem two_le_evalSubst {rk : Nat} (hrk : 2 ≤ rk) :
    ∀ R : LTree, AllLeavesTwoLe R → ∀ {t : Nat}, 2 ≤ t → 2 ≤ evalSubst rk R t
  | leaf _, _, _, ht => ht
  | node l r, h, t, ht => by
      have hl := two_le_evalSubst hrk l h.1 ht
      have hr := two_le_eval hrk r h.2
      exact two_le_hyper hl hrk (by omega)

/-- `evalSubst rk R` is strictly increasing on arguments `≥ 2`. -/
theorem evalSubst_lt {rk : Nat} (hrk : 2 ≤ rk) :
    ∀ R : LTree, AllLeavesTwoLe R → ∀ {s t : Nat}, 2 ≤ s → s < t →
      evalSubst rk R s < evalSubst rk R t
  | leaf _, _, _, _, _, hst => by simpa using hst
  | node l r, h, s, t, hs, hst => by
      have ih := evalSubst_lt hrk l h.1 hs hst
      have hbase : 2 ≤ evalSubst rk l s := two_le_evalSubst hrk l h.1 hs
      have hr : 2 ≤ eval rk r := two_le_eval hrk r h.2
      obtain ⟨u, rfl⟩ : ∃ u, rk = u + 1 := ⟨rk - 1, by omega⟩
      simpa using hyper_lt_base hbase ih u (eval (u + 1) r) (by omega)

/-- A strictly increasing integer function grows by at least the step. -/
theorem evalSubst_add_le {rk : Nat} (hrk : 2 ≤ rk) (R : LTree) (hR : AllLeavesTwoLe R)
    {t : Nat} (ht : 2 ≤ t) :
    ∀ b : Nat, evalSubst rk R t + b ≤ evalSubst rk R (t + b) := by
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
      have hassoc : t + (b + 1) = t + b + 1 := by omega
      have h1 : evalSubst rk R (t + b) < evalSubst rk R (t + b + 1) :=
        evalSubst_lt hrk R hR (by omega) (by omega)
      rw [hassoc]
      omega

/-- **The key estimate of the paper**: `b + G(c) ≤ G(b * c)`. -/
theorem add_evalSubst_le {rk : Nat} (hrk : 2 ≤ rk) (R : LTree) (hR : AllLeavesTwoLe R)
    {b c : Nat} (hb : 2 ≤ b) (hc : 2 ≤ c) :
    b + evalSubst rk R c ≤ evalSubst rk R (hyper rk b c) := by
  have hsum : b + c ≤ hyper rk b c := add_le_hyper hb hc hrk
  have h1 : evalSubst rk R c + b ≤ evalSubst rk R (c + b) :=
    evalSubst_add_le hrk R hR hc b
  have h2 : evalSubst rk R (c + b) ≤ evalSubst rk R (hyper rk b c) := by
    rcases Nat.eq_or_lt_of_le (by omega : c + b ≤ hyper rk b c) with h | h
    · rw [h]
    · exact Nat.le_of_lt (evalSubst_lt hrk R hR (by omega) h)
  omega

end LTree

/-- **The Stanley covering relation in local tree form** (Lemma 4.5).
At some node, `((A·B)·R)` becomes `(A·R')` where `R'` is `R` with its leftmost leaf `c`
replaced by `(B·c)`. -/
inductive StRot : LTree → LTree → Prop where
  | root (A B R : LTree) :
      StRot (LTree.node (LTree.node A B) R) (LTree.node A (LTree.graftLeft B R))
  | left {l l' : LTree} (r : LTree) : StRot l l' → StRot (LTree.node l r) (LTree.node l' r)
  | right (l : LTree) {r r' : LTree} : StRot r r' → StRot (LTree.node l r) (LTree.node l r')

theorem StRot.preserves {T U : LTree} (h : StRot T U) :
    LTree.AllLeavesTwoLe T → LTree.AllLeavesTwoLe U := by
  induction h with
  | root A B R => intro h; exact ⟨h.1.1, LTree.graftLeft_preserves B h.1.2 R h.2⟩
  | left r _ ih => intro h; exact ⟨ih h.1, h.2⟩
  | right l _ ih => intro h; exact ⟨h.1, ih h.2⟩

/-- **Evaluation is strictly increasing along a Stanley cover**, at every rank `rk ≥ 4`.

The arithmetic input is the strict nested bound `nested_bound_strict`. -/
theorem StRot.eval_lt {rk : Nat} (hrk : 4 ≤ rk)
    {T U : LTree} (h : StRot T U) (hT : LTree.AllLeavesTwoLe T) :
    LTree.eval rk T < LTree.eval rk U := by
  have hrk2 : 2 ≤ rk := by omega
  induction h with
  | root A B R =>
      obtain ⟨⟨hA, hB⟩, hR⟩ := hT
      set a := LTree.eval rk A with ha'
      set b := LTree.eval rk B with hb'
      set c := LTree.leftLeaf R with hc'
      have hA2 : 2 ≤ a := LTree.two_le_eval hrk2 A hA
      have hB2 : 2 ≤ b := LTree.two_le_eval hrk2 B hB
      have hC2 : 2 ≤ c := LTree.two_le_leftLeaf R hR
      have hG2 : 2 ≤ LTree.evalSubst rk R c := LTree.two_le_evalSubst hrk2 R hR hC2
      -- 左辺 = (a*b) * G(c)
      have hlhs : LTree.eval rk (LTree.node (LTree.node A B) R)
          = hyper rk (hyper rk a b) (LTree.evalSubst rk R c) := by
        simp [LTree.eval_eq_evalSubst rk R]
        rfl
      -- 右辺 = a * G(b*c)
      have hrhs : LTree.eval rk (LTree.node A (LTree.graftLeft B R))
          = hyper rk a (LTree.evalSubst rk R (hyper rk b c)) := by
        simp [LTree.eval_graftLeft]
        rfl
      have step1 : hyper rk (hyper rk a b) (LTree.evalSubst rk R c)
          < hyper rk a (b + LTree.evalSubst rk R c) :=
        nested_bound_strict hrk hA2 (by omega) (by omega)
      have step2 : hyper rk a (b + LTree.evalSubst rk R c)
          ≤ hyper rk a (LTree.evalSubst rk R (hyper rk b c)) :=
        hyper_mono_arg hA2 hrk2 (by omega)
          (LTree.add_evalSubst_le hrk2 R hR hB2 hC2)
      rw [hlhs, hrhs]; omega
  | left r _ ih =>
      obtain ⟨hl, hr⟩ := hT
      have h2 : 2 ≤ LTree.eval rk r := LTree.two_le_eval hrk2 r hr
      obtain ⟨u, rfl⟩ : ∃ u, rk = u + 1 := ⟨rk - 1, by omega⟩
      have hb : 2 ≤ LTree.eval (u + 1) _ := LTree.two_le_eval hrk2 _ hl
      simpa using hyper_lt_base hb (ih hl) u (LTree.eval (u + 1) r) (by omega)
  | right l _ ih =>
      obtain ⟨hl, hr⟩ := hT
      have hb : 2 ≤ LTree.eval rk l := LTree.two_le_eval hrk2 l hl
      have h2 := LTree.two_le_eval hrk2 _ hr
      simpa using hyper_lt_arg hb hrk2 (by omega) (ih hr)

theorem StRot.preserves_star {T U : LTree} (h : Relation.ReflTransGen StRot T U) :
    LTree.AllLeavesTwoLe T → LTree.AllLeavesTwoLe U := by
  induction h with
  | refl => exact id
  | tail _ hstep ih => intro hT; exact hstep.preserves (ih hT)

/-- **Along the whole Stanley order.** -/
theorem StRot.eval_lt_of_transGen {rk : Nat} (hrk : 4 ≤ rk)
    {T U : LTree} (h : Relation.TransGen StRot T U) (hT : LTree.AllLeavesTwoLe T) :
    LTree.eval rk T < LTree.eval rk U := by
  induction h with
  | single hstep => exact hstep.eval_lt hrk hT
  | tail hchain hstep ih =>
      have hmid := StRot.preserves_star (Relation.TransGen.to_reflTransGen hchain) hT
      exact lt_trans ih (hstep.eval_lt hrk hmid)

/-! ## Non-degeneracy

The witnesses below show (i) that `StRot` relates trees which the Tamari relation does
not, so the theorem is strictly stronger than `LRot.eval_lt`; (ii) that the conclusion
has content at that pair; and (iii) instances of the nested bound at rank four, computed
from the definition, which `nested_bound_strict` proves in general. -/

namespace Witness

open LTree

/-- `((2·2)·(2·2))`. -/
def C : LTree := node (node (leaf 2) (leaf 2)) (node (leaf 2) (leaf 2))
/-- `(2·((2·2)·2))`. -/
def Bt : LTree := node (leaf 2) (node (node (leaf 2) (leaf 2)) (leaf 2))

/-- `C` is Stanley-covered by `Bt`. This pair is **not** related by a Tamari rotation:
in the pentagon `T₄`, `C=((ab)(cd))` and `Bt=(a((bc)d))` are incomparable. -/
theorem C_StRot_Bt : StRot C Bt := by
  have h : graftLeft (leaf 2) (node (leaf 2) (leaf 2))
      = node (node (leaf 2) (leaf 2)) (leaf 2) := rfl
  have := StRot.root (leaf 2) (leaf 2) (node (leaf 2) (leaf 2))
  simpa [C, Bt, h] using this

theorem C_leaves : AllLeavesTwoLe C := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> exact Nat.le_refl 2

/-! 値の計算。`hyper` はカーネルで簡約しないので、`hyper_three` を経由する。 -/

theorem h4_2_1 : hyper 4 2 1 = 2 := by simp
theorem h4_2_2 : hyper 4 2 2 = 4 := by simp
theorem h4_2_3 : hyper 4 2 3 = 16 := by simp
theorem h4_4_1 : hyper 4 4 1 = 4 := by simp
theorem h4_3_1 : hyper 4 3 1 = 3 := by simp
theorem h4_3_2 : hyper 4 3 2 = 27 := by simp

set_option maxRecDepth 20000 in
/-- At rank $3$ the values are $256$ and $65536$: the conclusion is not vacuous. -/
theorem eval_C_lt_eval_Bt_rank3 :
    eval 3 C = 256 ∧ eval 3 Bt = 65536 ∧ eval 3 C < eval 3 Bt := by
  have hC : eval 3 C = 256 := by simp [C, eval]
  have hB : eval 3 Bt = 65536 := by
    show hyper 3 2 (hyper 3 (hyper 3 2 2) 2) = 65536
    rw [hyper_three, hyper_three, hyper_three]
    norm_num
  exact ⟨hC, hB, by omega⟩

/-- Instances of the nested bound at rank $4$, computed from the definition. -/
theorem saibian_instances :
    hyper 4 (hyper 4 2 1) 1 < hyper 4 2 (1 + 1) ∧
    hyper 4 (hyper 4 2 1) 2 < hyper 4 2 (1 + 2) ∧
    hyper 4 (hyper 4 2 2) 1 < hyper 4 2 (2 + 1) ∧
    hyper 4 (hyper 4 3 1) 1 < hyper 4 3 (1 + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h4_2_1]; rw [show (1:Nat)+1 = 2 from rfl, h4_2_1, h4_2_2]; omega
  · rw [h4_2_1]; rw [show (1:Nat)+2 = 3 from rfl, h4_2_2, h4_2_3]; omega
  · rw [h4_2_2]; rw [show (2:Nat)+1 = 3 from rfl, h4_4_1, h4_2_3]; omega
  · rw [h4_3_1]; rw [show (1:Nat)+1 = 2 from rfl, h4_3_1, h4_3_2]; omega

end Witness


/-! ## Rank three (Theorem 7.1 of the paper)

At rank three the collapsing law `(x^y)^z = x^(yz)` makes the function `G` of
`evalSubst` a pure power, and the whole cover inequality reduces to `b·c^K ≤ b^(Kc)`.
The result is Chow's; this is only a shorter proof of it. -/

namespace LTree

/-- `K` of the paper: the product of the sibling values along the left spine. -/
def Kof : LTree → Nat
  | leaf _ => 1
  | node l r => Kof l * eval 3 r

theorem one_le_Kof : ∀ R : LTree, AllLeavesTwoLe R → 1 ≤ Kof R
  | leaf _, _ => Nat.le_refl 1
  | node l r, h => by
      have hl := one_le_Kof l h.1
      have hr : 2 ≤ eval 3 r := two_le_eval (by omega) r h.2
      have hK : Kof (node l r) = Kof l * eval 3 r := rfl
      have hpos : 1 ≤ Kof l * eval 3 r := Nat.one_le_iff_ne_zero.mpr (by
        intro hz
        rcases Nat.mul_eq_zero.mp hz with h0 | h0 <;> omega)
      omega

/-- At rank three, `G(t) = t^K`. -/
theorem evalSubst_rank3 : ∀ (R : LTree) (t : Nat), evalSubst 3 R t = t ^ Kof R
  | leaf _, t => by simp [evalSubst, Kof]
  | node l r, t => by
      have ih := evalSubst_rank3 l t
      show hyper 3 (evalSubst 3 l t) (eval 3 r) = t ^ (Kof l * eval 3 r)
      rw [hyper_three, ih, ← pow_mul]

end LTree

/-- `c ≤ b^(c-1)` for `b, c ≥ 2`, stated without subtraction. -/
theorem le_pow_pred : ∀ (b c : Nat), 2 ≤ b → 2 ≤ c → c ≤ b ^ (c - 1) := by
  intro b c hb
  induction c with
  | zero => omega
  | succ c ih =>
      intro _
      rcases Nat.lt_or_ge c 2 with h | h
      · have : c = 1 := by omega
        subst this; simpa using hb
      · have hc := ih h
        have hp : 1 ≤ b ^ (c - 1) := Nat.one_le_pow _ _ (by omega)
        have hstep : b ^ (c + 1 - 1) = b * b ^ (c - 1) := by
          have : c + 1 - 1 = (c - 1) + 1 := by omega
          rw [this]; ring
        have h2 : 2 * b ^ (c - 1) ≤ b * b ^ (c - 1) := Nat.mul_le_mul_right _ hb
        omega

/-- **Theorem 7.1**: at rank three, evaluation is monotone along a Stanley cover. -/
theorem StRot.eval_le_rank3 {T U : LTree} (h : StRot T U)
    (hT : LTree.AllLeavesTwoLe T) :
    LTree.eval 3 T ≤ LTree.eval 3 U := by
  induction h with
  | root A B R =>
      obtain ⟨⟨hA, hB⟩, hR⟩ := hT
      have hA2 : 2 ≤ LTree.eval 3 A := LTree.two_le_eval (by omega) A hA
      have hB2 : 2 ≤ LTree.eval 3 B := LTree.two_le_eval (by omega) B hB
      have hC2 : 2 ≤ LTree.leftLeaf R := LTree.two_le_leftLeaf R hR
      have hK1 : 1 ≤ LTree.Kof R := LTree.one_le_Kof R hR
      set a := LTree.eval 3 A
      set b := LTree.eval 3 B
      set c := LTree.leftLeaf R
      set K := LTree.Kof R
      -- 指数の比較: b * c^K ≤ b^(K*c)
      have key : b * c ^ K ≤ b ^ (K * c) := by
        have h1 : c ≤ b ^ (c - 1) := le_pow_pred b c hB2 hC2
        have h2 : c ^ K ≤ (b ^ (c - 1)) ^ K := Nat.pow_le_pow_left h1 K
        have h3 : (b ^ (c - 1)) ^ K = b ^ ((c - 1) * K) := by rw [← pow_mul]
        have h4 : b * b ^ ((c - 1) * K) = b ^ ((c - 1) * K + 1) := by ring
        have h5 : (c - 1) * K + 1 ≤ K * c := by
          have : (c - 1) * K + K = K * c := by
            have hc : c - 1 + 1 = c := by omega
            calc (c - 1) * K + K = ((c - 1) + 1) * K := by ring
              _ = c * K := by rw [hc]
              _ = K * c := by ring
          omega
        calc b * c ^ K ≤ b * b ^ ((c - 1) * K) := Nat.mul_le_mul_left _ (by rw [← h3]; exact h2)
          _ = b ^ ((c - 1) * K + 1) := h4
          _ ≤ b ^ (K * c) := Nat.pow_le_pow_right (by omega) h5
      have hlhs : LTree.eval 3 (LTree.node (LTree.node A B) R) = a ^ (b * c ^ K) := by
        show hyper 3 (hyper 3 a b) (LTree.eval 3 R) = a ^ (b * c ^ K)
        rw [LTree.eval_eq_evalSubst 3 R, LTree.evalSubst_rank3, hyper_three, hyper_three,
            ← pow_mul]
      have hrhs : LTree.eval 3 (LTree.node A (LTree.graftLeft B R)) = a ^ (b ^ (K * c)) := by
        show hyper 3 a (LTree.eval 3 (LTree.graftLeft B R)) = a ^ (b ^ (K * c))
        rw [LTree.eval_graftLeft, LTree.evalSubst_rank3, hyper_three, hyper_three,
            ← pow_mul, Nat.mul_comm c K]
      rw [hlhs, hrhs]
      exact Nat.pow_le_pow_right (by omega) key
  | left r _ ih =>
      obtain ⟨hl, hr⟩ := hT
      have h2 : 2 ≤ LTree.eval 3 r := LTree.two_le_eval (by omega) r hr
      have hb : 2 ≤ LTree.eval 3 _ := LTree.two_le_eval (by omega) _ hl
      simpa using hyper_mono_base hb (ih hl) 2 (LTree.eval 3 r) (by omega)
  | right l _ ih =>
      obtain ⟨hl, hr⟩ := hT
      have hb : 2 ≤ LTree.eval 3 l := LTree.two_le_eval (by omega) l hl
      have h2 : 2 ≤ LTree.eval 3 _ := LTree.two_le_eval (by omega) _ hr
      exact hyper_mono_arg (x := LTree.eval 3 l) hb (r := 3) (by omega)
        (by omega) (ih hr)

/-- Along the whole Stanley order at rank three. -/
theorem StRot.eval_le_rank3_star {T U : LTree} (h : Relation.ReflTransGen StRot T U)
    (hT : LTree.AllLeavesTwoLe T) : LTree.eval 3 T ≤ LTree.eval 3 U := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail hchain hstep ih =>
      have hmid := StRot.preserves_star hchain hT
      exact le_trans ih (hstep.eval_le_rank3 hmid)

/-! ## 公理監査 -/

#print axioms HyperTamari.LTree.evalSubst_leaf
#print axioms HyperTamari.LTree.evalSubst_node
#print axioms HyperTamari.LTree.eval_eq_evalSubst
#print axioms HyperTamari.LTree.eval_graftLeft
#print axioms HyperTamari.LTree.two_le_leftLeaf
#print axioms HyperTamari.LTree.graftLeft_preserves
#print axioms HyperTamari.LTree.two_le_evalSubst
#print axioms HyperTamari.LTree.evalSubst_lt
#print axioms HyperTamari.LTree.evalSubst_add_le
#print axioms HyperTamari.LTree.add_evalSubst_le
#print axioms HyperTamari.StRot.preserves
#print axioms HyperTamari.StRot.eval_lt
#print axioms HyperTamari.StRot.preserves_star
#print axioms HyperTamari.StRot.eval_lt_of_transGen
#print axioms HyperTamari.Witness.C_StRot_Bt
#print axioms HyperTamari.Witness.C_leaves
#print axioms HyperTamari.Witness.h4_2_1
#print axioms HyperTamari.Witness.h4_2_2
#print axioms HyperTamari.Witness.h4_2_3
#print axioms HyperTamari.Witness.h4_4_1
#print axioms HyperTamari.Witness.h4_3_1
#print axioms HyperTamari.Witness.h4_3_2
#print axioms HyperTamari.Witness.eval_C_lt_eval_Bt_rank3
#print axioms HyperTamari.Witness.saibian_instances
#print axioms HyperTamari.LTree.one_le_Kof
#print axioms HyperTamari.LTree.evalSubst_rank3
#print axioms HyperTamari.le_pow_pred
#print axioms HyperTamari.StRot.eval_le_rank3
#print axioms HyperTamari.StRot.eval_le_rank3_star

end HyperTamari
