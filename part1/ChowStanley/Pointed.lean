import ChowStanley.Tower

/-!
# Trees, pointed trees, and the separation theorem

This file contains the contribution of

  *The evaluation order of iterated exponentiation is the Stanley order*.

A `PTree` is a binary tree with one distinguished leaf, the *hole*.  `PTree.val P t` is
the value of the underlying tree, read with exponentiation at every node, when the hole
carries `t` and every other leaf carries `2`.  This is exactly the family of assignments
that the proof uses, and it makes the induction of Proposition 6.3 a plain structural
induction.

* `PTree.F_rdepth_le_val`  and  `PTree.val_le_F_rdepth`  are Proposition 6.3.
* `PTree.separation` is Theorem 1.2: if the hole of `Q` sits at a strictly smaller right
  depth than the hole of `P`, then the single value `M = 2 * (PTree.K Q)^2` at the hole,
  with every other leaf left at `2`, already gives `val Q M < val P M`.

Nothing here uses classical logic.
-/

namespace ChowStanley

/-- Binary trees: a leaf, or an ordered pair. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree
  deriving DecidableEq, Repr

namespace Tree

/-- The value of a tree, read with exponentiation at every node, when every leaf
carries `2`. -/
def two : Tree → Nat
  | leaf => 2
  | node L R => L.two ^ R.two

/-- Every value is at least `2`. -/
theorem two_le_two : ∀ T : Tree, 2 ≤ T.two
  | leaf => Nat.le_refl 2
  | node L R => by
      have hL : 2 ≤ L.two := L.two_le_two
      have hR : 2 ≤ R.two := R.two_le_two
      calc (2:Nat) ≤ L.two := hL
        _ = L.two ^ 1 := (pow_one _).symm
        _ ≤ L.two ^ R.two := Nat.pow_le_pow_right (by omega) (by omega)

/-- The number of leaves. -/
def numLeaves : Tree → Nat
  | leaf => 1
  | node L R => L.numLeaves + R.numLeaves

/-- The right-depth sequence: `rseq T` lists, for each leaf from left to right, the
number of right branches on the path from the root to that leaf. -/
def rseq : Tree → List Nat
  | leaf => [0]
  | node L R => L.rseq ++ R.rseq.map (· + 1)

@[simp] theorem rseq_length : ∀ T : Tree, T.rseq.length = T.numLeaves
  | leaf => rfl
  | node L R => by simp [rseq, numLeaves, rseq_length L, rseq_length R]

end Tree

/-- A binary tree with one distinguished leaf, the *hole*. -/
inductive PTree where
  | hole  : PTree
  | left  : PTree → Tree → PTree
  | right : Tree → PTree → PTree
  deriving Repr, Inhabited

namespace PTree

/-- The underlying tree, obtained by filling the hole with a leaf. -/
def tree : PTree → Tree
  | hole => Tree.leaf
  | left P R => Tree.node P.tree R
  | right L P => Tree.node L P.tree

/-- The right depth of the hole: the number of right branches from the root to it. -/
def rdepth : PTree → Nat
  | hole => 0
  | left P _ => P.rdepth
  | right _ P => P.rdepth + 1

/-- `K P` is the product of the all-`2` values of the sibling subtrees met on the path
from the hole to the root (Definition 6.1). -/
def K : PTree → Nat
  | hole => 1
  | left P R => P.K * R.two
  | right L P => P.K * L.two

/-- `val P t` is the value of the underlying tree when the hole carries `t` and every
other leaf carries `2`. -/
def val : PTree → Nat → Nat
  | hole,      t => t
  | left P R,  t => (P.val t) ^ R.two
  | right L P, t => L.two ^ (P.val t)

theorem one_le_K : ∀ P : PTree, 1 ≤ P.K
  | hole => Nat.le_refl 1
  | left P R => by
      have := P.one_le_K
      have hR := R.two_le_two
      have : 1 * 1 ≤ P.K * R.two := Nat.mul_le_mul (by omega) (by omega)
      simpa [K] using this
  | right L P => by
      have := P.one_le_K
      have hL := L.two_le_two
      have : 1 * 1 ≤ P.K * L.two := Nat.mul_le_mul (by omega) (by omega)
      simpa [K] using this

theorem two_le_val {t : Nat} (ht : 2 ≤ t) : ∀ P : PTree, 2 ≤ P.val t
  | hole => ht
  | left P R => by
      have ih : 2 ≤ P.val t := two_le_val ht P
      have hR := R.two_le_two
      calc (2:Nat) ≤ P.val t := ih
        _ = (P.val t) ^ 1 := (pow_one _).symm
        _ ≤ (P.val t) ^ R.two := Nat.pow_le_pow_right (by omega) (by omega)
  | right L P => by
      have ih : 2 ≤ P.val t := two_le_val ht P
      have hL := L.two_le_two
      calc (2:Nat) ≤ L.two := hL
        _ = L.two ^ 1 := (pow_one _).symm
        _ ≤ L.two ^ (P.val t) := Nat.pow_le_pow_right (by omega) (by omega)

/-- Filling the hole with `2` gives the all-`2` value of the underlying tree. -/
theorem val_two : ∀ P : PTree, P.val 2 = P.tree.two
  | hole => rfl
  | left P R => by simp [val, tree, Tree.two, val_two P]
  | right L P => by simp [val, tree, Tree.two, val_two P]

/-! ### Proposition 6.3: two-sided bounds -/

/-- Lower bound of Proposition 6.3. -/
theorem F_rdepth_le_val {t : Nat} (ht : 2 ≤ t) :
    ∀ P : PTree, Tower.F P.rdepth t ≤ P.val t
  | hole => Nat.le_refl t
  | left P R => by
      have ih := F_rdepth_le_val ht P
      have hv : 2 ≤ P.val t := two_le_val ht P
      have hR := R.two_le_two
      have : P.val t ≤ (P.val t) ^ R.two := by
        calc P.val t = (P.val t) ^ 1 := (pow_one _).symm
          _ ≤ (P.val t) ^ R.two := Nat.pow_le_pow_right (by omega) (by omega)
      simpa [rdepth, val] using le_trans ih this
  | right L P => by
      have ih := F_rdepth_le_val ht P
      have hL := L.two_le_two
      have h1 : (2:Nat) ^ (Tower.F P.rdepth t) ≤ 2 ^ (P.val t) :=
        Nat.pow_le_pow_right (by omega) ih
      have h2 : (2:Nat) ^ (P.val t) ≤ L.two ^ (P.val t) :=
        Nat.pow_le_pow_left hL _
      simpa [rdepth, val] using le_trans h1 h2

/-- `2 ≤ t ^ K` whenever `2 ≤ t` and `1 ≤ K`. -/
private theorem two_le_pow {t K : Nat} (ht : 2 ≤ t) (hK : 1 ≤ K) : 2 ≤ t ^ K := by
  calc (2:Nat) ≤ t := ht
    _ = t ^ 1 := (pow_one _).symm
    _ ≤ t ^ K := Nat.pow_le_pow_right (by omega) hK

/-- Upper bound of Proposition 6.3. -/
theorem val_le_F_rdepth {t : Nat} (ht : 2 ≤ t) :
    ∀ P : PTree, P.val t ≤ Tower.F P.rdepth (t ^ P.K)
  | hole => by simp [rdepth, val, K]
  | left P R => by
      have ih := val_le_F_rdepth ht P
      have hK := P.one_le_K
      have hR := R.two_le_two
      have htK : 2 ≤ t ^ P.K := two_le_pow ht hK
      have s1 : (P.val t) ^ R.two ≤ (Tower.F P.rdepth (t ^ P.K)) ^ R.two :=
        Nat.pow_le_pow_left ih _
      have s2 : (Tower.F P.rdepth (t ^ P.K)) ^ R.two
          ≤ Tower.F P.rdepth ((t ^ P.K) ^ R.two) :=
        Tower.F_pow_le htK (by omega) _
      have s3 : (t ^ P.K) ^ R.two = t ^ (P.K * R.two) := by rw [← pow_mul]
      calc (P.val t) ^ R.two ≤ (Tower.F P.rdepth (t ^ P.K)) ^ R.two := s1
        _ ≤ Tower.F P.rdepth ((t ^ P.K) ^ R.two) := s2
        _ = Tower.F P.rdepth (t ^ (P.K * R.two)) := by rw [s3]
  | right L P => by
      have ih := val_le_F_rdepth ht P
      have hK := P.one_le_K
      have hL := L.two_le_two
      have hv : 2 ≤ P.val t := two_le_val ht P
      have htK : 2 ≤ t ^ P.K := two_le_pow ht hK
      have s0 : L.two ^ (P.val t) ≤ 2 ^ ((P.val t) ^ L.two) :=
        Tower.pow_le_two_pow hL hv
      have s1 : (P.val t) ^ L.two ≤ (Tower.F P.rdepth (t ^ P.K)) ^ L.two :=
        Nat.pow_le_pow_left ih _
      have s2 : (Tower.F P.rdepth (t ^ P.K)) ^ L.two
          ≤ Tower.F P.rdepth ((t ^ P.K) ^ L.two) :=
        Tower.F_pow_le htK (by omega) _
      have s3 : (t ^ P.K) ^ L.two = t ^ (P.K * L.two) := by rw [← pow_mul]
      have chain : (P.val t) ^ L.two ≤ Tower.F P.rdepth (t ^ (P.K * L.two)) := by
        calc (P.val t) ^ L.two ≤ (Tower.F P.rdepth (t ^ P.K)) ^ L.two := s1
          _ ≤ Tower.F P.rdepth ((t ^ P.K) ^ L.two) := s2
          _ = Tower.F P.rdepth (t ^ (P.K * L.two)) := by rw [s3]
      have : (2:Nat) ^ ((P.val t) ^ L.two)
          ≤ 2 ^ (Tower.F P.rdepth (t ^ (P.K * L.two))) :=
        Nat.pow_le_pow_right (by omega) chain
      simpa [rdepth, val, K] using le_trans s0 this

/-! ### Theorem 1.2: separation by a single leaf -/

/-- **Separation by a single leaf** (Theorem 1.2).  If the hole of `Q` sits at a strictly
smaller right depth than the hole of `P`, then putting `M = 2 * (K Q)^2` at the hole and
leaving every other leaf at `2` already makes `P` the larger. -/
theorem separation {P Q : PTree} (h : Q.rdepth < P.rdepth) :
    Q.val (2 * Q.K ^ 2) < P.val (2 * Q.K ^ 2) := by
  have hK : 1 ≤ Q.K := Q.one_le_K
  have hKsq : 1 ≤ Q.K ^ 2 := by
    calc (1:Nat) = 1 ^ 2 := by norm_num
      _ ≤ Q.K ^ 2 := Nat.pow_le_pow_left hK 2
  have hM : 2 ≤ 2 * Q.K ^ 2 := by omega
  set M := 2 * Q.K ^ 2 with hMdef
  have hup : Q.val M ≤ Tower.F Q.rdepth (M ^ Q.K) := val_le_F_rdepth hM Q
  have hlo : Tower.F P.rdepth M ≤ P.val M := F_rdepth_le_val hM P
  have hthr : M ^ Q.K < 2 ^ M := Tower.threshold hK
  have hstrict : Tower.F Q.rdepth (M ^ Q.K) < Tower.F Q.rdepth (2 ^ M) :=
    Tower.F_strictMono_arg hthr _
  have heq : Tower.F Q.rdepth (2 ^ M) = Tower.F (Q.rdepth + 1) M :=
    (Tower.F_succ_arg Q.rdepth M).symm
  have hmono : Tower.F (Q.rdepth + 1) M ≤ Tower.F P.rdepth M :=
    Tower.F_mono_height hM h
  calc Q.val M ≤ Tower.F Q.rdepth (M ^ Q.K) := hup
    _ < Tower.F Q.rdepth (2 ^ M) := hstrict
    _ = Tower.F (Q.rdepth + 1) M := heq
    _ ≤ Tower.F P.rdepth M := hmono
    _ ≤ P.val M := hlo

/-- Two pointed trees whose holes sit at different right depths are separated at some
assignment, in the direction given by the depths. -/
theorem exists_separating {P Q : PTree} (h : Q.rdepth ≠ P.rdepth) :
    ∃ M : Nat, 2 ≤ M ∧ (Q.val M < P.val M ∨ P.val M < Q.val M) := by
  rcases Nat.lt_or_ge Q.rdepth P.rdepth with hlt | hge
  · refine ⟨2 * Q.K ^ 2, ?_, Or.inl (separation hlt)⟩
    have hK : 1 ≤ Q.K := Q.one_le_K
    have : 1 ≤ Q.K ^ 2 := by
      calc (1:Nat) = 1 ^ 2 := by norm_num
        _ ≤ Q.K ^ 2 := Nat.pow_le_pow_left hK 2
    omega
  · have hlt : P.rdepth < Q.rdepth := by omega
    refine ⟨2 * P.K ^ 2, ?_, Or.inr (separation hlt)⟩
    have hK : 1 ≤ P.K := P.one_le_K
    have : 1 ≤ P.K ^ 2 := by
      calc (1:Nat) = 1 ^ 2 := by norm_num
        _ ≤ P.K ^ 2 := Nat.pow_le_pow_left hK 2
    omega

end PTree
end ChowStanley
