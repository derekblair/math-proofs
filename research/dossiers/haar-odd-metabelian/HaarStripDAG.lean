import Mathlib.Algebra.Group.Basic
import HaarStripVoltage
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi

namespace HaarStripDAG
open HaarStripVoltage

structure Expr where
  power : Nat
  coeff : List ℤ
deriving Inhabited

structure Branch where
  diff : V
  child : Nat
  proofs : List Expr
deriving Inhabited

structure Node where
  rels : List V
  word : List P
  closing : Expr
  branches : List Branch
deriving Inhabited

def linear : List V → List ℤ → V
  | r::rs, c::cs => c • r + linear rs cs
  | _, _ => 0

def exprOK (rs : List V) (r : V) (w : Expr) : Prop :=
  (2^w.power : ℕ) • r = linear rs w.coeff

instance (rs : List V) (r : V) (w : Expr) : Decidable (exprOK rs r w) :=
  inferInstanceAs (Decidable (_ = _))

def wordsOK (n : Node) : Prop := n.word.length ∈ [4,8,16,32]
instance (n : Node) : Decidable (wordsOK n) := inferInstanceAs (Decidable (_ ∈ _))

def difAt (n : Node) (i j : Fin n.word.length) : V :=
  ((rows start n.word)[i.val]'(by simpa using i.isLt)).2 -
    ((rows start n.word)[j.val]'(by simpa using j.isLt)).2

def Match (n : Node) (i j : Fin n.word.length) (b : Branch) : Prop :=
  difAt n i j = b.diff ∨ difAt n i j = -b.diff
instance (n : Node) (i j : Fin n.word.length) (b : Branch) : Decidable (Match n i j b) :=
  inferInstanceAs (Decidable (_ ∨ _))

def baseAt (n : Node) (i : Fin n.word.length) : B :=
  ((rows start n.word)[i.val]'(by simpa using i.isLt)).1

def pairOK (n : Node) (i j : Fin n.word.length) : Prop :=
  i.val < j.val → baseAt n i = baseAt n j → ∃ b : Fin n.branches.length, Match n i j n.branches[b]
instance (n : Node) (i j : Fin n.word.length) : Decidable (pairOK n i j) :=
  inferInstanceAs (Decidable (_ → _ → _))

def edgeOK (D : Nat → Node) (i : Nat) (b : Branch) : Prop :=
  b.child<i ∧ ∀ j : Fin (D b.child).rels.length,
    exprOK ((D i).rels ++ [b.diff]) (D b.child).rels[j] b.proofs[j.val]!
instance (D : Nat → Node) (i : Nat) (b : Branch) : Decidable (edgeOK D i b) :=
  inferInstanceAs (Decidable (_ ∧ _))

def valid (D : Nat → Node) (i : Nat) : Prop :=
  let n := D i
  wordsOK n ∧
  (finish start n.word).1 = start.1 ∧
  exprOK n.rels (finish start n.word).2 n.closing ∧
  (∀ ii jj : Fin n.word.length, pairOK n ii jj) ∧
  ∀ j : Fin n.branches.length, edgeOK D i n.branches[j]
instance (D : Nat → Node) (i : Nat) : Decidable (valid D i) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {A : Type*} [AddCommGroup A]

def Vanish (φ : V →+ A) (rs : List V) : Prop := ∀ r ∈ rs, φ r = 0

theorem map_linear (φ : V →+ A) (rs : List V) (cs : List ℤ)
    (H : Vanish φ rs) : φ (linear rs cs) = 0 := by
  induction rs generalizing cs with
  | nil => simp [linear]
  | cons r rs ih =>
    cases cs with
    | nil => simp [linear]
    | cons c cs =>
      have h : φ r=0 := H r (by simp)
      simp [linear,h,zsmul_zero,ih cs (fun b hb => H b (by simp [hb]))]

theorem dyad_zero (noTwo : ∀ a : A, a+a=0 → a=0) (k : ℕ) (a : A)
    (h : (2^k : ℕ) • a=0) : a=0 := by
  induction k with
  | zero => simpa only [pow_zero,one_nsmul] using h
  | succ k ih =>
    apply ih
    apply noTwo
    simpa [pow_succ, mul_nsmul,two_nsmul, nsmul_add, Nat.mul_comm] using h

theorem expr_sound (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0)
    (rs : List V) (r : V) (w : Expr) (h : exprOK rs r w) (H : Vanish φ rs) :
    φ r=0 := by
  apply dyad_zero noTwo w.power
  have e := congrArg φ h
  rw [map_nsmul, map_linear φ rs w.coeff H] at e
  exact e

theorem dag_sound (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0)
    (D : Nat → Node) (root : Nat) (allValid : ∀ i ≤ root, valid D i)
    (hroot : (D root).rels=[]) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n := by
  suffices H : ∀ i ≤ root, Vanish φ (D i).rels → ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n by
    apply H root (by rfl)
    simp [Vanish,hroot]
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi H
    rcases allValid i hi with ⟨length, endBase, close, pairs, edges⟩
    by_cases bad : ∃ j : Fin (D i).branches.length, φ ((D i).branches[j]).diff=0
    · obtain ⟨j,hj⟩ := bad
      let b := (D i).branches[j]
      have E : edgeOK D i b := edges j
      apply ih b.child E.1 (Nat.le_trans (Nat.le_of_lt E.1) hi)
      intro r hr
      obtain ⟨k,hk⟩ := List.mem_iff_get.mp hr
      rw [← hk]
      apply expr_sound φ noTwo ((D i).rels ++ [b.diff]) _ _ (E.2 k)
      intro a ha
      rcases List.mem_append.mp ha with ha|ha
      · exact H a ha
      · rcases List.mem_singleton.mp ha with rfl
        exact hj
    · refine ⟨(D i).word.length,length,from_rows φ (D i).word ?_ ?_ ?_⟩
      · simp [wordsOK] at length
        omega
      · apply Prod.ext
        · exact endBase
        · simpa [lift,start] using expr_sound φ noTwo _ _ _ close H
      · intro j k hjk eq
        have bb : baseAt (D i) j = baseAt (D i) k := (congrArg (fun a : B × A => a.1) eq)
        obtain ⟨l,hl⟩ := pairs j k hjk bb
        apply bad
        refine ⟨l,?_⟩
        have d : φ (difAt (D i) j k)=0 := by
          unfold difAt
          rw [map_sub,sub_eq_zero]
          exact congrArg Prod.snd eq
        rcases hl with h|h
        · rwa [h] at d
        · rwa [h,map_neg,neg_eq_zero] at d
end HaarStripDAG
