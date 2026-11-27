import FamilyPrefix
import ColorCore
import Mathlib.Data.Finset.Basic

namespace IU
def mask (A : Finset Nat) : Nat → Nat
  | 0 => 0
  | n+1 => if n ∈ A then mask A n ||| 2^n else mask A n

theorem bits (A : Finset Nat) (n i : Nat) :
    (mask A n).testBit i = decide (i<n ∧ i∈A) := by
  induction n with
  | zero => simp [mask]
  | succ n ih =>
    by_cases H : n∈A
    · rw [mask,if_pos H,Nat.testBit_or,ih,Nat.testBit_two_pow]
      by_cases e : i=n
      · subst i
        simp [H]
      · have nn : n≠i := Ne.symm e
        have eq : i<n+1 ↔ i<n := by omega
        simp [nn,eq]
    · rw [mask,if_neg H,ih]
      by_cases e : i=n
      · subst i
        simp [H]
      · have eq : i<n+1 ↔ i<n := by omega
        simp [eq]

theorem mask_lt (A : Finset Nat) (n : Nat) : mask A n<2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro i h
  rw [bits]
  simp [show ¬i<n by omega]

theorem mask_inj {A B : Finset Nat} {n : Nat} (a : A⊆Finset.range n)
    (b : B⊆Finset.range n) (eq : mask A n=mask B n) : A=B := by
  ext i
  have E := congrArg (fun x => x.testBit i) eq
  rw [bits,bits] at E
  by_cases h : i<n
  · simpa [h] using E
  · have an : i∉A := fun u => h (Finset.mem_range.mp (a u))
    have bn : i∉B := fun u => h (Finset.mem_range.mp (b u))
    simp [an,bn]

theorem rank_mask (A : Finset Nat) {n t : Nat} (h : t≤n) : rank (mask A n) t=pr A t := by
  let R := (List.range t).filter (fun i => (mask A n).testBit i)
  have cardR : R.toFinset.card=R.length := List.toFinset_card_of_nodup
    (List.Nodup.filter _ List.nodup_range)
  have E : R.toFinset=below A t := by
    ext i
    simp only [R,List.mem_toFinset,List.mem_filter,List.mem_range,bits,decide_eq_true_eq,
      Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.2.2,h.1⟩
    · intro h
      exact ⟨h.2,by omega,h.1⟩
  change R.length = (below A t).card
  rw [←cardR,E]

theorem rank_full {A : Finset Nat} {n : Nat} (h : A⊆Finset.range n) :
    rank (mask A n) n=A.card := by
  rw [rank_mask A le_rfl]
  change (A.filter (·<n)).card=_
  rw [Finset.filter_true_of_mem fun x hx => Finset.mem_range.mp (h hx)]

theorem image_in_prefix_graph {F : Finset (Finset Nat)} {n p q : Nat}
    (hp : 0<p) (V : IsIU F n p q) (closed : ClosedUnderPrefix F n) :
    let G := F.image (fun A => mask A n)
    G.card=F.card ∧ (∀ a∈G, a∈admissible n p q) ∧
      (∀ a∈G, ∀ b∈G, a≠b → edge n p q a b=true) := by
  classical
  have good (A B : Finset Nat) (a : A∈F) (b : B∈F) : edge n p q (mask A n) (mask B n)=true := by
    obtain ⟨t,tn,Z⟩ := prefix_compatible hp V closed a b
    unfold edge
    rw [List.any_eq_true]
    refine ⟨t,List.mem_range.mpr (by omega),?_⟩
    rw [decide_eq_true_eq,rank_full (V.1 A a),rank_full (V.1 B b),rank_mask A tn,rank_mask B tn]
    exact Z
  refine ⟨Finset.card_image_of_injOn (fun A a B b e => mask_inj (V.1 A a) (V.1 B b) e),?_,?_⟩
  · intro a ha
    obtain ⟨A,aF,rfl⟩ := Finset.mem_image.mp ha
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (mask_lt A n),?_⟩
    obtain ⟨l,r⟩ := V.2 A aF A aF
    simp only [Finset.inter_self,Finset.union_self] at l r
    simp [vertex,rank_full (V.1 A aF),l,r,good A A aF aF]
  · intro a ha b hb _
    obtain ⟨A,aF,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨B,bF,rfl⟩ := Finset.mem_image.mp hb
    exact good A B aF bF

#print axioms image_in_prefix_graph
end IU
