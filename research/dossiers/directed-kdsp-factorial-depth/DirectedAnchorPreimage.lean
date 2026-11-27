import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace DirectedKDSP

variable {D : Type*} [DecidableEq D]

/-- Preimages under bijections can be implemented as images under
the inverse, and therefore retain cardinality. -/
def permPreimage (A : Finset D) (p : Equiv.Perm D) : Finset D :=
  A.map p.symm.toEmbedding

@[simp] theorem mem_permPreimage (A : Finset D) (p : Equiv.Perm D) (x : D) :
    x ∈ permPreimage A p ↔ p x ∈ A := by
  unfold permPreimage
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := Finset.mem_map.mp hx
    change p.symm y=x at he
    rw [← he,p.apply_symm_apply]
    exact hy
  · intro hx
    exact Finset.mem_map.mpr ⟨p x,hx,p.symm_apply_apply x⟩

@[simp] theorem card_permPreimage (A : Finset D) (p : Equiv.Perm D) :
    (permPreimage A p).card = A.card := Finset.card_map _

/-- If the same tokens stand in A at two pref states, the interval
permutation sends positions of A to positions of A and the complement
to the complement. Composition uses Lean's right-to-left convention. -/
theorem interval_preserves_of_same_preimage (A : Finset D) (p q : Equiv.Perm D)
    (same : permPreimage A p = permPreimage A q) :
    ∀ a, (q * p⁻¹) a ∈ A ↔ a ∈ A := by
  intro a
  apply Iff.trans ((mem_permPreimage A q (p.symm a)).symm)
  rw [← same,mem_permPreimage,p.apply_symm_apply]

variable [Fintype D]

def preimageState (A : Finset D) (p : Equiv.Perm D) :
    ((Finset.univ : Finset D).powersetCard A.card) :=
  ⟨permPreimage A p,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,card_permPreimage A p⟩⟩

theorem preimage_state_count (A : Finset D) :
    Fintype.card ↥((Finset.univ : Finset D).powersetCard A.card) =
      Nat.choose (Fintype.card D) A.card := by
  rw [Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ]

/-- With at least choose(k,|A|) events there are two chronological
pref states, and hence a nonempty interval preserving both parts. -/
theorem prefix_interval_preserves (A : Finset D) {n : ℕ}
    (pref : Fin (n+1) → Equiv.Perm D)
    (large : Nat.choose (Fintype.card D) A.card ≤ n) :
    ∃ i j : Fin (n+1), i<j ∧ ∀ x, (pref j * (pref i)⁻¹) x ∈ A ↔ x ∈ A := by
  have K : Fintype.card ↥((Finset.univ : Finset D).powersetCard A.card) <
      Fintype.card (Fin (n+1)) := by
    rw [preimage_state_count,Fintype.card_fin]
    omega
  obtain ⟨i,j,ne,same⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => preimageState A (pref i)) K
  have E := congrArg Subtype.val same
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact ⟨i,j,lt,interval_preserves_of_same_preimage A (pref i) (pref j) E⟩
  · exact ⟨j,i,gt,interval_preserves_of_same_preimage A (pref j) (pref i) E.symm⟩

/-- Apply chronological events from left to right to tokens. Group
composition of permutations is right-to-left, hence the reverse. -/
def prefixPerm (events : List (Equiv.Perm D)) (n : ℕ) : Equiv.Perm D :=
  (events.take n).reverse.prod

def permInterval (events : List (Equiv.Perm D)) (i j : ℕ) : List (Equiv.Perm D) :=
  (events.take j).drop i

theorem interval_product_eq_quotient (events : List (Equiv.Perm D))
    {i j : ℕ} (hij : i ≤ j) :
    (permInterval events i j).reverse.prod = prefixPerm events j * (prefixPerm events i)⁻¹ := by
  have h := List.take_append_drop i (events.take j)
  rw [List.take_take, min_eq_left hij] at h
  have H := congrArg (fun l : List (Equiv.Perm D) => l.reverse.prod) h
  rw [List.reverse_append,List.prod_append] at H
  change (permInterval events i j).reverse.prod * prefixPerm events i = prefixPerm events j at H
  rw [← H,mul_assoc,mul_inv_cancel,mul_one]

/-- A contiguous nonempty sublist, not merely an abstract permutation
quotient, implements a partition-preserving interval. -/
theorem sequence_interval_preserves (A : Finset D) (events : List (Equiv.Perm D))
    (large : Nat.choose (Fintype.card D) A.card ≤ events.length) :
    ∃ i j : ℕ, i<j ∧ j≤events.length ∧
      (permInterval events i j).length=j-i ∧
        ∀ x, ((permInterval events i j).reverse.prod) x∈A ↔ x∈A := by
  obtain ⟨i,j,lt,h⟩ := prefix_interval_preserves A
    (fun r : Fin (events.length+1) => prefixPerm events r.val) large
  have ij : i.val<j.val := lt
  have jn : j.val≤events.length := by omega
  refine ⟨i.val,j.val,ij,jn,?_,?_⟩
  · simp [permInterval,List.length_take,min_eq_left jn]
  · rw [interval_product_eq_quotient _ ij.le]
    exact h

#print axioms interval_product_eq_quotient
#print axioms sequence_interval_preserves
#print axioms interval_preserves_of_same_preimage
#print axioms prefix_interval_preserves
end DirectedKDSP
