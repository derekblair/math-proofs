import WagnerHallMass
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators
namespace Erdős151.H12.Wagner

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem matching_remaining (A : L → R → Prop) [DecidableRel A]
    (row : ∀ s, (∑ t : R, if A s t then (1:ℕ) else 0) = 3)
    (col : ∀ t, (∑ s : L, if A s t then (1:ℕ) else 0) = 3)
    (P : Finset L) (B : Finset R) (h4 : B.card = 4)
    (onLeft : ∀ s, s∉P → ∀ t∈B, ∀ u∈B, A s t → A s u → t=u)
    (onRight : ∀ t∈B, ∀ s, s∉P → ∀ u, u∉P → A s t → A u t → s=u)
    (small : ∀ S : Finset L, ∀ T : Finset R,
      Disjoint S P → 3 ≤ S.card → cutMass A S T ≤ 5 → mass A S T < S.card + T.card) :
    ∃ f : {s : L // s∉P} → {t : R // t∉B},
      Function.Injective f ∧ ∀ s, A s.1 (f s).1 := by
  classical
  let L0 := {s : L // s∉P}
  let R0 := {t : R // t∉B}
  let ae : L0 ↪ L := ⟨Subtype.val,Subtype.val_injective⟩
  let be : R0 ↪ R := ⟨Subtype.val,Subtype.val_injective⟩
  let N (s : L0) : Finset R0 := Finset.univ.filter (fun t => A s.val t.val)
  have hall (X : Finset L0) : X.card ≤ (X.biUnion N).card := by
    by_contra! h
    let S := X.map ae
    let T := (X.biUnion N).map be
    have hs : S.card = X.card := Finset.card_map ae
    have ht : T.card = (X.biUnion N).card := Finset.card_map be
    have dS : Disjoint S P := Finset.disjoint_left.mpr (by
      intro x hx hxP
      obtain ⟨s,_,rfl⟩ := Finset.mem_map.mp hx
      exact s.property hxP)
    have dT : Disjoint T B := Finset.disjoint_left.mpr (by
      intro x hx hxB
      obtain ⟨s,_,rfl⟩ := Finset.mem_map.mp hx
      exact s.property hxB)
    have dead (s : L) (hs : s∈S) (t : R) (ht : t∉T) (hb : t∉B) : ¬A s t := by
      intro ast
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hs
      apply ht
      refine Finset.mem_map.mpr ⟨⟨t,hb⟩, ?_, rfl⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨a,ha,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ast⟩⟩
    have lmass : mass A S B ≤ S.card :=
      mass_le_card_left A S B (fun s hs => onLeft s (fun k => Finset.disjoint_left.mp dS hs k))
    have rmass : mass A S B ≤ B.card :=
      mass_le_card_right A S B (fun t ht s hs u hu =>
        onRight t ht s (fun k => Finset.disjoint_left.mp dS hs k)
          u (fun k => Finset.disjoint_left.mp dS hu k))
    obtain ⟨p,q,r⟩ := hall_deficit_mass A row col S T B dT
      (by omega) dead (by omega) lmass
    exact (not_lt_of_ge r) (small S T dS p q)
  obtain ⟨f,inj,hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hall
  exact ⟨f,inj,fun s => (Finset.mem_filter.mp (hf s)).2⟩

theorem cubic_bipartite_card_eq (A : L → R → Prop) [DecidableRel A]
    (row : ∀ s, (∑ t : R, if A s t then (1:ℕ) else 0) = 3)
    (col : ∀ t, (∑ s : L, if A s t then (1:ℕ) else 0) = 3) :
    Fintype.card L = Fintype.card R := by
  have hl : mass A Finset.univ Finset.univ = 3*Fintype.card L := by
    simp [mass,row,Nat.mul_comm]
  have hr : mass A Finset.univ Finset.univ = 3*Fintype.card R := by
    rw [transpose]; simp [col,Nat.mul_comm]
  omega

/-- Extend a specified matching on the deleted square nodes, provided
the abstract short-cut condition is satisfied. -/
theorem matching_extends_square (A : L → R → Prop) [DecidableRel A]
    (row : ∀ s, (∑ t : R, if A s t then (1:ℕ) else 0) = 3)
    (col : ∀ t, (∑ s : L, if A s t then (1:ℕ) else 0) = 3)
    (P : Finset L) (B : Finset R) (h4 : B.card = 4)
    (m0 : ↥P ≃ ↥B) (local_mem : ∀ s, A s.val (m0 s).val)
    (onLeft : ∀ s, s∉P → ∀ t∈B, ∀ u∈B, A s t → A s u → t=u)
    (onRight : ∀ t∈B, ∀ s, s∉P → ∀ u, u∉P → A s t → A u t → s=u)
    (small : ∀ S : Finset L, ∀ T : Finset R,
      Disjoint S P → 3 ≤ S.card → cutMass A S T ≤ 5 → mass A S T < S.card + T.card) :
    ∃ m : L ≃ R, (∀ s, A s (m s)) ∧ ∀ s : ↥P, m s.val = (m0 s).val := by
  classical
  obtain ⟨f,inj,adj⟩ := matching_remaining A row col P B h4 onLeft onRight small
  let g (s : L) : R := if h : s∈P then (m0 ⟨s,h⟩).val else (f ⟨s,h⟩).val
  have gP (s : L) (h : s∈P) : g s = (m0 ⟨s,h⟩).val := by simp [g,h]
  have gn (s : L) (h : s∉P) : g s = (f ⟨s,h⟩).val := by simp [g,h]
  have gi : Function.Injective g := by
    intro a b hab
    by_cases ha : a∈P <;> by_cases hb : b∈P
    · rw [gP a ha,gP b hb] at hab
      exact congrArg Subtype.val (m0.injective (Subtype.ext hab))
    · rw [gP a ha,gn b hb] at hab
      exact False.elim ((f ⟨b,hb⟩).property (hab ▸ (m0 ⟨a,ha⟩).property))
    · rw [gn a ha,gP b hb] at hab
      exact False.elim ((f ⟨a,ha⟩).property (hab.symm ▸ (m0 ⟨b,hb⟩).property))
    · rw [gn a ha,gn b hb] at hab
      exact congrArg Subtype.val (inj (Subtype.ext hab))
  have bij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨gi,cubic_bipartite_card_eq A row col⟩
  refine ⟨Equiv.ofBijective g bij,?_,?_⟩
  · intro a
    change A a (g a)
    by_cases h : a∈P
    · rw [gP a h]; exact local_mem ⟨a,h⟩
    · rw [gn a h]; exact adj ⟨a,h⟩
  · intro a
    exact gP a.val a.property

#print axioms matching_extends_square
#print axioms matching_remaining
#print axioms cubic_bipartite_card_eq
end Erdős151.H12.Wagner
