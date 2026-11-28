import UpperIncidence
open scoped BigOperators
namespace Erdős151.H10
open Erdős151.Upper Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem edge_budget_h10 (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]
    (sym : ∀ {u v}, G u v → G v u) (sub : ∀ {u v}, C u v → G u v)
    (w : V) (loop : ¬ G w w) (cap : ℕ)
    (deg : ∀ u ∈ nbr G w, (nbr G u).card ≤ 9)
    (coreDeg : ∀ u ∈ nbr C w, (nbr G u).card ≤ cap)
    (book : ∀ u ∈ nbr C w, 2 ≤ ((nbr C w).filter (C u)).card) :
    incidence G (nbr G w) (ext (nbr G w) w) + (nbr G w).card + 2 * (nbr C w).card
      ≤ (nbr C w).card * cap + ((nbr G w).card - (nbr C w).card) * 9 := by
  have hsub : nbr C w ⊆ nbr G w := fun u hu =>
    mem_filter.mpr ⟨mem_univ u, sub (mem_filter.mp hu).2⟩
  have h := split_cap (nbr G w) (nbr C w) hsub (fun u => (nbr G u).card) cap 9 coreDeg deg
  have hi := internal_lower G C sub w book
  have hw : w ∉ nbr G w := by simpa [nbr] using loop
  have hs : (∑ u ∈ nbr G w, (nbr G u).card) =
      (∑ u ∈ nbr G w, row G (ext (nbr G w) w) u) +
      (∑ u ∈ nbr G w, row G (nbr G w) u) + (nbr G w).card := by
    rw [← sum_add_distrib, show (nbr G w).card = ∑ _u ∈ nbr G w, 1 by simp,
      ← sum_add_distrib]
    exact sum_congr rfl (fun u hu => (row_degree G sym w u hu hw).symm)
  rw [hs] at h
  rw [transpose]
  omega

theorem lone_budget_h10 (G C : V → V → Prop)
    [DecidableRel G] [DecidableRel C] [DecidableRel (Lone G)]
    (sym : ∀ {u v}, G u v → G v u) (sub : ∀ {u v}, C u v → G u v)
    (w : V) (loop : ¬ G w w) (cap : ℕ)
    (deg : ∀ u ∈ nbr G w, (nbr G u).card ≤ 9)
    (coreDeg : ∀ u ∈ nbr C w, (nbr G u).card ≤ cap)
    (coreMin : ∀ u ∈ nbr C w, 8 ≤ (nbr C u).card)
    (coreNotLone : ∀ {u v}, C u v → ¬ Lone G u v) :
    incidence (Lone G) (nbr G w) (ext (nbr G w) w)
      ≤ (nbr C w).card * (cap - 8) + ((nbr G w).card - (nbr C w).card) * 8 := by
  have hsub : nbr C w ⊆ nbr G w := fun u hu =>
    mem_filter.mpr ⟨mem_univ u, sub (mem_filter.mp hu).2⟩
  have hw : w ∉ nbr G w := by simpa [nbr] using loop
  have hrow : ∀ u ∈ nbr G w, row (Lone G) (ext (nbr G w) w) u ≤ 8 := by
    intro u hu
    have hle : row (Lone G) (ext (nbr G w) w) u ≤ row G (ext (nbr G w) w) u :=
      card_le_card (fun v hv => mem_filter.mpr ⟨(mem_filter.mp hv).1,(mem_filter.mp hv).2.1⟩)
    have hd := row_degree G sym w u hu hw
    have hmax := deg u hu
    omega
  have hcore : ∀ u ∈ nbr C w, row (Lone G) (ext (nbr G w) w) u ≤ cap - 8 := by
    intro u hu
    let A := (ext (nbr G w) w).filter (Lone G u)
    have hd : Disjoint A (nbr C u) := by
      rw [disjoint_left]
      intro v hv hcv
      exact coreNotLone (mem_filter.mp hcv).2 (mem_filter.mp hv).2
    have hcap : (A ∪ nbr C u).card ≤ (nbr G u).card := by
      apply card_le_card
      intro v hv
      rcases mem_union.mp hv with hl|hc
      · exact mem_filter.mpr ⟨mem_univ v,(mem_filter.mp hl).2.1⟩
      · exact mem_filter.mpr ⟨mem_univ v,sub (mem_filter.mp hc).2⟩
    rw [card_union_of_disjoint hd] at hcap
    have hmin := coreMin u hu
    have hmax := coreDeg u hu
    change A.card ≤ cap - 8
    omega
  rw [transpose]
  exact split_cap _ _ hsub _ _ _ hcore hrow


#print axioms edge_budget_h10
#print axioms lone_budget_h10
end Erdős151.H10
