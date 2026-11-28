import UnblockingGraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Erdős151.Upper
open scoped BigOperators
open Finset
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

def nbr (G : V → V → Prop) [DecidableRel G] (u : V) : Finset V :=
  univ.filter (G u)

def row (R : V → V → Prop) [DecidableRel R] (X : Finset V) (u : V) : ℕ :=
  (X.filter (R u)).card

def incidence (R : V → V → Prop) [DecidableRel R] (S X : Finset V) : ℕ :=
  ∑ x ∈ X, (S.filter (fun u => R u x)).card

theorem transpose (R : V → V → Prop) [DecidableRel R] (S X : Finset V) :
    incidence R S X = ∑ u ∈ S, row R X u := by
  simp only [incidence, row, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

def ext (S : Finset V) (w : V) : Finset V := univ \ insert w S

theorem split_cap (S T : Finset V) (hTS : T ⊆ S) (f : V → ℕ) (a b : ℕ)
    (ha : ∀ u ∈ T, f u ≤ a) (hb : ∀ u ∈ S, f u ≤ b) :
    (∑ u ∈ S, f u) ≤ T.card * a + (S.card - T.card) * b := by
  rw [← sum_sdiff hTS (f := f), add_comm]
  apply Nat.add_le_add
  · simpa using (sum_le_sum ha : (∑ u ∈ T, f u) ≤ ∑ _u ∈ T, a)
  · have h := sum_le_sum (fun u (hu : u ∈ S \ T) => hb u (mem_sdiff.mp hu).1)
    simpa [card_sdiff_of_subset hTS] using h

theorem row_degree (G : V → V → Prop) [DecidableRel G]
    (sym : ∀ {u v}, G u v → G v u) (w : V) (u : V)
    (hu : u ∈ nbr G w) (hw : w ∉ nbr G w) :
    row G (ext (nbr G w) w) u + row G (nbr G w) u + 1 = (nbr G u).card := by
  have huw : G u w := sym (mem_filter.mp hu).2
  have hsplit : (ext (nbr G w) w).filter (G u) ∪
      insert w ((nbr G w).filter (G u)) = nbr G u := by
    ext z
    by_cases hzw : z = w
    · subst z
      simp [nbr, huw]
    · by_cases hz : G w z <;> simp [ext, hzw, hz, nbr]
  have hd : Disjoint ((ext (nbr G w) w).filter (G u))
      (insert w ((nbr G w).filter (G u))) := by
    rw [disjoint_left]
    intro z h1 h2
    exact (mem_sdiff.mp (mem_filter.mp h1).1).2
      (by rcases mem_insert.mp h2 with rfl|hz
          · exact mem_insert_self _ _
          · exact mem_insert_of_mem ((mem_filter.mp hz).1))
  have hc := card_union_of_disjoint hd
  rw [hsplit, card_insert_of_notMem (fun hm => hw (mem_filter.mp hm).1)] at hc
  simpa [row, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc.symm

theorem internal_lower (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]
    (sub : ∀ {u v}, C u v → G u v) (w : V)
    (book : ∀ u ∈ nbr C w, 2 ≤ ((nbr C w).filter (C u)).card) :
    2 * (nbr C w).card ≤ ∑ u ∈ nbr G w, row G (nbr G w) u := by
  have hsub : nbr C w ⊆ nbr G w := fun u hu =>
    mem_filter.mpr ⟨mem_univ u, sub (mem_filter.mp hu).2⟩
  have hrow : ∀ u ∈ nbr C w, 2 ≤ row G (nbr G w) u := by
    intro u hu
    apply (book u hu).trans (card_le_card ?_)
    intro z hz
    exact mem_filter.mpr ⟨hsub (mem_filter.mp hz).1, sub (mem_filter.mp hz).2⟩
  calc
    2 * (nbr C w).card = ∑ _u ∈ nbr C w, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ nbr C w, row G (nbr G w) u := sum_le_sum hrow
    _ ≤ ∑ u ∈ nbr G w, row G (nbr G w) u :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; omega)

theorem edge_budget (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]
    (sym : ∀ {u v}, G u v → G v u) (sub : ∀ {u v}, C u v → G u v)
    (w : V) (loop : ¬ G w w) (cap : ℕ)
    (deg : ∀ u ∈ nbr G w, (nbr G u).card ≤ 10)
    (coreDeg : ∀ u ∈ nbr C w, (nbr G u).card ≤ cap)
    (book : ∀ u ∈ nbr C w, 2 ≤ ((nbr C w).filter (C u)).card) :
    incidence G (nbr G w) (ext (nbr G w) w) + (nbr G w).card + 2 * (nbr C w).card
      ≤ (nbr C w).card * cap + ((nbr G w).card - (nbr C w).card) * 10 := by
  have hsub : nbr C w ⊆ nbr G w := fun u hu =>
    mem_filter.mpr ⟨mem_univ u, sub (mem_filter.mp hu).2⟩
  have h := split_cap (nbr G w) (nbr C w) hsub (fun u => (nbr G u).card) cap 10 coreDeg deg
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

theorem lone_budget (G C : V → V → Prop)
    [DecidableRel G] [DecidableRel C] [DecidableRel (Lone G)]
    (sym : ∀ {u v}, G u v → G v u) (sub : ∀ {u v}, C u v → G u v)
    (w : V) (loop : ¬ G w w) (cap : ℕ)
    (deg : ∀ u ∈ nbr G w, (nbr G u).card ≤ 10)
    (coreDeg : ∀ u ∈ nbr C w, (nbr G u).card ≤ cap)
    (coreMin : ∀ u ∈ nbr C w, 8 ≤ (nbr C u).card)
    (coreNotLone : ∀ {u v}, C u v → ¬ Lone G u v) :
    incidence (Lone G) (nbr G w) (ext (nbr G w) w)
      ≤ (nbr C w).card * (cap - 8) + ((nbr G w).card - (nbr C w).card) * 9 := by
  have hsub : nbr C w ⊆ nbr G w := fun u hu =>
    mem_filter.mpr ⟨mem_univ u, sub (mem_filter.mp hu).2⟩
  have hw : w ∉ nbr G w := by simpa [nbr] using loop
  have hrow : ∀ u ∈ nbr G w, row (Lone G) (ext (nbr G w) w) u ≤ 9 := by
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

/-- Two core witnesses for each oriented core edge imply that none of those
edges is lone in the host. -/
theorem core_not_lone (G C : V → V → Prop) [DecidableRel C]
    (sub : ∀ {u v}, C u v → G u v)
    (book : ∀ u, ∀ v ∈ nbr C u, 2 ≤ ((nbr C u).filter (C v)).card)
    {u v : V} (huv : C u v) : ¬ Lone G u v := by
  intro hl
  have hc := book u v (mem_filter.mpr ⟨mem_univ v,huv⟩)
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < ((nbr C u).filter (C v)).card by omega)
  exact hl.2 x ⟨sub (mem_filter.mp (mem_filter.mp hx).1).2, sub (mem_filter.mp hx).2⟩

#print axioms edge_budget
#print axioms lone_budget
#print axioms core_not_lone

section Stages

variable (G C : V → V → Prop)
    [DecidableRel G] [DecidableRel C] [DecidableRel (Lone G)]
    (sym : ∀ {u v}, G u v → G v u) (sub : ∀ {u v}, C u v → G u v)
    (w : V) (loop : ¬ G w w)
    (deg : ∀ u ∈ nbr G w, (nbr G u).card ≤ 10)
    (coreMin : ∀ u ∈ nbr C w, 8 ≤ (nbr C u).card)
    (book : ∀ u, ∀ v ∈ nbr C u, 2 ≤ ((nbr C u).filter (C v)).card)

include sym sub loop deg coreMin book in
theorem stage_ten (h : (nbr G w).card = 10) :
    incidence G (nbr G w) (ext (nbr G w) w) + 2 * (nbr C w).card ≤ 90 ∧
    incidence (Lone G) (nbr G w) (ext (nbr G w) w) + 7 * (nbr C w).card ≤ 90 := by
  have hsub : nbr C w ⊆ nbr G w := fun u hu =>
    mem_filter.mpr ⟨mem_univ u, sub (mem_filter.mp hu).2⟩
  have hr := card_le_card hsub
  have hc : ∀ u ∈ nbr C w, (nbr G u).card ≤ 10 := fun u hu => deg u (hsub hu)
  have he := edge_budget G C sym sub w loop 10 deg hc (book w)
  have hl := lone_budget G C sym sub w loop 10 deg hc coreMin
    (fun h => core_not_lone G C sub book h)
  omega

include sym sub loop deg coreMin book in
theorem stage_nine (h : (nbr G w).card = 9)
    (hc : ∀ u ∈ nbr C w, (nbr G u).card ≤ 9) :
    incidence G (nbr G w) (ext (nbr G w) w) + 3 * (nbr C w).card ≤ 81 ∧
    incidence (Lone G) (nbr G w) (ext (nbr G w) w) + 8 * (nbr C w).card ≤ 81 := by
  have hsub : nbr C w ⊆ nbr G w := fun u hu =>
    mem_filter.mpr ⟨mem_univ u, sub (mem_filter.mp hu).2⟩
  have hr := card_le_card hsub
  have he := edge_budget G C sym sub w loop 9 deg hc (book w)
  have hl := lone_budget G C sym sub w loop 9 deg hc coreMin
    (fun h => core_not_lone G C sub book h)
  omega

include sym sub loop deg coreMin book in
theorem stage_eight (h : (nbr G w).card = 8) (hr0 : 8 ≤ (nbr C w).card)
    (hc : ∀ u ∈ nbr C w, (nbr G u).card ≤ 8) :
    incidence G (nbr G w) (ext (nbr G w) w) ≤ 40 ∧
    incidence (Lone G) (nbr G w) (ext (nbr G w) w) = 0 := by
  have hsub : nbr C w ⊆ nbr G w := fun u hu =>
    mem_filter.mpr ⟨mem_univ u, sub (mem_filter.mp hu).2⟩
  have hr := card_le_card hsub
  have he := edge_budget G C sym sub w loop 8 deg hc (book w)
  have hl := lone_budget G C sym sub w loop 8 deg hc coreMin
    (fun h => core_not_lone G C sub book h)
  omega

end Stages
#print axioms stage_ten
#print axioms stage_nine
#print axioms stage_eight
end Erdős151.Upper
