import H12ExactBook
import NineLinkPivot

open scoped BigOperators
namespace H13MixedComponents
open Erdos151H12 Erdős151.Upper Erdos151CoreHigh Erdos151MarkedLinkTable Finset
variable {V : Type*} [DecidableEq V] [Fintype V] (C : V→V→Prop) [DecidableRel C]

/-- The type-2 exclusion does not require every vertex to use the
8-link atlas: any additional cubic links have no low or high vertex. -/
theorem neutral_eight_is_wagner
    (sym : ∀ {a b}, C a b → C b a) (irr : ∀ a, ¬ C a a)
    (shapes : ∀ u, (neighbors C u).Nonempty →
      (∃ L : NamedLink (neighbors C) (ambientCodeg C) u, (edges L.kind).length=12) ∨
      (∀ v∈neighbors C u, ambientCodeg C u v=3)) :
    ∀ u (L : NamedLink (neighbors C) (ambientCodeg C) u),
      (edges L.kind).length=12 → L.kind=6 := by
  have book_comm (u v : V) : ambientCodeg C u v=ambientCodeg C v u := by
    simp [ambientCodeg,Finset.inter_comm]
  have lowSym (u v : V) (hv : v∈actualLow C u) : u∈actualLow C v := by
    have ⟨hn,hb⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨(mem_neighbors C).mpr (sym ((mem_neighbors C).mp hn)),
      (book_comm v u).trans hb⟩
  have noLoop (v : V) : v∉actualLow C v :=
    fun h => irr v ((mem_neighbors C).mp (mem_filter.mp h).1)
  have cubic_counts (u : V) (h : ∀ v∈neighbors C u, ambientCodeg C u v=3) :
      actualLow C u = ∅ ∧ actualHigh C u = ∅ := by
    constructor
    · apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hh := h v (mem_filter.mp hv).1
      have hz := (mem_filter.mp hv).2
      change ambientCodeg C u v=2 at hz
      omega
    · apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hh := h v (mem_filter.mp hv).1
      have hz := (mem_filter.mp hv).2
      change ambientCodeg C u v=4 at hz
      omega
  have counts (u : V) : ((actualLow C u).card=0 ∨ (actualLow C u).card=2) ∧
      (actualHigh C u).card≤2 := by
    by_cases h : (neighbors C u).Nonempty
    · rcases shapes u h with ⟨L,hL⟩|hc
      · rw [low_chart_count C u L,high_chart_count C u L]
        exact ⟨(row12_table.2.1 L.kind hL).2,(row12_table.2.1 L.kind hL).1⟩
      · obtain ⟨hlo,hhi⟩ := cubic_counts u hc
        simp [hlo,hhi]
    · have e := Finset.not_nonempty_iff_eq_empty.mp h
      simp [actualLow,actualHigh,e]
  have trans (u v : V) (hv : v∈actualLow C u) :
      actualHigh C u = neighbors C u ∩ neighbors C v := by
    rcases shapes u ⟨v,(mem_filter.mp hv).1⟩ with ⟨L,hL⟩|hc
    · exact low_inter_equals_high C u v L hL hv
    · rw [(cubic_counts u hc).1] at hv
      exact (notMem_empty _ hv).elim
  have hHiSym (u v : V) (hv : v∈actualHigh C u) : u∈actualHigh C v := by
    obtain ⟨hn,hb⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨(mem_neighbors C).mpr (sym ((mem_neighbors C).mp hn)),
      (book_comm v u).trans hb⟩
  have hHi (u v : V) (hv : v∈actualLow C u) : (actualHigh C u).Nonempty := by
    have h := (mem_filter.mp hv).2
    rw [trans u v hv]
    apply card_pos.mp
    change 0 < ambientCodeg C u v
    omega
  have hTrans (u v : V) (hv : v∈actualLow C u) : actualHigh C u=actualHigh C v := by
    rw [trans u v hv,trans v u (lowSym u v hv),Finset.inter_comm]
  have none := low_classes_empty (actualHigh C) (actualLow C) noLoop (fun u => (counts u).1)
    (fun u => (counts u).2) hHiSym hHi hTrans
  intro u L hL
  have h0 := none u
  rw [low_chart_count C u L] at h0
  exact row12_table.2.2.2 L.kind hL h0

#print axioms neutral_eight_is_wagner
end H13MixedComponents
