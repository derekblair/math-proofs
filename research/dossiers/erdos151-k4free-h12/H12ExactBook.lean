import H12AtlasBounds
import H12MarkedLow

namespace Erdos151H12
open Erdős151.Upper Erdos151CoreHigh Erdos151MarkedLinkTable
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V] (C : V → V → Prop) [DecidableRel C]

def actualHigh (u : V) : Finset V := (neighbors C u).filter (fun v => ambientCodeg C u v=4)
def actualLow (u : V) : Finset V := (neighbors C u).filter (fun v => ambientCodeg C u v=2)

theorem row12_table :
    (∀ k : Fin 7, (edges k).length=12 → k=2 ∨ k=6) ∧
    (∀ k : Fin 7, (edges k).length=12 →
      ((Finset.univ : Finset (Fin 8)).filter (fun v => deg k v=4)).card ≤ 2 ∧
      (((Finset.univ : Finset (Fin 8)).filter (fun v => deg k v=2)).card=0 ∨
       ((Finset.univ : Finset (Fin 8)).filter (fun v => deg k v=2)).card=2)) ∧
    (∀ i : Fin 8, deg 6 i=3) ∧
    (∀ k : Fin 7, (edges k).length=12 →
      ((Finset.univ : Finset (Fin 8)).filter (fun v => deg k v=2)).card=0 → k=6) := by
  decide

theorem row12_chart (w : V)
    (L : NamedLink (neighbors C) (ambientCodeg C) w)
    (hSum : ∑ v∈neighbors C w,row C (neighbors C w) v=24) :
    (edges L.kind).length=12 := by
  have hsum : (∑ v∈neighbors C w,row C (neighbors C w) v) = ∑ i:Fin 8,deg L.kind i := by
    calc
      _ = ∑ v∈Finset.univ.map L.emb,row C (neighbors C w) v := by rw [L.vertices]
      _ = _ := by
        rw [Finset.sum_map]
        exact Finset.sum_congr rfl (fun i _ => (row_core_codeg C w (L.emb i)).trans (L.book i))
  have hc := (atlas_table_link_count L.kind).1
  omega

theorem low_chart_count (u : V) (L : NamedLink (neighbors C) (ambientCodeg C) u) :
    (actualLow C u).card =
      ((Finset.univ : Finset (Fin 8)).filter (fun i => deg L.kind i = 2)).card := by
  unfold actualLow
  rw [←L.vertices,Finset.filter_map,Finset.card_map]
  simp_rw [Function.comp_apply,L.book]

theorem high_chart_count (u : V) (L : NamedLink (neighbors C) (ambientCodeg C) u) :
    (actualHigh C u).card =
      ((Finset.univ : Finset (Fin 8)).filter (fun i => deg L.kind i = 4)).card := by
  unfold actualHigh
  rw [←L.vertices,Finset.filter_map,Finset.card_map]
  simp_rw [Function.comp_apply,L.book]

theorem low_inter_equals_high (u v : V) (L : NamedLink (neighbors C) (ambientCodeg C) u)
    (h12 : (edges L.kind).length=12) (hv : v∈actualLow C u) :
    actualHigh C u = neighbors C u ∩ neighbors C v := by
  have ⟨hvN,hvLo⟩ := Finset.mem_filter.mp hv
  obtain ⟨iv,hi⟩ := NamedLink.get _ _ u L hvN
  have hlo : deg L.kind iv=2 := by rwa [←L.book iv,hi]
  have hkind : L.kind=2 := by
    rcases row12_table.1 L.kind h12 with hh|hh
    · exact hh
    · rw [hh,row12_table.2.2.1] at hlo
      contradiction
  have pivot (j : Fin 8) : L.emb j∈neighbors C v ↔ ambientCodeg C u (L.emb j)=4 := by
    rw [←hi,L.induced,L.book,hkind]
    rw [hkind] at hlo
    exact type2_low_neighbors iv j hlo
  ext x
  constructor
  · intro hx
    have ⟨hxN,hxHi⟩ := Finset.mem_filter.mp hx
    obtain ⟨j,rfl⟩ := NamedLink.get _ _ u L hxN
    exact Finset.mem_inter.mpr ⟨hxN,(pivot j).mpr hxHi⟩
  · intro hx
    obtain ⟨hxU,hxV⟩ := Finset.mem_inter.mp hx
    obtain ⟨j,rfl⟩ := NamedLink.get _ _ u L hxU
    exact Finset.mem_filter.mpr ⟨hxU,(pivot j).mp hxV⟩

/-- Completing the named-atlas step after Seymour equality: every genuine core edge has
exactly three common core neighbors. This eliminates named row #2 on actual graphs. -/
theorem exact_book_after_density
    (sym : ∀ {a b}, C a b → C b a) (irr : ∀ a, ¬C a a)
    (atlas12 : ∀ u, (neighbors C u).Nonempty →
       ∃ L : NamedLink (neighbors C) (ambientCodeg C) u, (edges L.kind).length=12) :
    ∀ u v, C u v → ambientCodeg C u v=3 := by
  have book_comm (u v : V) : ambientCodeg C u v=ambientCodeg C v u := by
    simp [ambientCodeg,Finset.inter_comm]
  have lowSym (u v : V) (hv : v∈actualLow C u) : u∈actualLow C v := by
    have ⟨hn,hb⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨(mem_neighbors C).mpr (sym ((mem_neighbors C).mp hn)),
      (book_comm v u).trans hb⟩
  have noLoop (v : V) : v∉actualLow C v :=
    fun h => irr v ((mem_neighbors C).mp (Finset.mem_filter.mp h).1)
  have counts (u : V) : ((actualLow C u).card=0 ∨ (actualLow C u).card=2) ∧
       (actualHigh C u).card≤2 := by
    by_cases h : (neighbors C u).Nonempty
    · obtain ⟨L,hL⟩ := atlas12 u h
      rw [low_chart_count C u L,high_chart_count C u L]
      exact ⟨(row12_table.2.1 L.kind hL).2,(row12_table.2.1 L.kind hL).1⟩
    · have e := Finset.not_nonempty_iff_eq_empty.mp h
      simp [actualLow,actualHigh,e]
  have trans (u v : V) (hv : v∈actualLow C u) :
      actualHigh C u = neighbors C u ∩ neighbors C v := by
    obtain ⟨L,hL⟩ := atlas12 u ⟨v,(Finset.mem_filter.mp hv).1⟩
    exact low_inter_equals_high C u v L hL hv
  have hHiSym (u v : V) (hv : v∈actualHigh C u) : u∈actualHigh C v := by
    obtain ⟨hn,hb⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨(mem_neighbors C).mpr (sym ((mem_neighbors C).mp hn)),
      (book_comm v u).trans hb⟩
  have hHi (u v : V) (hv : v∈actualLow C u) : (actualHigh C u).Nonempty := by
    have h := (Finset.mem_filter.mp hv).2
    rw [trans u v hv]
    apply Finset.card_pos.mp
    change 0 < ambientCodeg C u v
    omega
  have hTrans (u v : V) (hv : v∈actualLow C u) : actualHigh C u=actualHigh C v := by
    rw [trans u v hv,trans v u (lowSym u v hv),Finset.inter_comm]
  have none := low_classes_empty (actualHigh C) (actualLow C) noLoop (fun u => (counts u).1)
    (fun u => (counts u).2) hHiSym hHi hTrans
  intro u v huv
  obtain ⟨L,hL⟩ := atlas12 u ⟨v,(mem_neighbors C).mpr huv⟩
  have h0 := none u
  rw [low_chart_count C u L] at h0
  have hk := row12_table.2.2.2 L.kind hL h0
  obtain ⟨i,rfl⟩ := NamedLink.get _ _ u L ((mem_neighbors C).mpr huv)
  rw [L.book,hk,row12_table.2.2.1]

#print axioms exact_book_after_density
end Erdos151H12
