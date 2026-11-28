import H12UnifiedRows
import CoreHighElimination

namespace Erdos151H12
open Erdős151.Upper Erdos151MarkedLinkTable Erdos151CoreHigh
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (C : V → V → Prop) [DecidableRel C]

theorem atlas_table_link_count :
    ∀ k : Fin 7, (∑ v : Fin 8, deg k v) = 2*(edges k).length ∧
      10 ≤ (edges k).length ∧ (edges k).length ≤ 12 := by
  decide

theorem named_link_bounds (w : V) (e : Nat)
    (he : ∑ v∈neighbors C w,row C (neighbors C w) v = 2*e)
    (L : NamedLink (neighbors C) (ambientCodeg C) w) :
    (10≤e ∧ e≤12) ∧ (∀ v∈neighbors C w, ambientCodeg C w v≤4) := by
  have hsum : (∑ v∈neighbors C w,row C (neighbors C w) v) = ∑ i:Fin 8,deg L.kind i := by
    calc
      _ = ∑ v∈Finset.univ.map L.emb,row C (neighbors C w) v := by rw [L.vertices]
      _ = _ := by
        rw [Finset.sum_map]
        exact Finset.sum_congr rfl (fun i _ => (row_core_codeg C w (L.emb i)).trans (L.book i))
  have hh := atlas_table_link_count L.kind
  refine ⟨?_,?_⟩
  · omega
  · intro v hv
    obtain ⟨i,rfl⟩ := NamedLink.get _ _ w L hv
    rw [L.book]
    exact (minMax L.kind i).2

variable (G : V → V → Prop) [DecidableRel G]

theorem unified_contributions_from_named_atlas
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (tf : Erdős151.TriangleFreeLinks G)
    (symC : ∀ {a b}, C a b → C b a)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (deg : ∀ v, (neighbors G v).card ≤ 11)
    (minC : ∀ {a b}, C a b → 8 ≤ (neighbors C a).card)
    (upper : ∀ P : Finset V, Erdős151.Free (Erdős151.Forbidden G) (P : Set V) → P.card ≤ 11)
    (lower : ∀ R : Finset V, 41 ≤ R.card →
      ∃ P ⊆ R, 10 ≤ P.card ∧ Erdős151.Free (Erdős151.Forbidden G) (P : Set V))
    (atlas : ∀ w, (neighbors C w).card = 8 → Nonempty (NamedLink (neighbors C) (ambientCodeg C) w))
    (n53 : 53 ≤ Fintype.card V)
    (e : V → Nat) (he : ∀ w, ∑ u∈neighbors C w,row C (neighbors C w) u = 2*e w) :
    ∀ w, 8 ≤ (neighbors C w).card →
      2*e w ≤ 3*(neighbors C w).card ∧
        (9 ≤ (neighbors C w).card → 2*e w < 3*(neighbors C w).card) := by
  have hAtlas (w : V) (hw : (neighbors C w).card = 8) :=
    named_link_bounds C w (e w) (he w) (Classical.choice (atlas w hw))
  have hcap (u v : V) (huv : C u v) (hu : (neighbors C u).card=8) :
      ambientCodeg C u v ≤ 4 :=
    (hAtlas u hu).2 v ((mem_neighbors C).mpr huv)
  intro w hw
  exact unified_vertex_contribution G C sym irr tf symC sub two deg minC upper lower hcap n53
    w hw (e w) (he w) (fun h => (hAtlas w h).1)

#print axioms named_link_bounds
#print axioms unified_contributions_from_named_atlas
end Erdos151H12
