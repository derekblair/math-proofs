import N62OwnerPressure

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V] (G C : V→V→Prop)
variable [DecidableRel G] [DecidableRel C]

/-- Strengthened actual ambient d12, core r10 degree row at order≥62.
The e=17 saturation case is impossible by marked-owner triangle forcing. -/
theorem degreeTwelve_r10_at_least62
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (deg : ∀ v, (neighbors G v).card≤12)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (hn : 62≤Fintype.card V) (w : V) (s12 : (neighbors G w).card=12)
    (t10 : (neighbors C w).card=10)
    (cmin : ∀ u∈neighbors C w, 8≤(neighbors C u).card)
    (e : Nat) (he : ∑ u∈neighbors C w,row C (neighbors C w) u=2*e) : e≤16 := by
  classical
  let S := neighbors G w
  let X := ext S w
  let I := ∑ x∈X,ncol G S x
  let L := ∑ x∈X,lcol G S x
  let P := (specialCols G S X).card
  have hf : Free (Forbidden G) (S : Set V) := by
    convert neighborhood_free G sym tf w using 1
    ext x
    exact mem_neighbors G
  have dx : Disjoint X S := Finset.disjoint_left.mpr (fun x hx h => (Finset.mem_sdiff.mp hx).2
    (Finset.mem_insert_of_mem h))
  have cX : 49≤X.card := by
    have hw : w∉S := fun h => irr w ((mem_neighbors G).mp h)
    change 49≤((Finset.univ : Finset V)\insert w S).card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_insert_of_notMem hw]
    change S.card=12 at s12
    omega
  have lo := degreeTwelve_lower_incidence_h13 G S X sym irr tf s12 hf dx upper
  have sp := degreeTwelve_special_cost_h13 G S X sym irr tf s12 hf dx upper
  obtain ⟨hi,hl⟩ := degreeTwelve_upper_slots_h13 G C sym irr sub two deg w s12 cmin e he
  change 3*X.card≤I+12+P at lo
  change 2*P≤L+12 at sp
  change I+2*e≤132 at hi
  change L+7*(neighbors C w).card≤132 at hl
  rw [t10] at hl
  have hle : e≤17 := by omega
  by_contra! hh
  have eq : e=17 := by omega
  rw [eq] at he
  apply frame_impossible G (frame_of_saturated G C w sym irr tf sub two deg upper hn s12 t10 cmin he)
    sym irr dx s12 hf upper deg

#print axioms degreeTwelve_r10_at_least62
end Erdos151N62
