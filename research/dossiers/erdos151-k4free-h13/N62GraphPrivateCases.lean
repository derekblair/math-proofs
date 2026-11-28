import N62PrivateSums
import N62TenAmbientRigidity

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G C : V→V→Prop) [DecidableRel G] [DecidableRel C]

/-- The exact six cases are constraints on actual block counts of the
graph, rather than abstract feasible parameters. -/
theorem e16_actual_private_cases
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (deg : ∀ v, (neighbors G v).card≤12)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (hn : 62≤Fintype.card V) (w : V) (s12 : (neighbors G w).card=12)
    (t10 : (neighbors C w).card=10)
    (hmin : ∀ u∈neighbors C w, 8≤(neighbors C u).card)
    (h16 : ∑ u∈neighbors C w,row C (neighbors C w) u = 32) :
    let S := neighbors G w
    let X := ext S w
    let a := acnt G S X
    let b := bcnt G S X
    let c := ccnt G S X
    let d := dcnt G S X
    let l := ∑ x∈X,lcol G S x
    (a=8 ∧ d=27 ∧ b=4 ∧ c=0 ∧ l=62) ∨
    (a=9 ∧ d=26 ∧ b+c=3 ∧ c≤1) ∨
    (a=10 ∧ d=26 ∧ 1≤b ∧ c=0 ∧ l=62) ∨
    (a=10 ∧ d=25 ∧ b+c=2) ∨
    (a=11 ∧ 24≤d) ∨ (a=12 ∧ 23≤d) := by
  classical
  let S := neighbors G w
  let X := ext S w
  let I := ∑ x∈X,ncol G S x
  let L := ∑ x∈X,lcol G S x
  have hw : w∉S := fun h => irr w ((mem_neighbors G).mp h)
  have x49 : 49≤X.card := by
    change 49≤((Finset.univ : Finset V) \ insert w S).card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_insert_of_notMem hw]
    change S.card=12 at s12
    omega
  have hS : Free (Forbidden G) (S : Set V) := by
    convert neighborhood_free G sym tf w using 1
    ext x
    exact mem_neighbors G
  have dis : Disjoint X S := Finset.disjoint_left.mpr (fun x hx hs =>
    (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hs))
  have blocked (x : V) (hx : x∈X) := all_exterior_blocked_12 G S s12 upper x
    (Finset.disjoint_left.mp dis hx)
  obtain ⟨lo,pr⟩ := degreeTwelve_exact_private_incidence G S X sym irr tf s12 hS dis upper
  obtain ⟨hi,hl⟩ := degreeTwelve_upper_slots_h13 G C sym irr sub two deg w s12 hmin 16
    (by simpa only using h16)
  have loL := exact_lone_column_lower G S X sym irr hS blocked
  obtain ⟨p,q⟩ := exact_private_special_counts G S X
  rw [p,q] at lo
  rw [p] at pr
  change I+32≤132 at hi
  change L+7*(neighbors C w).card≤132 at hl
  rw [t10] at hl
  have demand : 147≤I+acnt G S X+bcnt G S X+ccnt G S X+(acnt G S X+dcnt G S X) := by
    change 3*X.card ≤ I + (acnt G S X+bcnt G S X+ccnt G S X) + (acnt G S X+dcnt G S X) at lo
    omega
  have loL' : acnt G S X+2*dcnt G S X+ccnt G S X≤L := by
    change acnt G S X+ccnt G S X+2*dcnt G S X≤L at loL
    omega
  exact tight16_private_cases (acnt G S X) (bcnt G S X) (ccnt G S X) (dcnt G S X)
    I L demand pr (by omega) loL' (by omega)

#print axioms e16_actual_private_cases
end Erdos151N62
