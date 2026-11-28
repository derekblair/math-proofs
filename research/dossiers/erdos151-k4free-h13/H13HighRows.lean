import H13HighUpper
import H13UnblockedCounts
import H13DegreeElevenCounts
import H13DegreeTwelveSpecial

namespace Erdos151H12
open Erdős151 Erdős151.Upper
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V] (G C : V → V → Prop)
variable [DecidableRel G] [DecidableRel C]

/-- Weighted private-owner deficit at ambient degree eleven. -/
theorem degreeEleven_at_least64_h13
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (tf : TriangleFreeLinks G)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (degree : ∀ v, (neighbors G v).card ≤ 12)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12)
    (hn : 64 ≤ Fintype.card V)
    (w : V) (h10 : (neighbors G w).card = 11)
    (cmin : ∀ u∈neighbors C w, 8 ≤ (neighbors C u).card)
    (e : Nat) (he : ∑ u∈neighbors C w,row C (neighbors C w) u = 2*e) :
    ((neighbors C w).card = 10 → e ≤ 14) ∧
    ((neighbors C w).card = 11 → e ≤ 13) := by
  classical
  let S := neighbors G w
  let X := ext S w
  let U := weightedSet X (fun x => Free (Forbidden G) (insert x (S : Set V)))
  let B := X \ U
  let a := (weightedSet B (Acol G S)).card
  let b := (weightedSet B (Bcol G S)).card
  let c := (weightedSet B (Ccol G S)).card
  let d := (weightedSet B (Dcol G S)).card
  let I := ∑ x∈X,ncol G S x
  let IU := ∑ x∈U,ncol G S x
  let ell := ∑ x∈X,lcol G S x
  have hS : Free (Forbidden G) (S : Set V) := by
    have h := neighborhood_free G sym tf w
    convert h using 1
    ext x
    exact mem_neighbors G
  have hUX : U ⊆ X := fun x hx => (Finset.mem_filter.mp hx).1
  have hBX : B ⊆ X := Finset.sdiff_subset
  have hXS : Disjoint X S := Finset.disjoint_left.mpr (by
    intro x hx hxS
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hxS))
  have hUS := Finset.disjoint_left.mpr (fun x hxU hxS => Finset.disjoint_left.mp hXS (hUX hxU) hxS)
  have hBS := Finset.disjoint_left.mpr (fun x hxB hxS => Finset.disjoint_left.mp hXS (hBX hxB) hxS)
  have hadd : ∀ x∈U, Free (Forbidden G) (insert x (S : Set V)) :=
    fun x hx => (Finset.mem_filter.mp hx).2
  have blocked : ∀ x∈B, ¬Free (Forbidden G) (insert x (S : Set V)) :=
    fun x hx hf => (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨hBX hx,hf⟩)
  have hS10 : S.card = 11 := h10
  have hx52 : 52 ≤ X.card := by
    have hwS : w ∉ S := fun hw => irr w ((mem_neighbors G).mp hw)
    change 52 ≤ ((Finset.univ : Finset V) \ insert w S).card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_insert_of_notMem hwS,hS10]
    omega
  obtain ⟨ha,habc,hls,hIB⟩ := degreeEleven_counts_h13 G S sym irr tf hS10 hS B hBS blocked upper
  obtain ⟨hz,hU3,hU2⟩ := degreeEleven_ambient_unblocked_h13 G sym irr tf S U hS10 hUS upper hadd
  obtain ⟨hIslots,hLslots⟩ := degreeEleven_upper_slots_h13 G C sym irr sub two degree w h10 cmin e he
  change I+2*e≤121 at hIslots
  change ell+7*(neighbors C w).card≤121 at hLslots
  have hLmono : (∑ x∈B,lcol G S x) ≤ ell :=
    Finset.sum_le_sum_of_subset_of_nonneg hBX (by intros; omega)
  have hcard := Finset.card_sdiff_add_card_eq_card hUX
  change B.card+U.card=X.card at hcard
  have hsplit := Finset.sum_sdiff hUX (f:=ncol G S)
  change (∑ x∈B,ncol G S x) + IU = I at hsplit
  have hlow : 3*52+IU≤I+3*U.card+(2*a+b+c+d) := by
    change 3*B.card ≤ (∑ x∈B,ncol G S x) + (2*a+b+c+d) at hIB
    omega
  have hl : a+c+2*d≤ell := by
    change a+c+2*d≤∑ x∈B,lcol G S x at hls
    exact hls.trans hLmono
  by_cases h3 : U.card = 3
  · have hh := hU3 h3
    change 6 ≤ IU at hh
    omega
  · omega

#print axioms degreeEleven_at_least64_h13
theorem degreeTwelve_at_least64_h13
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (tf : TriangleFreeLinks G)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (degree : ∀ v, (neighbors G v).card ≤ 12)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12)
    (hn : 64 ≤ Fintype.card V)
    (w : V) (h11 : (neighbors G w).card = 12)
    (cmin : ∀ u∈neighbors C w, 8 ≤ (neighbors C u).card)
    (e : Nat) (he : ∑ u∈neighbors C w,row C (neighbors C w) u = 2*e) :
    ((neighbors C w).card = 10 → 2*e ≤ 28) ∧
    ((neighbors C w).card = 11 → 2*e ≤ 24) ∧
    ((neighbors C w).card = 12 → 2*e ≤ 21) := by
  classical
  let S := neighbors G w
  let X := ext S w
  let A := (specialCols G S X).card
  let I := ∑ x∈X,ncol G S x
  let ell := ∑ x∈X,lcol G S x
  have hS : Free (Forbidden G) (S : Set V) := by
    have h := neighborhood_free G sym tf w
    convert h using 1
    ext x
    exact mem_neighbors G
  have hXS : Disjoint X S := Finset.disjoint_left.mpr (by
    intro x hx hxS
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hxS))
  have hS11 : S.card = 12 := h11
  have hx51 : 51 ≤ X.card := by
    have hwS : w ∉ S := fun hw => irr w ((mem_neighbors G).mp hw)
    change 51 ≤ ((Finset.univ : Finset V) \ insert w S).card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_insert_of_notMem hwS,hS11]
    omega
  have hLo := degreeTwelve_lower_incidence_h13 G S X sym irr tf hS11 hS hXS upper
  have hSpec := degreeTwelve_special_cost_h13 G S X sym irr tf hS11 hS hXS upper
  obtain ⟨hI,hL⟩ := degreeTwelve_upper_slots_h13 G C sym irr sub two degree w h11 cmin e he
  change 3*X.card ≤ I+12+A at hLo
  change 2*A ≤ ell+12 at hSpec
  change I+2*e ≤ 132 at hI
  change ell+7*(neighbors C w).card ≤132 at hL
  omega

#print axioms degreeTwelve_at_least64_h13

/-- Both high ambient-degree rows give strict core-link density deficit. -/
theorem high_rows_at_least64_h13
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFreeLinks G) (sub : ∀ {a b}, C a b → G a b)
    (two : TwoTriangles C)
    (degree : ∀ v, (neighbors G v).card ≤ 12)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12)
    (hn : 64 ≤ Fintype.card V)
    (w : V) (hd : 11 ≤ (neighbors G w).card)
    (hr : 10 ≤ (neighbors C w).card)
    (cmin : ∀ u∈neighbors C w, 8 ≤ (neighbors C u).card)
    (e : Nat) (he : ∑ u∈neighbors C w,row C (neighbors C w) u = 2*e) :
    2*e < 3*(neighbors C w).card := by
  have hs : neighbors C w ⊆ neighbors G w := fun _ h =>
    (mem_neighbors G).mpr (sub ((mem_neighbors C).mp h))
  have hc := Finset.card_le_card hs
  have hdeg := degree w
  by_cases h11 : (neighbors G w).card = 11
  · obtain ⟨h10,h11'⟩ := degreeEleven_at_least64_h13 G C sym irr tf sub two
      degree upper hn w h11 cmin e he
    by_cases h : (neighbors C w).card = 10
    · have := h10 h
      omega
    · have := h11' (by omega)
      omega
  · have h12 : (neighbors G w).card = 12 := by omega
    obtain ⟨h10,h11',h12'⟩ := degreeTwelve_at_least64_h13 G C sym irr tf sub two
      degree upper hn w h12 cmin e he
    by_cases h : (neighbors C w).card = 10
    · have := h10 h
      omega
    · by_cases h' : (neighbors C w).card = 11
      · have := h11' h'
        omega
      · have := h12' (by omega)
        omega

#print axioms high_rows_at_least64_h13
end Erdos151H12
