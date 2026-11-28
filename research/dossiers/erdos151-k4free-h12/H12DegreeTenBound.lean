import H12DegreeTenUpper
import H12UnblockedCounts

namespace Erdos151H12
open Erdős151 Erdős151.Upper
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V] (G C : V → V → Prop)
variable [DecidableRel G] [DecidableRel C]

/-- Complete finite graph bridge for the exceptional degree-ten rows at order ≥53.
The supplied e is exactly half the internal directed core degree sum (no assumed
bound on e). The two explicitly realized equality profiles are excluded internally. -/
theorem degreeTen_at_least53
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (tf : TriangleFreeLinks G)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (degree : ∀ v, (neighbors G v).card ≤ 11)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (hn : 53 ≤ Fintype.card V)
    (w : V) (h10 : (neighbors G w).card = 10)
    (cmin : ∀ u∈neighbors C w, 8 ≤ (neighbors C u).card)
    (e : Nat) (he : ∑ u∈neighbors C w,row C (neighbors C w) u = 2*e) :
    ((neighbors C w).card = 9 → e ≤ 13) ∧
    ((neighbors C w).card = 10 → e ≤ 14) := by
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
  have hS10 : S.card = 10 := h10
  have hx42 : 42 ≤ X.card := by
    have hwS : w ∉ S := fun hw => irr w ((mem_neighbors G).mp hw)
    change 42 ≤ ((Finset.univ : Finset V) \ insert w S).card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_insert_of_notMem hwS,hS10]
    omega
  obtain ⟨ha,habc,hls,hIB⟩ := degreeTen_counts G S sym irr tf hS10 hS B hBS blocked upper
  obtain ⟨hz,hU3,hU2⟩ := degreeTen_ambient_unblocked G sym irr tf S U hS10 hUS upper hadd
  obtain ⟨hIslots,hLslots⟩ := degreeTen_upper_slots G C sym irr sub two degree w h10 cmin e he
  change I+2*e≤100 at hIslots
  change ell+7*(neighbors C w).card≤100 at hLslots
  have hLmono : (∑ x∈B,lcol G S x) ≤ ell :=
    Finset.sum_le_sum_of_subset_of_nonneg hBX (by intros; omega)
  have hcard := Finset.card_sdiff_add_card_eq_card hUX
  change B.card+U.card=X.card at hcard
  have hsplit := Finset.sum_sdiff hUX (f:=ncol G S)
  change (∑ x∈B,ncol G S x) + IU = I at hsplit
  have hlow : 3*42+IU≤I+3*U.card+(2*a+b+c+d) := by
    change 3*B.card ≤ (∑ x∈B,ncol G S x) + (2*a+b+c+d) at hIB
    omega
  have hl : a+c+2*d≤ell := by
    change a+c+2*d≤∑ x∈B,lcol G S x at hls
    exact hls.trans hLmono
  have hprofiles := degreeTen_endpoints (neighbors C w).card e I U.card IU a b c d ell hz hU3
    (fun _ => if h : IU=0 then Or.inl h else Or.inr (by omega)) ha habc hl hLslots hlow hIslots
  refine ⟨?_,hprofiles.1⟩
  intro hr
  by_contra! hbig
  obtain ⟨hUcard,hIU,_,_,hprof⟩ := hprofiles.2 hr hbig
  rcases hprof with h19|h20
  · have hb : (weightedSet B (Bcol G S)).Nonempty := by
      apply Finset.card_pos.mp
      change 0 < b
      omega
    exact degreeTen_nineteen_impossible G sym irr S B hS10 hS hBS blocked upper (by
      change 19 ≤ a
      omega) hb
  · have hd : (weightedSet B (Dcol G S)).Nonempty := by
      apply Finset.card_pos.mp
      change 0 < d
      omega
    obtain ⟨u,v,hu,hv,_,hL,hNo⟩ := hU2 hUcard hIU
    have huS : u∉S := Finset.disjoint_left.mp hUS hu
    have hvS : v∉S := Finset.disjoint_left.mp hUS hv
    exact degreeTen_twenty_impossible G sym irr S B hS10 hS hBS blocked upper degree
      u v huS hvS hL hNo (by change 20 ≤ a; omega) hd

#print axioms degreeTen_at_least53
end Erdos151H12
