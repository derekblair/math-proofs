import WeightedGraph
namespace IU.Slack
open Finset

def compact (t : Nat) (x : Q) : Q := (t-x.1,x.2.1,full x-t)

lemma mass_bounds {t u s : Nat} {x : Q} (h : Admissible t u s x)
    (c : Qcompat t s x x) : 2*((t-x.1)+x.2.2)≤s := by
  obtain ⟨i,iS,e⟩ := c
  have w : x.2.1.filter (·<t+i) ⊆ mid t i := by
    intro k hk
    obtain ⟨k1,k2⟩ := mem_filter.mp hk
    exact mem_sdiff.mpr ⟨mem_range.mpr k2,(mem_sdiff.mp (h.1 k1)).2⟩
  have w1 := card_le_card w
  rw [card_sdiff_of_subset (range_mono (by omega)),card_range,card_range] at w1
  have w2 : (x.2.1.filter (· < t+i)).card≤x.2.1.card := card_le_card (filter_subset _ _)
  have p1 := h.2.1
  have p2 := h.2.2.2.1
  have p3 := h.2.2.2.2
  unfold full at e p2 p3
  omega

theorem compact_card {I : Finset Q} {t u s : Nat}
    (adm : ∀ x∈I, Admissible t u s x) (self : ∀ x∈I, Qcompat t s x x) :
    I.card≤(s/2+1)*(2^s)*(s+1) := by
  let U := (range (s/2+1)) ×ˢ ((mid t s).powerset ×ˢ range (s+1))
  have ssub : I.image (compact t) ⊆ U := by
    intro x xh
    obtain ⟨y,hy,rfl⟩ := mem_image.mp xh
    have v := adm y hy
    have bd := mass_bounds v (self y hy)
    refine mem_product.mpr ⟨mem_range.mpr (by unfold compact; omega),
      mem_product.mpr ⟨mem_powerset.mpr v.1,mem_range.mpr ?_⟩⟩
    have f := v.2.2.2.2
    change full y-t < s+1
    omega
  have inj : Set.InjOn (compact t) (↑I : Set Q) := by
    intro x hx y hy xy
    have hx' := adm x hx
    have hy' := adm y hy
    have a := congrArg Prod.fst xy
    have b := congrArg (fun z => z.2.1) xy
    have c := congrArg (fun z => z.2.2) xy
    change t-x.1=t-y.1 at a
    change x.2.1=y.2.1 at b
    change full x-t=full y-t at c
    have ax := hx'.2.1
    have ay := hy'.2.1
    have fx := hx'.2.2.2.1
    have fy := hy'.2.2.2.1
    have d := congrArg Finset.card b
    unfold full at c fx fy
    apply Prod.ext (by omega)
    apply Prod.ext b
    omega
  have cap := card_le_card ssub
  rw [card_image_of_injOn inj] at cap
  dsimp [U] at cap
  rw [card_product,card_product,card_range,card_range,card_powerset,
    card_sdiff_of_subset (range_mono (by omega)),card_range,card_range,
    show t+s-t=s by omega,←Nat.mul_assoc] at cap
  exact cap

#print axioms compact_card
#print axioms mass_bounds
end IU.Slack
