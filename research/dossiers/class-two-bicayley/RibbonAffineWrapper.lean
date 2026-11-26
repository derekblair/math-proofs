import RibbonAffineGroup
import RibbonMetaFinal
import RibbonP3Odd

namespace RibbonAffine
open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback
universe u

/-- Interface for the universal metabelian word certificates: their lifts
close in the actual group, and normalized affine images separate prefixes. -/
def AffineWitness : Prop :=
  ∀ {G : Type u} [Group G] (m : RibbonMeta.Meta G) (x y : G)
    {K : Type u} [Field K] [Finite K] (μ : G →* Kˣ) (τ : G → K) (n : ℕ),
    (2:K) ≠ 0 → IsCocycle μ τ → Odd n → (μ x)^n=1 → (μ y)^n=1 →
    μ x≠1 → τ x=0 → τ y=1 → Ribbon.Cycle x y 32

abbrev Good {G : Type u} [Group G] (x y : G) : Prop :=
  Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨ Ribbon.Cycle x y 32

private theorem generated_meta (cert : AffineWitness.{u}) {G : Type u} [Group G] [Finite G]
    (m : RibbonMeta.Meta G) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) : Good x y := by
  by_cases hc : portC x y=1
  · have R := Ribbon.class2_pair x y (portC x y) (hc ▸ Commute.one_left x) (hc ▸ Commute.one_left y)
      (ports_xy x y) hx (by simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd hy)
    exact R.imp_right (fun z => z.imp_right Or.inl)
  · refine Or.inr (Or.inr (Or.inr ?_))
    by_cases stat : portC x y∈LS G 2
    · obtain ⟨K,fK,nK,μ,τ,n,two,co,on,px,py,h⟩ := stationary_affine m x y gen odd stat hc
      rcases h with ⟨a,e,f⟩ | ⟨a,e,f⟩
      · exact cert m x y μ τ n two co on px py a e f
      · exact RibbonP3.flip_cycle (cert m y x μ τ n two co on py px a e f)
    · exact RibbonMeta.finite_odd_local_C32 m x y odd
        (fun e => stat ((QuotientGroup.eq_one_iff _).mp e))

/-- All finite odd metabelian groups, once supplied with the field-uniform
normalized affine word certificate. No nilpotence assumption. -/
theorem all_meta (cert : AffineWitness.{u}) {G : Type u} [Group G] [Finite G]
    (m : RibbonMeta.Meta G) (x y : G)
    (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) : Good x y := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  rcases generated_meta cert (RibbonMeta.subgroup_meta m S) _ _ (pair_generates x y)
      (Odd.of_dvd_nat odd dvd) hx' hy' with h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (pair_lift x y 32 h)))

theorem all_metabelian (cert : AffineWitness.{u}) {G : Type u} [Group G] [Finite G]
    (h : IsMulCommutative (commutator G)) (x y : G)
    (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) : Good x y := by
  apply all_meta cert _ x y odd hx hy
  rw [← Subgroup.top_lowerCentralSeries_one] at h
  have hh := isMulCommutative_iff.mp h
  intro a ha b hb
  exact congrArg Subtype.val (hh ⟨a,ha⟩ ⟨b,hb⟩)

end RibbonAffine
#print axioms RibbonAffine.all_meta
#print axioms RibbonAffine.all_metabelian
