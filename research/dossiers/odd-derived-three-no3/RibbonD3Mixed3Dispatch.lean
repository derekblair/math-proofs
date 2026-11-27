import RibbonD3Mixed3
import RibbonOrder3Affine
import RibbonD3P3Family

namespace RibbonD3Mixed3
open RibbonDerived3 RibbonD3Stationary RibbonP11 RibbonAffine HaarClass4Structure HaarClass4Ports
open HaarClass4Generate RibbonClass4Fallback
open scoped commutatorElement
universe u

abbrev WideGood {G : Type*} [Group G] (x y : G) :=
  LongGood x y ∨ Ribbon.Cycle x y 256

/-- A characteristic-three field chart can be supplied independently. -/
def CharThreeCover : Prop :=
  ∀ {G K : Type u} [Group G] [Field K] [Finite G] [Finite K]
    (_d3 : DLS G 3=⊥) (x y : G) (μ : G→*Kˣ) (τ : G→K),
    (2:K)≠0 → (3:K)=0 → Odd (Nat.card G) → RibbonP11.IsCocycle μ τ →
    Normalized (RingHom.id K) x y μ τ →
    (μ x)^(Nat.card G)=1 → (μ y)^(Nat.card G)=1 → WideGood x y

theorem projected_three_of_shadow {G K : Type*} [Group G] [Field K]
    (d3 : DLS G 3=⊥) (x y : G) (μ : G→*Kˣ) (τ : G→K)
    (o : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=3)
    (h2 : (2:K)≠0) (h3 : (3:K)≠0)
    (co : RibbonP11.IsCocycle μ τ) (norm : Normalized (RingHom.id K) x y μ τ) : LongGood x y := by
  rcases norm with ⟨n,z,t⟩|⟨_,n,z,t⟩
  · exact Or.inr (Or.inr (Or.inr (projected_three_normalized d3 x y o μ τ co n h2 h3 z t)))
  · have h : portC y x = (portC x y)⁻¹ := by simp [portC,commutatorElement_inv]
    have O : orderOf (QuotientGroup.mk' (LS G 2) (portC y x))=3 := by
      rwa [h,map_inv,orderOf_inv]
    rcases projected_three_normalized d3 y x O μ τ co n h2 h3 t z with c|c|c
    · exact Or.inr (Or.inr (Or.inr (Or.inl (RibbonP3.flip_cycle c))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (RibbonP3.flip_cycle c)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (RibbonP3.flip_cycle c)))))

/-- The entire projected-order-three case, conditional only on an independent char-three cover. -/
theorem projected_three {G : Type u} [Group G] [Finite G]
    (char3 : CharThreeCover.{u}) (d3 : DLS G 3=⊥) (x y : G)
    (gen : Generates x y) (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1)
    (o : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=3) : WideGood x y := by
  by_cases st : LS G 2=LS G 3
  · by_cases z : LS G 2=⊥
    · exact Or.inl (class_two_case z x y odd hx hy)
    have h : ¬LS G 2≤(commutator (D G)).map (D G).subtype := by
      have H := RibbonIA.stable_visible (G:=G) ⟨3,d3⟩ st z
      rw [←Subgroup.top_lowerCentralSeries_one,Subgroup.top_subtype_lowerCentralSeries]
      exact H
    obtain ⟨K,F,I,μ,τ,h2,co,n,px,py⟩ :=
      RibbonOrder3.stable_third_affine_of_visible x y gen odd st h
    by_cases h3 : (3:K)=0
    · exact char3 d3 x y μ τ h2 h3 odd co n px py
    · exact Or.inl (projected_three_of_shadow d3 x y μ τ o h2 h3 co n)
  · rcases RibbonD3P3.nonstable_projected_three d3 x y gen o st with c|c|c
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl c))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c)))))
    · exact Or.inr c

#print axioms projected_three_of_shadow
#print axioms projected_three
end RibbonD3Mixed3
