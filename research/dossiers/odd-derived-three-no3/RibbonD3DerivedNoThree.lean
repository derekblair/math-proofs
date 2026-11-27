import RibbonAffineCocycle
import RibbonStationaryChart
import RibbonP11Interfaces

namespace RibbonD3DerivedNoThree
open HaarClass4Structure HaarClass4Ports RibbonAffine RibbonStationaryChart
open scoped commutatorElement
variable {G K : Type*} [Group G] [Field K]

abbrev GoodDerived (G : Type*) [Group G] := ¬3∣Nat.card (D G)

theorem mu_derived (μ : G→*Kˣ) (d : D G) : μ d=1 := by
  apply MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker μ ?_)
  have E := d.property
  change (d:G) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 at E
  rwa [Subgroup.top_lowerCentralSeries_one] at E

theorem tau_eq_zero [Finite G] [CharP K 3] (no3 : GoodDerived G)
    (μ : G→*Kˣ) (τ : G→K) (co : Aff μ τ) (d : D G) : τ d=0 := by
  let f : D G→*Multiplicative K := {
    toFun := fun g => Multiplicative.ofAdd (τ g)
    map_one' := co.1
    map_mul' := fun a b => by
      change τ (a.val*b.val)=τ a.val+τ b.val
      rw [co.2,mu_derived μ a,Units.val_one,one_mul] }
  have e : f d ^ Nat.card (D G)=1 := by rw [←map_pow,pow_card_eq_one',map_one]
  have h : Nat.card (D G) • τ d=0 := by
    have eq : f d = Multiplicative.ofAdd (τ d) := rfl
    rw [eq] at e
    have ee := congrArg (fun z : Multiplicative K => z.toAdd) e
    rw [toAdd_pow] at ee
    exact ee
  have h' : (Nat.card (D G):K) * τ d=0 := by
    simpa only [nsmul_eq_mul] using h
  have z : (Nat.card (D G):K)≠0 := fun e => no3 ((CharP.cast_eq_zero_iff K 3 _).mp e)
  exact (mul_eq_zero.mp h').resolve_left z

theorem not_normalized [Finite G] [CharP K 3] (no3 : GoodDerived G)
    (x y : G) (μ : G→*Kˣ) (τ : G→K) (co : Aff μ τ)
    (norm : RibbonP11.Normalized (RingHom.id K) x y μ τ) : False := by
  have cd : portC x y∈D G := layer_c x y
  have z := tau_eq_zero no3 μ τ co ⟨portC x y,cd⟩
  change τ (portC x y)=0 at z
  have H := congrArg τ (ports_xy x y)
  rw [co.2 (y*x) (portC x y),z,mul_zero,add_zero,co.2 x y,co.2 y x] at H
  rcases norm with ⟨px,x0,y1⟩ | ⟨_,py,x1,y0⟩
  · exact px (by simpa [x0,y1] using H)
  · exact py (by simpa [x1,y0] using H.symm)

theorem inherited [Finite G] (no3 : GoodDerived G) (S : Subgroup G) : GoodDerived S := by
  have le : (D S).map S.subtype ≤ D G := Subgroup.lowerCentralSeries_map_subtype_le S 1
  have mul : Nat.card (D S) ∣ Nat.card (D G) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective (D S) S.subtype Subtype.val_injective).toEquiv]
    exact Subgroup.card_dvd_of_le le
  exact fun h => no3 (dvd_trans h mul)

theorem projected_order_dvd [Finite G] (x y : G) :
    orderOf (QuotientGroup.mk' (LS G 2) (portC x y)) ∣ Nat.card (D G) := by
  let f : D G→*G ⧸ LS G 2 := (QuotientGroup.mk' (LS G 2)).comp (D G).subtype
  exact dvd_trans (orderOf_map_dvd f ⟨portC x y,layer_c x y⟩)
    (orderOf_dvd_natCard (⟨portC x y,layer_c x y⟩ : D G))

#print axioms not_normalized
#print axioms inherited
#print axioms projected_order_dvd
end RibbonD3DerivedNoThree
