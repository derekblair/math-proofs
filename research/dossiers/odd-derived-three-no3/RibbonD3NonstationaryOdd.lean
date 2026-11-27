import RibbonD3Mixed3Dispatch
namespace RibbonD3Mixed3
open RibbonDerived3 RibbonD3Stationary HaarClass4Structure HaarClass4Ports HaarClass4Generate
universe u

theorem nonstationary_odd {G : Type u} [Group G] [Finite G]
    (char3 : CharThreeCover.{u}) (d3 : DLS G 3=⊥) (x y : G)
    (gen : Generates x y) (odd : Odd (Nat.card G))
    (hx : x≠1) (hy : y≠1) (nst : portC x y ∉ LS G 2) : WideGood x y := by
  let c := QuotientGroup.mk' (LS G 2) (portC x y)
  by_cases h3 : orderOf c=3
  · exact projected_three char3 d3 x y gen odd hx hy h3
  by_cases h5 : orderOf c=5
  · exact Or.inl (small_dispatch RibbonD3Low.mixed_small d3 x y 0 gen odd hx hy h5)
  by_cases h7 : orderOf c=7
  · exact Or.inl (small_dispatch RibbonD3Low.mixed_small d3 x y 1 gen odd hx hy h7)
  have c1 : c≠1 := fun h => nst ((QuotientGroup.eq_one_iff _).mp h)
  have good (k : Nat) (lo : 1≤k) (hi : k≤7) : c^k≠1 := by
    intro E
    have d := orderOf_dvd_iff_pow_eq_one.mpr E
    have le := (Nat.le_of_dvd (by omega : 0<k) d).trans hi
    have D : orderOf c ∣ Nat.card G := dvd_trans (orderOf_dvd_natCard c) (LS G 2).card_quotient_dvd_card
    have O := Odd.of_dvd_nat odd D
    have small : orderOf c=1 ∨ orderOf c=3 ∨ orderOf c=5 ∨ orderOf c=7 := by
      obtain ⟨v,h⟩ := O
      omega
    rcases small with H|H|H|H
    · exact c1 (orderOf_eq_one_iff.mp H)
    · exact h3 H
    · exact h5 H
    · exact h7 H
  exact Or.inl (Or.inr (Or.inr (Or.inr (RibbonDerived3.local_bound d3 x y good))))

#print axioms nonstationary_odd
end RibbonD3Mixed3
