import RibbonD3OrderFive
import RibbonD3SmallDispatch

namespace RibbonD3Low
open RibbonDerived3 HaarClass4Structure HaarClass4Ports RibbonClass4Fallback
open RibbonD3Stationary RibbonP11 Ribbon8Small
open scoped commutatorElement
universe u

theorem minus_not_zero {K : Type*} [Field K] (bad : (2:K) ≠ 0)
    (b : Kˣ) {n : Nat} (hn : Odd n) (e : b^n=1) : (b:K)+1 ≠ 0 := by
  intro h
  have hB : (b:K) = -1 := eq_neg_of_add_eq_zero_left h
  have P : (b:K)^n=1 := by simpa only [Units.val_pow_eq_pow_val,Units.val_one] using congrArg Units.val e
  rw [hB,hn.neg_one_pow] at P
  apply bad
  linear_combination -P

private theorem order_swap {G : Type*} [Group G] (x y : G) :
    orderOf (QuotientGroup.mk' (LS G 2) (portC y x)) =
      orderOf (QuotientGroup.mk' (LS G 2) (portC x y)) := by
  have h : portC y x = (portC x y)⁻¹ := by simp [portC,commutatorElement_inv]
  rw [h,map_inv,orderOf_inv]

private theorem liftLong {G : Type*} [Group G] {x y : G}
    (h : Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128) :
    LongGood x y := Or.inr (Or.inr (Or.inr h))

theorem mixed_small : MixedSmallCover.{u} := by
  intro G K iG iK fg fk dnil x y p μ τ o h2 odd co N hx hy
  fin_cases p
  · change orderOf (QuotientGroup.mk' (LS G 2) (portC x y)) = 5 at o
    rcases N with ⟨n,z,t⟩|⟨_,n,z,t⟩
    · exact liftLong (projected_five_normalized dnil x y o μ τ co n (minus_not_zero h2 _ odd hy) z t)
    · have O : orderOf (QuotientGroup.mk' (LS G 2) (portC y x)) = 5 := (order_swap x y).trans o
      rcases projected_five_normalized dnil y x O μ τ co n (minus_not_zero h2 _ odd hx) t z with h|h|h
      · exact liftLong (Or.inl (RibbonP3.flip_cycle h))
      · exact liftLong (Or.inr (Or.inl (RibbonP3.flip_cycle h)))
      · exact liftLong (Or.inr (Or.inr (RibbonP3.flip_cycle h)))
  · change orderOf (QuotientGroup.mk' (LS G 2) (portC x y)) = 7 at o
    exact liftLong (projected_seven dnil x y o)

#print axioms mixed_small
end RibbonD3Low
