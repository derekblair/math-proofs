import RibbonClass4Short
import RibbonClass4Fallback

namespace RibbonClass4Family

open HaarClass4Structure HaarClass4Ports HaarClass4Generate
open RibbonClass4 RibbonClass4Fallback
variable {G : Type*} [Group G]

private theorem fourth_ne (h : ∀ {g : G}, g≠1 → g*g≠1)
    {g : G} (hg : g≠1) : g^(4:Nat)≠1 := by
  intro eq
  apply h (g:=g^2)
  · simpa only [pow_two] using h hg
  · rw [← pow_add]
    simpa using eq

/-- One selected fourth-layer coordinate of order not dividing four
already forces a simple C32, with no restriction on other torsion. -/
theorem cycle32_of_fourth (nil : LS G 4=⊥) (x y : G) (s : Fin 3)
    (nz : (target (make nil x y) s)^(4:Nat)≠1) : Ribbon.Cycle x y 32 := by
  have projGood : RibbonClass4Short.Good (proj G (portC x y)) :=
    fun eq => nz (target_power_from_proj nil x y s 4 eq)
  exact RibbonClass4Short.cycle32 (make nil x y) (proj G) (kills nil x y) projGood

private theorem generated (nil : LS G 4=⊥) (x y : G) (gen : Generates x y)
    (no2 : ∀ {g : G}, g≠1 → g*g≠1) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨ Ribbon.Cycle x y 32 := by
  let M := make nil x y
  by_cases ha : M.a=1
  · by_cases hb : M.b=1
    · by_cases hd : M.d=1
      · exact RibbonClass3.involution_free_class3 x y (class_drop x y gen nil ha hb hd) no2 hx hy
      · exact Or.inr (Or.inr (Or.inr (cycle32_of_fourth nil x y 2 (fourth_ne no2 hd))))
    · exact Or.inr (Or.inr (Or.inr (cycle32_of_fourth nil x y 1 (fourth_ne no2 hb))))
  · exact Or.inr (Or.inr (Or.inr (cycle32_of_fourth nil x y 0 (fourth_ne no2 ha))))

theorem involution_free_class4 (nil : LS G 4=⊥) (x y : G)
    (no2 : ∀ {g : G}, g≠1 → g*g≠1) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨ Ribbon.Cycle x y 32 := by
  let P := Pair x y
  have hx' : leftPort x y ≠ 1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y ≠ 1 := fun e => hy (congrArg Subtype.val e)
  have no2' : ∀ {g : P}, g≠1 → g*g≠1 := by
    intro g ng eq
    have ne : (g:G)≠1 := fun e => ng (Subtype.ext e)
    exact no2 ne (congrArg Subtype.val eq)
  rcases generated (pair_nil x y 4 nil) _ _ (pair_generates x y) no2' hx' hy' with h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (pair_lift x y 32 h)))

theorem odd_class4 (nil : LS G 4=⊥) (x y : G) (odd : Odd (Nat.card G))
    (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨ Ribbon.Cycle x y 32 :=
  involution_free_class4 nil x y (fun h => by
    simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd h) hx hy

end RibbonClass4Family
#print axioms RibbonClass4Family.cycle32_of_fourth
#print axioms RibbonClass4Family.involution_free_class4
#print axioms RibbonClass4Family.odd_class4
