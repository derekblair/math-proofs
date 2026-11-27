import HaarDerivedGirthEnd
import HaarDerivedWreathUpper
import HaarDerivedBase22Witness
import HaarDerivedBarbell

namespace HaarDerivedThree128
open HaarAllNoncommuting HaarDerivedGirth22 HaarDerivedWreathCore
open HaarDerivedWreathTrace HaarDerivedWreathGirth
open scoped commutatorElement

abbrev H := W G
abbrev X : H := up false x
abbrev Y : H := up true y

theorem no_cycle_below66 (n : ℕ) (lo : 3≤n) (hi : n<66) : ¬ HasCycle X Y n := by
  intro h
  have l : HasCycle (liftPort x y 1) (liftPort x y 2) n := h
  have large := girth_bound x y x_ne_one y_ne_one x_ne_y 11
    (fun k a cy => by
      by_contra! small
      exact no_cycle_below22 k a small cy) n lo l
  omega

theorem cycle66 : HasCycle X Y 66 := by
  exact HaarDerivedWreathUpper.threefold_shortest x y x_ne_one y_ne_one x_ne_y 11
    (by decide)
    (fun k lo cy => by
      by_contra! small
      exact no_cycle_below22 k lo small cy)
    HaarDerivedBase22Witness.cycle22

theorem three_exact : derivedSeries H 3=⊥ ∧ derivedSeries H 2≠⊥ := by
  refine ⟨wreath_candidate.2,?_⟩
  intro h
  let a := ⁅X,Y⁆
  let b := ⁅Y,X⁻¹⁆
  have ha : a ∈ commutator H := Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hb : b ∈ commutator H := Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [show (2:ℕ)=1+1 by decide,derivedSeries_succ,derivedSeries_one] at h
  have eq := commutatorElement_eq_one_iff_mul_comm.mp
    (Subgroup.mem_bot.mp (Subgroup.commutator_le.mp h.le a ha b hb))
  have q : (a*b).lamp false 1 ≠ (b*a).lamp false 1 := by
    dsimp only [a,b]
    decide +kernel
  exact q (congrArg (fun g : H => g.lamp false 1) eq)

theorem ports_distinct : X≠1 ∧ Y≠1 ∧ X≠Y := by
  refine ⟨?_,?_,?_⟩
  · intro e; exact x_ne_one (congrArg (fun q : H => q.pos) e)
  · intro e; exact y_ne_one (congrArg (fun q : H => q.pos) e)
  · intro e; exact x_ne_y (congrArg (fun q : H => q.pos) e)

/-- A finite odd-order cubic Haar graph of derived length exactly three whose
least power-of-two simple cycle length is 128. -/
theorem sharp :
    Odd (Nat.card H) ∧ (derivedSeries H 3=⊥ ∧ derivedSeries H 2≠⊥) ∧
    (X≠1 ∧ Y≠1 ∧ X≠Y) ∧
    HasCycle X Y 66 ∧ HasCycle X Y 128 ∧ ∀ n ∈ [4,8,16,32,64], ¬ HasCycle X Y n := by
  refine ⟨wreath_candidate.1,three_exact,ports_distinct,cycle66,HaarDerivedBarbell.cycle128,?_⟩
  intro n hn
  simp at hn
  exact no_cycle_below66 n (by omega) (by omega)

end HaarDerivedThree128
#print axioms HaarDerivedThree128.no_cycle_below66
#print axioms HaarDerivedThree128.three_exact
#print axioms HaarDerivedThree128.cycle66
#print axioms HaarDerivedThree128.sharp
