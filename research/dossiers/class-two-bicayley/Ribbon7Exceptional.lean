import Ribbon7Local
import Ribbon7AuxFinish
namespace Ribbon7
open Ribbon5Bridge HaarUniversal36
variable {G : Type*} [Group G]

private theorem E (x y : G) (i : Nat) :
    (pathAt x y wt i).2 = Ribbon5Law.trace x y false (Ribbon7Aux.wd.take i) := by
  have h : wt.toList = Ribbon7Aux.wd := by decide +kernel
  simp only [pathAt,h,run_trace,start,one_mul]

theorem exceptional_proved (nil : L G 7=⊥) (x y : G) (h : Z x y≠1) :
    exceptional x y := by
  have g : Ribbon5Law.trace x y false Ribbon7Aux.wc ≠ 1 := by
    rw [Ribbon7Aux.w_end]
    exact h
  have helper (i j : Nat)
      (ij : (i=48 ∧ j=98) ∨ (i=49 ∧ j=99) ∨ (i=50 ∧ j=100)) :
      pathAt x y wt i ≠ pathAt x y wt j := by
    intro L
    have Q := congrArg Prod.snd L
    rw [E,E] at Q
    apply Ribbon7Aux.exceptional_ne nil x y g i j ij
    unfold Ribbon7Aux.diff
    rw [Q,inv_mul_cancel]
  exact ⟨helper 48 98 (Or.inl ⟨rfl,rfl⟩),
    helper 49 99 (Or.inr (Or.inl ⟨rfl,rfl⟩)),
    helper 50 100 (Or.inr (Or.inr ⟨rfl,rfl⟩))⟩

end Ribbon7
#print axioms Ribbon7.exceptional_proved
