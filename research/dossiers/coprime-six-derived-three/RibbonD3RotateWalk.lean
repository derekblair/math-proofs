import RibbonD3Closure
import Ribbon5Bridge64

namespace RibbonD3RotateWalk
open Ribbon5Bridge RibbonDerived3
variable {G : Type*} [Group G]

def base (b : Bool) : Bool × G := (b,1)

theorem shift_shift (g h : G) (p : Bool × G) : shift g (shift h p) = shift (g*h) p := by
  simp [shift,mul_assoc]

theorem reverse_eval (x y : G) (b : Bool) (a : G) (w : List P)
    (ha : run x y (base b) w = shift a (base b)) :
    run x y (base b) (reverseWord w) = shift a⁻¹ (base b) := by
  have H := undo_run x y (base b) w
  rw [ha,shift_run] at H
  have E := congrArg (shift a⁻¹) H
  simpa [shift_shift,shift] using E

/-- Exact displacement of traversing a closed-side word, followed by the reverse
of its rotation at a closed-side prefix. No group relation is assumed. -/
theorem rotation_eval (x y : G) (b : Bool) (r u : G) (A B : List P)
    (hA : run x y (base b) A = shift u (base b))
    (hAB : run x y (base b) (A++B) = shift r (base b)) :
    run x y (base b) ((A++B) ++ reverseWord (B++A)) =
      shift (r*u⁻¹*r⁻¹*u) (base b) := by
  rw [run_append,hA,shift_run] at hAB
  have tmp := congrArg (shift u⁻¹) hAB
  have hB : run x y (base b) B = shift (u⁻¹*r) (base b) := by
    simpa [shift_shift,shift,mul_assoc] using tmp
  have hBA : run x y (base b) (B++A) = shift (u⁻¹*r*u) (base b) := by
    rw [run_append,hB,shift_run,hA,shift_shift]
  have first : run x y (base b) (A++B) = shift r (base b) := by
    rw [run_append,hA,shift_run,hAB]
  rw [run_append,first,shift_run,reverse_eval x y b _ _ hBA,shift_shift]
  simp only [mul_inv_rev,inv_inv,mul_assoc]

/-- Combining the exact port identity with the derived class bound. -/
theorem twice_eval (x y : G) (b : Bool) (r u p : G) (A B C E : List P)
    (hA : run x y (base b) A = shift u (base b))
    (hAB : run x y (base b) (A++B) = shift r (base b))
    (hC : run x y (base b) C = shift p (base b))
    (align : C++E = (A++B) ++ reverseWord (B++A))
    (d3 : DLS G 3 = ⊥) (hr : r ∈ DLS G 1)
    (hu : u ∈ Derived G) (hp : p ∈ Derived G) :
    run x y (base b) ((C++E) ++ reverseWord (E++C)) = base b := by
  have hCE := rotation_eval x y b r u A B hA hAB
  rw [←align] at hCE
  rw [rotation_eval x y b _ p C E hC hCE,RibbonD3Closure.rotateTwice_close d3 hr hu hp]
  simp [shift]

#print axioms rotation_eval
#print axioms twice_eval
end RibbonD3RotateWalk
