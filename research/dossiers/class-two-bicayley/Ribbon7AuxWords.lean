import Ribbon7AuxDefs
import Ribbon5LawWords
namespace Ribbon7Aux
open scoped commutatorElement
variable {G : Type*} [Group G]
open Ribbon5Law (trace)
def diff (x y : G) (i j : Nat) : G :=
  (trace x y false (wd.take i))⁻¹ * trace x y false (wd.take j)


set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem a_end (x y : G) : trace x y false wa=res x y := by
  norm_num [trace,wa,res,U,V]
  try group

theorem b_end (x y : G) : trace x y false wb=V x y*U x y := by
  norm_num [trace,wb,U,V]
  try group

theorem w_end (x y : G) : trace x y false wc=⁅U x y,V x y⁆ := by
  norm_num [trace,wc,U,V,commutatorElement_def]
  try group

theorem res_form (x y : G) : res x y=t x y*⁅q x y,h x y⁆*(t x y)⁻¹ := by
  simp only [res,U,V,t,h,q,commutatorElement_def,pow_two]
  group
  simp only [zpow_ofNat,pow_two,mul_assoc]

def sideAfter : Bool → List (Fin 3) → Bool
  | b, [] => b
  | b, p::w => sideAfter (if p=2 then !b else b) w

theorem trace_append (x y : G) (u v : List (Fin 3)) (b : Bool) :
    trace x y b (u++v)=trace x y b u*trace x y (sideAfter b u) v := by
  induction u generalizing b with
  | nil => simp [trace,sideAfter]
  | cons p u ih =>
    by_cases e : p=2
    · simpa [e,trace,sideAfter] using ih (!b)
    · simp [e,trace,sideAfter,ih,mul_assoc]

theorem diff48 (x y : G) : diff x y 48 98=delta x y := by
  let v : List (Fin 3) := [2,0,0,2,1,1,2,1,2,0,2,0,2,0,2,1,1,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,2,1,2,1]
  have E : wd.take 98=wd.take 48++v := by decide +kernel
  have B : sideAfter false (wd.take 48)=true := by decide +kernel
  unfold diff
  rw [E,trace_append,B,inv_mul_cancel_left]
  norm_num [v,trace,delta]
  try group

theorem diff49 (x y : G) : diff x y 49 99=delta x y := by
  let v : List (Fin 3) := [0,0,2,1,1,2,1,2,0,2,0,2,0,2,1,1,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,2,1,2,1,2]
  have E : wd.take 99=wd.take 49++v := by decide +kernel
  have B : sideAfter false (wd.take 49)=false := by decide +kernel
  unfold diff
  rw [E,trace_append,B,inv_mul_cancel_left]
  norm_num [v,trace,delta]
  try group

theorem diff50 (x y : G) : diff x y 50 100=x⁻¹*delta x y*x := by
  let v : List (Fin 3) := [0,2,1,1,2,1,2,0,2,0,2,0,2,1,1,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,2,1,2,1,2,0]
  have E : wd.take 100=wd.take 50++v := by decide +kernel
  have B : sideAfter false (wd.take 50)=false := by decide +kernel
  unfold diff
  rw [E,trace_append,B,inv_mul_cancel_left]
  norm_num [v,trace,delta]
  try group

end Ribbon7Aux
#print axioms Ribbon7Aux.res_form
#print axioms Ribbon7Aux.diff50
