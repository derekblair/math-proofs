import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

namespace RibbonP3
open scoped commutatorElement
variable {G : Type*} [Group G]
def a : List (Fin 3) := [0,0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,1,2]
def b : List (Fin 3) := [2,0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,1,2,0,0,2,0,0,2,1,2,1,1,2,1]
def ax : List (Fin 3) := [0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,1,2,0]
def bx : List (Fin 3) := [2,0,0,2,1,2,1,1,2,0,0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,1,2,1]

def trace (x y : G) : Bool → List (Fin 3) → G
  | _, [] => 1
  | side, p::w =>
    if p=2 then trace x y (!side) w
    else let g := if side then y else x
         (if p=0 then g else g⁻¹) * trace x y side w

def pref (x y : G) (w : List (Fin 3)) (i : ℕ) : G :=
  trace x y false (w.take i)

theorem factorA (x y : G) :
    trace x y false a =
      x * ⁅⁅x,y*y⁆, x⁻¹ * (⁅x,y*y⁆)⁻¹ * x⁆ * x⁻¹ := by
  norm_num [a,trace,commutatorElement_def]
  first | rfl | group
theorem endpoint_b (x y : G) :
    trace x y false b = (x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹) * trace x y false a * (x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹)⁻¹ := by
  norm_num [a,b,trace]
  first | rfl | group
theorem endpoint_ax (x y : G) :
    trace x y false ax = (x⁻¹) * trace x y false a * (x⁻¹)⁻¹ := by
  norm_num [a,ax,trace]
  first | rfl | group
theorem endpoint_bx (x y : G) :
    trace x y false bx = (x*y*y*x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹) * trace x y false a * (x*y*y*x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹)⁻¹ := by
  norm_num [a,bx,trace]
  first | rfl | group
theorem pair_a_1_31 (x y : G) :
    (pref x y a 1)⁻¹ * pref x y b 31 =
      (y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹) * (trace x y false a) * (y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹)⁻¹ := by
  norm_num [pref,a,b,trace,List.take_succ_cons]
  first | rfl | group
theorem pair_a_27_5 (x y : G) :
    (pref x y a 27)⁻¹ * pref x y b 5 =
      (x⁻¹*y⁻¹*y⁻¹) * ((trace x y false a)⁻¹) * (x⁻¹*y⁻¹*y⁻¹)⁻¹ := by
  norm_num [pref,a,b,trace,List.take_succ_cons]
  first | rfl | group
theorem pair_a_28_4 (x y : G) :
    (pref x y a 28)⁻¹ * pref x y b 4 =
      (y⁻¹*y⁻¹) * ((trace x y false a)⁻¹) * (y⁻¹*y⁻¹)⁻¹ := by
  norm_num [pref,a,b,trace,List.take_succ_cons]
  first | rfl | group
theorem pair_a_29_3 (x y : G) :
    (pref x y a 29)⁻¹ * pref x y b 3 =
      (y⁻¹*y⁻¹) * ((trace x y false a)⁻¹) * (y⁻¹*y⁻¹)⁻¹ := by
  norm_num [pref,a,b,trace,List.take_succ_cons]
  first | rfl | group
theorem pair_a_30_2 (x y : G) :
    (pref x y a 30)⁻¹ * pref x y b 2 =
      (y⁻¹) * ((trace x y false a)⁻¹) * (y⁻¹)⁻¹ := by
  norm_num [pref,a,b,trace,List.take_succ_cons]
  first | rfl | group
theorem pair_a_31_1 (x y : G) :
    (pref x y a 31)⁻¹ * pref x y b 1 =
      (1) * ((trace x y false a)⁻¹) * (1)⁻¹ := by
  norm_num [pref,a,b,trace,List.take_succ_cons]
theorem pair_ax_1_31 (x y : G) :
    (pref x y ax 1)⁻¹ * pref x y bx 31 =
      (y*y*x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹) * (trace x y false a) * (y*y*x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹)⁻¹ := by
  norm_num [pref,a,ax,bx,trace,List.take_succ_cons]
  first | rfl | group
theorem pair_ax_2_30 (x y : G) :
    (pref x y ax 2)⁻¹ * pref x y bx 30 =
      (y*y*x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹) * (trace x y false a) * (y*y*x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹)⁻¹ := by
  norm_num [pref,a,ax,bx,trace,List.take_succ_cons]
  first | rfl | group
theorem pair_ax_3_29 (x y : G) :
    (pref x y ax 3)⁻¹ * pref x y bx 29 =
      (y*x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹) * (trace x y false a) * (y*x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹)⁻¹ := by
  norm_num [pref,a,ax,bx,trace,List.take_succ_cons]
  first | rfl | group
theorem pair_ax_4_28 (x y : G) :
    (pref x y ax 4)⁻¹ * pref x y bx 28 =
      (x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹) * (trace x y false a) * (x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹)⁻¹ := by
  norm_num [pref,a,ax,bx,trace,List.take_succ_cons]
  first | rfl | group
theorem pair_ax_5_27 (x y : G) :
    (pref x y ax 5)⁻¹ * pref x y bx 27 =
      (x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹) * (trace x y false a) * (x⁻¹*x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹)⁻¹ := by
  norm_num [pref,a,ax,bx,trace,List.take_succ_cons]
  first | rfl | group
theorem pair_ax_6_26 (x y : G) :
    (pref x y ax 6)⁻¹ * pref x y bx 26 =
      (x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹) * (trace x y false a) * (x⁻¹*y⁻¹*y⁻¹*x*y*y*x*y⁻¹*y⁻¹*x⁻¹*x⁻¹)⁻¹ := by
  norm_num [pref,a,ax,bx,trace,List.take_succ_cons]
  first | rfl | group
end RibbonP3
#print axioms RibbonP3.factorA
#print axioms RibbonP3.pair_ax_6_26
