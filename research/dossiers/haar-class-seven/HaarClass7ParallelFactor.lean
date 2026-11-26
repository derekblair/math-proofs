import HaarClass7ParallelPairs

namespace HaarClass7ParallelFactor
open HaarClass7Parallel HaarClass7ParallelCycle HaarHalfCollision
open scoped commutatorElement
variable {G : Type*} [Group G]

def Z (x y : G) (t : Fin 3) : G :=
  if t=2 then ⁅y⁻¹,x⁻¹⁆ * ⁅x⁻¹,y⁆ else ⁅x⁻¹*x⁻¹,y⁆

theorem factor (x y : G) (t : Fin 3) :
    prodFrom x y 0 (B t) = (Z x y t)⁻¹ * prodFrom x y 0 (A t) * Z x y t := by
  fin_cases t
  · change prodFrom x y 0 B1 = (Z x y 0)⁻¹ * prodFrom x y 0 A1 * Z x y 0
    norm_num [Z,A1,B1,prodFrom,signPort,port,commutatorElement_def] <;> group
  · change prodFrom x y 0 B2 = (Z x y 1)⁻¹ * prodFrom x y 0 A2 * Z x y 1
    norm_num [Z,A2,B2,prodFrom,signPort,port,commutatorElement_def] <;> group
  · change prodFrom x y 0 B3 = (Z x y 2)⁻¹ * prodFrom x y 0 A3 * Z x y 2
    norm_num [Z,A3,B3,prodFrom,signPort,port,commutatorElement_def] <;> group

theorem detects (x y : G) (t : Fin 3)
    (nz : ⁅Z x y t,prodFrom x y 0 (A t)⁆≠1) :
    prodFrom x y 0 (A t) ≠ prodFrom x y 0 (B t) := by
  intro e
  have h := congrArg (fun a => Z x y t * a) e
  rw [factor] at h
  apply nz
  apply Commute.commutator_eq
  change Z x y t * prodFrom x y 0 (A t)=prodFrom x y 0 (A t) * Z x y t
  simpa only [←mul_assoc,mul_inv_cancel,mul_one,one_mul] using h

end HaarClass7ParallelFactor
#print axioms HaarClass7ParallelFactor.detects
