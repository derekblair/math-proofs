import HaarClass5P3MetaModel
import HaarClass5L2Abelian
import HaarP3LayerGenConcrete

namespace HaarP3ExceptionalFinish

open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Data HaarP3LayerGen
variable {G : Type*} [Group G]

theorem rc_inj (x : G) : Function.Injective (rc x : G → G) := by
  intro a b h
  change x⁻¹*a*x=x⁻¹*b*x at h
  exact mul_left_cancel (mul_right_cancel h)

theorem exceptional_comm (x y c u A : G) (ua : Commute u A) (xy : x*y=y*x*c)
    (ha3 : A^(3:ℕ)=1)
    (xu : rc x⁻¹ u = u*A⁻¹) (xa : rc x⁻¹ A=u^(3:ℕ)*A)
    (yu : rc y⁻¹ u = A*(u^(2:ℕ))⁻¹) (ya : rc y⁻¹ A=(u^(3:ℕ))⁻¹*A) :
    Commute c u := by
  have l : rc x⁻¹ (rc y⁻¹ u)=u := by
    rw [yu,map_mul,map_inv,map_pow,xa,xu,ua.inv_right.mul_pow,mul_inv_rev]
    rw [show ((A⁻¹)^(2:ℕ))⁻¹=A^(2:ℕ) by rw [inv_pow,inv_inv]]
    calc
      u^3*A*(A^2*(u^2)⁻¹) = u^3*(A^3)*(u^2)⁻¹ := by group
      _ = u := by rw [ha3]; group
  have r : rc y⁻¹ (rc x⁻¹ u)=u := by
    rw [xu,map_mul,map_inv,yu,ya,mul_inv_rev,inv_inv]
    calc
      (A*(u^2)⁻¹)*(A⁻¹*u^3) = (((u^2)⁻¹)*A)*(A⁻¹*u^3) := by rw [(ua.pow_left 2).inv_left.symm.eq]
      _ = u := by group
  have l' : rc (x*y)⁻¹ u=u := by simpa only [mul_inv_rev,rc_add] using l
  have tr : rc y⁻¹ (rc x⁻¹ (rc c⁻¹ u))=rc y⁻¹ (rc x⁻¹ u) := by
    calc
      _ = rc (x*y)⁻¹ u := by rw [xy,mul_inv_rev,mul_inv_rev,rc_add,rc_add]
      _ = u := l'
      _ = _ := r.symm
  have e := rc_inj x⁻¹ (rc_inj y⁻¹ tr)
  change (c⁻¹)⁻¹*u*c⁻¹=u at e
  rw [inv_inv] at e
  exact mul_inv_eq_iff_eq_mul.mp e

end HaarP3ExceptionalFinish
#print axioms HaarP3ExceptionalFinish.exceptional_comm
