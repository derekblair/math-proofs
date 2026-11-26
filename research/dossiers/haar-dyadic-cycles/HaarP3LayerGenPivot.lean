import HaarP3LayerGenQuot

namespace HaarP3LayerGen

open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Generate HaarClass4Data HaarClass4CollectCore
variable {G : Type*} [Group G]

theorem rc_pow_parts {x u a : G} (hu : rc x u = u*a) (ha : Central a) (n : ℕ) :
    rc x (u^n) = u^n*a^n := by
  rw [map_pow,hu,((ha u).symm).mul_pow]

theorem rc_pivot {x u v a t : G} (hu : rc x u = u*a) (ha : Central a)
    (n : ℕ) (he : v=u^n*t) (ht : Central t) :
    rc x v = v*a^n := by
  rw [he,map_mul,rc_pow_parts hu ha,rc_center ht,mul_assoc,←(ht (a^n)).eq,←mul_assoc]

theorem rc_power_central {x u a : G} (hu : rc x u = u*a) (ha : Central a)
    (n : ℕ) (ht : Central (u^n)) : a^n=1 := by
  have e := (rc_pow_parts hu ha n).symm.trans (rc_center ht x)
  exact mul_left_cancel (e.trans (mul_one _).symm)

theorem pivotU (h : LS G 4 = ⊥) (x y : G) (n : ℕ)
    (cub : (portU x y)^3 ∈ LS G 3) (t : G) (ht : t ∈ LS G 3)
    (hv : portV x y = (portU x y)^n*t) :
    let E := make h x y
    E.a^3 = 1 ∧ E.b=E.a^n ∧ E.d=E.a^(n*n) := by
  let E := make h x y
  change E.a^3=1 ∧ E.b=E.a^n ∧ E.d=E.a^(n*n)
  have ux : rc E.x E.u = E.u*E.a := rc_eq (by simpa only [mul_assoc] using E.ux)
  have uy : rc E.y E.u = E.u*E.b := rc_eq (by simpa only [mul_assoc] using E.uy)
  have vx : rc E.x E.v = E.v*E.b := rc_eq (by simpa only [mul_assoc] using E.vx)
  have vy : rc E.y E.v = E.v*E.d := rc_eq (by simpa only [mul_assoc] using E.vy)
  have b : E.b=E.a^n := mul_left_cancel (vx.symm.trans
    (rc_pivot ux E.ca n (show E.v=E.u^n*t from hv) (center_in_layer4 h ht)))
  have d : E.d=E.b^n := mul_left_cancel (vy.symm.trans
    (rc_pivot uy E.cb n (show E.v=E.u^n*t from hv) (center_in_layer4 h ht)))
  exact ⟨rc_power_central ux E.ca 3 (center_in_layer4 h cub),b,by rw [d,b,pow_mul]⟩

theorem pivotV (h : LS G 4 = ⊥) (x y : G)
    (cub : (portV x y)^3 ∈ LS G 3) (hu : portU x y ∈ LS G 3) :
    let E := make h x y
    E.d^3 = 1 ∧ E.a=1 ∧ E.b=1 := by
  let E := make h x y
  change E.d^3=1 ∧ E.a=1 ∧ E.b=1
  have ux : rc E.x E.u = E.u*E.a := rc_eq (by simpa only [mul_assoc] using E.ux)
  have uy : rc E.y E.u = E.u*E.b := rc_eq (by simpa only [mul_assoc] using E.uy)
  have vy : rc E.y E.v = E.v*E.d := rc_eq (by simpa only [mul_assoc] using E.vy)
  exact ⟨rc_power_central vy E.cd 3 (center_in_layer4 h cub),
    mul_left_cancel (ux.symm.trans ((rc_center (center_in_layer4 h hu) E.x).trans (mul_one _).symm)),
    mul_left_cancel (uy.symm.trans ((rc_center (center_in_layer4 h hu) E.y).trans (mul_one _).symm))⟩

end HaarP3LayerGen

#print axioms HaarP3LayerGen.pivotU
#print axioms HaarP3LayerGen.pivotV
