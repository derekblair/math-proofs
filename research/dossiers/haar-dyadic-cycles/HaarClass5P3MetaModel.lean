import HaarClass5P3MetaCore

namespace HaarClass5P3Meta
open HaarClass4Data
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem conjugation (a b : G) :
    rc b⁻¹ a = ⁅a,b⁆⁻¹ * a := by
  simp only [rc,MonoidHom.coe_mk,OneHom.coe_mk,inv_inv,commutatorElement_def]
  group

def of_comm (x y c u A : G)
    (cu : Commute c u) (ca : Commute c A) (ua : Commute u A)
    (xy : x*y=y*x*c) (u9 : u^(9:ℕ)=1) (A3 : A^(3:ℕ)=1)
    (cx : ⁅c,x⁆=u) (ux : ⁅u,x⁆=A) (Ax : ⁅A,x⁆=u^(-3:ℤ))
    (cy : ⁅c,y⁆=u^(2:ℕ)*A⁻¹) (uy : ⁅u,y⁆=u^(3:ℕ)*A⁻¹)
    (Ay : ⁅A,y⁆=u^(3:ℕ)) : Model G := by
  refine ⟨x,y,c,u,A,cu,ca,ua,xy,u9,A3,?_,?_,?_,?_,?_,?_⟩
  · rw [conjugation,cx,cu.inv_right.eq.symm]
  · rw [conjugation,ux,ua.inv_right.eq.symm]
  · rw [conjugation,Ax,←zpow_neg]
    simpa using (ua.pow_left 3).eq
  · rw [conjugation,cy,mul_inv_rev,inv_inv]
    have r : (u^(2:ℕ))⁻¹=u^(-2:ℤ) := by simp
    rw [r]
    simp only [mul_assoc]
    rw [((cu.zpow_right (-2)).symm).eq,←mul_assoc A c,ca.symm.eq,
      mul_assoc c A, (ua.zpow_left (-2)).symm.eq]
  · rw [conjugation,uy,mul_inv_rev,inv_inv,mul_assoc]
    have e : ((u^(3:ℕ))⁻¹)*u=u^(-2:ℤ) := by
      rw [←zpow_natCast,←zpow_neg]
      group
    rw [e, (ua.zpow_left (-2)).symm.eq]
  · rw [conjugation,Ay]
    have e : (u^(3:ℕ))⁻¹=u^(-3:ℤ) := by simp
    rw [e, (ua.zpow_left (-3)).eq]

end HaarClass5P3Meta
#print axioms HaarClass5P3Meta.of_comm
