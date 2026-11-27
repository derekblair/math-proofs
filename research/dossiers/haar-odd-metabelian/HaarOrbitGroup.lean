import Mathlib.Algebra.Group.Subgroup.Ker
import HaarOrbitVoltage
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Group

namespace HaarOrbitGroup
variable {G Q : Type*} [Group G] [Group Q]
variable (f : G →* Q)
variable [hA : Fact (∀ (a b : f.ker), a*b=b*a)]
local instance kerComm : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hA.out

def transport (g : G) (a : f.ker) : f.ker :=
  ⟨g*(a:G)*g⁻¹,by
    change f (g*(a:G)*g⁻¹)=1
    have h : f (a:G)=1 := a.property
    simp [h]⟩

def conjugation (g : G) : Additive f.ker →+ Additive f.ker where
  toFun a := Additive.ofMul (transport f g a.toMul)
  map_zero' := by
    apply Subtype.ext; change g*1*g⁻¹=1; group
  map_add' a b := by
    apply Subtype.ext
    change g*((a.toMul : G)*(b.toMul : G))*g⁻¹ =
      (g*(a.toMul : G)*g⁻¹)*(g*(b.toMul : G)*g⁻¹)
    group

def offset (u v g : G) (h : f (g*u)=f v) : Additive f.ker :=
  Additive.ofMul ⟨g*u*v⁻¹,by change f (g*u*v⁻¹)=1; rw [map_mul,map_inv,h,mul_inv_cancel]⟩

def weight (u v p : G) (h : f (u*p)=f v) : Additive f.ker := offset f p v u h

theorem edge_law_order (u v u' v' s g : G)
    (base : f (u*s)=f v) (moved : f (u'*s)=f v')
    (hu : f (g*u)=f u') (hv : f (g*v)=f v') :
    weight f u' v' s moved =
      -offset f u u' g hu + conjugation f g (weight f u v s base) + offset f v v' g hv := by
  apply Subtype.ext
  change u'*s*(v')⁻¹ =
    (g*u*(u')⁻¹)⁻¹*(g*(u*s*v⁻¹)*g⁻¹)*(g*v*(v')⁻¹)
  group

include hA in
theorem edge_law (u v u' v' s g : G)
    (base : f (u*s)=f v) (moved : f (u'*s)=f v')
    (hu : f (g*u)=f u') (hv : f (g*v)=f v') :
    weight f u' v' s moved =
      conjugation f g (weight f u v s base) + offset f v v' g hv - offset f u u' g hu := by
  rw [edge_law_order f u v u' v' s g base moved hu hv]
  abel

end HaarOrbitGroup
#print axioms HaarOrbitGroup.edge_law
