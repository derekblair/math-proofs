import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Abel

namespace SharedRepair

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The protected repair padding has zero visible repair output despite
depending on the cumulative refresh. -/
theorem repair_pad_kernel (e : A →+ B) (j : B →+ A)
    (rightInv : ∀ b, e (j b)=b) (F R : A) :
    e ((F-R)-j (e (F-R)))=0 := by
  rw [map_sub,rightInv,sub_self]

/-- Adding the pad cancels all refresh coordinates apart from the intended
public repair value. The section embeds a public scalar as a polynomial. -/
theorem masked_identity (e : A →+ B) (j : B →+ A) (f F R : A) :
    f+R+((F-R)-j (e (F-R))) =
      j (e (f+R))+(f+F)-j (e (f+F)) := by
  simp only [map_add,map_sub]
  abel

/-- Uniform fake normalized coordinates stay uniform after translation by
the private initial normalized coordinates. -/
def normalizedTranslate (z : A →+ B) (j : B →+ A)
    (rightInv : ∀ b, z (j b)=b) (f : A) : z.ker ≃ z.ker where
  toFun F := ⟨f-j (z f)+F.1, by
    change z (f-j (z f)+F.1)=0
    rw [map_add, map_sub,rightInv,sub_self, show z F.1=0 from F.2, zero_add]⟩
  invFun F := ⟨F.1-(f-j (z f)), by
    change z (F.1-(f-j (z f)))=0
    rw [map_sub, map_sub,rightInv,sub_self, show z F.1=0 from F.2, sub_self]⟩
  left_inv F := Subtype.ext (by change f-j (z f)+F.1-(f-j (z f))=F.1; abel)
  right_inv F := Subtype.ext (by change f-j (z f)+(F.1-(f-j (z f)))=F.1; abel)

#print axioms repair_pad_kernel
#print axioms masked_identity
#print axioms normalizedTranslate
end SharedRepair
