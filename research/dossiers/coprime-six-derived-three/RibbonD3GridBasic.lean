import RibbonD3Closure

namespace RibbonD3Grid
open RibbonDerived3
open scoped commutatorElement
variable {G : Type*} [Group G]

def trans (x y : G) (i j : ℤ) : G := y ^ j * x ^ i

def edge (x y : G) (i j : ℤ) : G :=
  trans x y i j * y * (trans x y i (j+1))⁻¹

theorem hor_pos (x y : G) (i j : ℤ) :
    trans x y i j * x = trans x y (i+1) j := by
  simp [trans,zpow_add_one,mul_assoc]

theorem hor_neg (x y : G) (i j : ℤ) :
    trans x y i j * x⁻¹ = trans x y (i-1) j := by
  simp [trans,zpow_sub_one,mul_assoc]

theorem ver_pos (x y : G) (i j : ℤ) :
    trans x y i j * y = edge x y i j * trans x y i (j+1) := by
  simp [edge,mul_assoc]

theorem ver_neg (x y : G) (i j : ℤ) :
    trans x y i j * y⁻¹ = (edge x y i (j-1))⁻¹ * trans x y i (j-1) := by
  simp [edge,mul_assoc]

@[simp] theorem edge_axis (x y : G) (j : ℤ) : edge x y 0 j = 1 := by
  simp [edge,trans,zpow_add_one]

theorem edge_derived (x y : G) (i j : ℤ) : edge x y i j ∈ Derived G := by
  have H : ⁅x^i,y⁆ ∈ Derived G := Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _)
  have T := (inferInstance : (Derived G).Normal).conj_mem _ H (y^j)
  simpa [edge,trans,commutatorElement_def,zpow_add_one,mul_inv_rev,mul_assoc] using T

#print axioms edge_derived
end RibbonD3Grid
