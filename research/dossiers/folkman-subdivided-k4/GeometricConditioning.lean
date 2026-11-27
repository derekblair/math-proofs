import GeometricVariance

namespace RobustFolkman.Moment
open Finset
variable {X Y Z 𝕜 : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Field 𝕜]

/-- Given the common vertex, independent randomizations with the same
conditional means give the product probability after averaging. This
lemma also applies to disjoint triangles with a trivial conditioning state. -/
theorem conditionally_constant_product
    (p : X → 𝕜) (u : X → Y → 𝕜) (v : X → Z → 𝕜)
    (f : X → Y → 𝕜) (g : X → Z → 𝕜) (a b : 𝕜)
    (p1 : (∑ x, p x)=1)
    (fa : ∀ x, (∑ y,u x y*f x y)=a)
    (gb : ∀ x, (∑ z,v x z*g x z)=b) :
    (∑ x, ∑ y, ∑ z, p x*u x y*v x z*(f x y*g x z)) = a*b := by
  calc
    _ = ∑ x, p x*((∑ y,u x y*f x y)*(∑ z,v x z*g x z)) := by
      apply sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro z _
      ring
    _ = a*b := by
      simp only [fa, gb, ←Finset.sum_mul, p1, one_mul]

#print axioms conditionally_constant_product
end RobustFolkman.Moment
