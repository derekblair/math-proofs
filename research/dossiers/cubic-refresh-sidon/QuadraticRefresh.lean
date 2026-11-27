import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

namespace QuadraticRefresh

/-- In coefficient coordinates, the refresh direction Q/X = 1+θX
    cannot be on the span of two monic quadratic vanishing polynomials
    defined over the base field. Independent of the choice of sites. -/
theorem no_base_monic_secant {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (θ : K) (outside : θ ∉ Set.range φ)
    (c₁ d₁ c₂ d₂ : F) :
    ¬ ∃ l r : K, l+r=0 ∧ l*φ c₁+r*φ c₂=1 ∧ l*φ d₁+r*φ d₂=θ := by
  intro h
  obtain ⟨l,r,h₀,h₁,h₂⟩ := h
  have R : r = -l := eq_neg_of_add_eq_zero_right (by simpa [add_comm] using h₀)
  have A : l * φ (c₁-c₂) = 1 := by
    rw [map_sub,mul_sub]
    simpa only [R,neg_mul,sub_eq_add_neg] using h₁
  have B : l * φ (d₁-d₂) = θ := by
    rw [map_sub,mul_sub]
    simpa only [R,neg_mul,sub_eq_add_neg] using h₂
  have N : φ (c₁-c₂) ≠ 0 := by
    intro z
    rw [z,mul_zero] at A
    exact zero_ne_one A
  apply outside
  refine ⟨(d₁-d₂)/(c₁-c₂),?_⟩
  rw [map_div₀,div_eq_iff N,←B]
  calc
    φ (d₁-d₂) = φ (d₁-d₂) * 1 := (mul_one _).symm
    _ = φ (d₁-d₂) * (l * φ (c₁-c₂)) := by rw [A]
    _ = l * φ (d₁-d₂) * φ (c₁-c₂) := by ring

/-- The equal-offset restriction at two distinct sites can never give
    the same monic-basis coefficient. -/
theorem offset_disagrees {K : Type*} [Field K] (p a b : K) (p₀ : p≠0)
    (ane : a≠0) (bne : b≠0) (ab : a≠b) :
    (p*a)⁻¹ ≠ (p*b)⁻¹ := by
  intro E
  have C : p*a=p*b := inv_injective E
  exact ab (mul_left_cancel₀ p₀ C)

end QuadraticRefresh

#print axioms QuadraticRefresh.no_base_monic_secant
#print axioms QuadraticRefresh.offset_disagrees
