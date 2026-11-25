import Mathlib

/-! # Sidon autocorrelation and distinct pair-sum fiber overlap bound (SS-005) -/

namespace FiberOverlap

def IsSidon (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → ({a, b} : Multiset ℤ) = {c, d}

def fiber (A : Finset ℤ) (s : ℤ) : Finset ℤ :=
  A.image (fun a => s - a)

theorem autocorr_le_one (A : Finset ℤ) (hA : IsSidon A) (t : ℤ) (ht : t ≠ 0) :
    ((A.image (· + t)) ∩ A).card ≤ 1 := by
  sorry

theorem fiber_overlap (A : Finset ℤ) (hA : IsSidon A) (s s' : ℤ)
    (hne : s ≠ s') :
    ((fiber A s) ∩ (fiber A s')).card ≤ 1 := by
  sorry

end FiberOverlap
