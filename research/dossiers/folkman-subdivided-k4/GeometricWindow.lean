import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace RobustFolkman

def window (τ : ℚ) : ℚ := τ^2 - (5/6)*τ^3

/-- Explicit small-parameter algebra of the determinant-rate proof.
d₁ = I(T)-I(E); d₂ = I(H)-I(T); d₃ = I(H+triangle)-I(T);
d₄ = 2*I(T)-I(diamond); d₅ = I(T). -/
theorem geometric_window (τ k d₁ d₂ d₃ d₄ d₅ : ℚ)
    (τ0 : 0<τ) (τsmall : τ≤1/100) (control : k*τ≤1/12)
    (link : d₁≤τ^2-τ^3+k*τ^4)
    (old : 2*τ^2-τ^3-k*τ^4≤d₂)
    (fresh : 3*τ^2-2*τ^3-k*τ^4≤d₃)
    (var : d₄≤τ^2/2+k*τ^4)
    (mean : d₅≤3*τ^2/2-τ^3+k*τ^4) :
    0<window τ ∧ d₁<window τ ∧ 2*window τ<d₂ ∧ 3*window τ<d₃ ∧
      d₄<2*window τ ∧ d₅<3*window τ := by
  have cubic : 0<τ^3 := by positivity
  have sq : 0<τ^2 := by positivity
  have ck := mul_le_mul_of_nonneg_right control cubic.le
  have small := mul_le_mul_of_nonneg_right τsmall sq.le
  unfold window
  constructor
  · nlinarith only [small,sq]
  constructor
  · nlinarith only [ck,link,cubic]
  constructor
  · nlinarith only [ck,old,cubic]
  constructor
  · nlinarith only [ck,fresh,cubic]
  constructor
  · nlinarith only [ck,small,var,sq]
  · nlinarith only [ck,small,mean,sq]

#print axioms geometric_window
end RobustFolkman
