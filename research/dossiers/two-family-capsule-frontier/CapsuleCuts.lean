import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace CapsuleCuts

/-- At least one threshold is valid iff both family-complement cuts
strictly outlast the worst availability loss. -/
theorem threshold_iff (e₁ e₂ v₁ v₂ loss : ℕ) :
    (∃ t : ℕ, e₂+v₁<t ∧ e₁+v₂<t ∧ t+loss≤e₁+e₂) ↔
    v₁+loss+1≤e₁ ∧ v₂+loss+1≤e₂ := by
  constructor
  · rintro ⟨t,h₁,h₂,ht⟩
    omega
  · rintro ⟨h₁,h₂⟩
    exact ⟨max (e₂+v₁) (e₁+v₂)+1,by omega,by omega,by omega⟩

/-- With fewer than 2a domains, a flat low-worst-loss multiplicity profile
cannot carry both required family masses. -/
theorem sparse_contradiction (a n s δ e₁ e₂ : ℕ)
    (nsmall : n<2*a) (used : s≤n) (mass : e₁+e₂=s+δ)
    (first : a+δ≤e₁) (second : a+δ≤e₂) : False := by omega

/-- Averaging the largest c and f entries rules out a weighted uniform
threshold below c+2f+1 endpoints. The top-sum averaging facts are inputs. -/
theorem weighted_average_cut (n c f e₁ e₂ v₁ v₂ loss : ℕ) (hn : 0<n)
    (x₁ : c*e₁ ≤ n*v₁) (x₂ : c*e₂ ≤ n*v₂)
    (xL : f*(e₁+e₂) ≤ n*loss)
    (h₁ : v₁+loss+1≤e₁) (h₂ : v₂+loss+1≤e₂) :
    c+2*f<n := by
  by_contra hc
  have h := Nat.mul_le_mul_right (e₁+e₂) (Nat.le_of_not_gt hc)
  have p₁ := Nat.mul_le_mul_left n h₁
  have p₂ := Nat.mul_le_mul_left n h₂
  nlinarith

/-- The separated construction preserves at least c+1 coordinates of each
family after f outages, exactly enough for its selected threshold. -/
theorem separated_recovery (c f dropped : ℕ) (hd : dropped≤f) :
    c+1 ≤ c+f+1-dropped := by omega

example :
    (2*(2+2+1) : ℕ)=10 ∧ 2*(2+2*2+1)=14 ∧
    (2+2+1 : ℕ) ≤ 8 ∧ 2+2*2+1≤8 ∧ 8<2*(2+2+1) := by decide

#print axioms threshold_iff
#print axioms sparse_contradiction
#print axioms weighted_average_cut
#print axioms separated_recovery
end CapsuleCuts
