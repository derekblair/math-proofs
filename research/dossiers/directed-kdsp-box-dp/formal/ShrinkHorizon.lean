import BoxShrink
import FiniteScale

namespace DirectedBoxDSP

variable {F : Type*} [Fintype F]

/-- A common finite depth works for every cut history obeying the geometric
longest-side rule, for a fixed initial bound and a positive target scale. -/
theorem uniform_shrink_horizon (W ε : ℝ) (hW : 0 < W) (hε : 0 < ε) :
    ∃ depth : ℕ,
      ∀ (w : ℕ → F → ℝ) (s : ℕ → F),
      (∀ f, w 0 f ≤ W) →
      (∀ n f, w (n+1) f ≤ w n f) →
      (∀ n f, w n f ≤ w n (s n)) →
      (∀ n, w (n+1) (s n) ≤ (2/3 : ℝ) * w n (s n)) →
      ∀ f, w depth f < ε := by
  obtain ⟨m, hm⟩ := contraction_below W ε hW hε
  let d := Fintype.card F
  refine ⟨m*d, ?_⟩
  intro w s h0 mono largest cut f
  have h (n : ℕ) : ∀ a, w (n*d) a ≤ (2/3 : ℝ)^n * W := by
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      intro a
      have step := longest_side_block_shrink
        (fun t => w (n*d+t)) (fun t => s (n*d+t)) ((2/3 : ℝ)^n * W)
        (by simpa using ih)
        (fun t f => by simpa only [Nat.add_assoc] using mono (n*d+t) f)
        (fun t f => largest (n*d+t) f)
        (fun t => by simpa only [Nat.add_assoc] using cut (n*d+t)) a
      change w (n*d+d) a ≤ (2/3 : ℝ) * ((2/3 : ℝ)^n * W) at step
      rw [Nat.succ_mul, pow_succ']
      simpa only [mul_assoc] using step
  exact (h m f).trans_lt hm

#print axioms uniform_shrink_horizon
end DirectedBoxDSP
