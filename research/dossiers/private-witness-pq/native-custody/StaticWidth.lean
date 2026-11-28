import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

namespace NativeThresholdRamp

private theorem sum_le_length_mul (l : List Nat) (p : Nat)
    (hb : ∀ x∈l, x≤p) : l.sum≤l.length*p := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    have h1 := hb x (by simp)
    have h2 := ih (fun a ha=>hb a (by simp [ha]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private theorem length_mul_le_sum (l : List Nat) (p : Nat)
    (hb : ∀ x∈l, p≤x) : l.length*p≤l.sum := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    have h1 := hb x (by simp)
    have h2 := ih (fun a ha=>hb a (by simp [ha]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Exact integer width cut, conditional on the entropy inequality that
the sum of the shortest retained responder widths is at least H. -/
theorem fixed_width_cut (H : Nat) (short long : List Nat)
    (P : 0<short.length) (entropyCut : H≤short.sum)
    (sortedSplit : ∀ a∈short, ∀ b∈long, a≤b) :
    H + long.length*((H+short.length-1)/short.length) ≤ (short++long).sum := by
  have h : ∀ b∈long, (H+short.length-1)/short.length≤b := by
    intro b hb
    have hu : H≤short.length*b := Nat.le_trans entropyCut
      (sum_le_length_mul short b (fun a ha=>sortedSplit a ha b hb))
    rw [Nat.div_le_iff_le_mul P, Nat.mul_comm b short.length]
    omega
  have hlong := length_mul_le_sum long _ h
  rw [List.sum_append]
  omega

theorem example_cut : 512+63*((512+22-1)/22)=8*253 ∧ 85*24=8*255 := by decide +kernel

#print axioms fixed_width_cut
#print axioms example_cut
end NativeThresholdRamp
