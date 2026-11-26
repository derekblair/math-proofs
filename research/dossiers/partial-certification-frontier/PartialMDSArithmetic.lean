import Mathlib.Data.Nat.Basic

namespace PartialMDSArithmetic

/-- Correction criterion on the support of one codeword difference. -/
def good (d h f b : Nat) : Prop :=
  d ≥ f + b + 1 ∧ d + (h - f) ≥ f + 2*b + 1

/-- Nonlinearity of the code does not change this monotone support test. -/
theorem support_monotone {d h f b d' h' : Nat}
    (D : d ≤ d') (H : h ≤ h') (G : good d h f b) :
    good d' h' f b := by
  unfold good at *
  omega

/-- Closed form of the parity-symbol and certificate-count frontier. -/
theorem certificate_frontier {n k h f b : Nat} (kn : k ≤ n) (kpos : 0 < k) :
    good (n-k+1) (h-(k-1)) f b ↔
      n-k ≥ f+b ∧
      (n-k ≥ f+2*b ∨ h ≥ (k-1)+f+(f+2*b-(n-k))) := by
  unfold good
  omega

/-- If not enough certified values survived for interpolation, then the
    actual residual errors and erasures are within the RS unique-decoding radius.
    At most f erasures are exogenous; all other unusable symbols and every
    erroneous opaque symbol consume distinct adversarial positions. -/
theorem decoder_radius {n k h f b e r trusted : Nat}
    (kn : k ≤ n) (kpos : 0 < k) (ht : trusted < k)
    (missing : h ≤ trusted + e)
    (errors : r ≤ b) (shared : r + e ≤ b + f)
    (frontier : good (n-k+1) (h-(k-1)) f b) :
    2*r+e ≤ n-k := by
  unfold good at frontier
  omega

/-- Exact split of the differing opaque coordinates between two worlds.
    Neither world needs more than c opaque Byzantine changes. -/
theorem split_opaque (w c : Nat) (h : w ≤ 2*c) :
    ∃ l r : Nat, l + r = w ∧ l ≤ c ∧ r ≤ c := by
  exact ⟨min w c,w-min w c,by omega,by omega,by omega⟩

end PartialMDSArithmetic

#print axioms PartialMDSArithmetic.support_monotone
#print axioms PartialMDSArithmetic.certificate_frontier
#print axioms PartialMDSArithmetic.decoder_radius
#print axioms PartialMDSArithmetic.split_opaque
