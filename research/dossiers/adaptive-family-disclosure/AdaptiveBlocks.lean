import Mathlib.Data.Finset.Card

namespace AdaptiveBlocks
open Finset

variable {V : Type*} [DecidableEq V]

/-- Exact proof-catalog support at the minimum number of domains. -/
theorem support_at_cut {U C W : Finset V} {f : ℕ}
    (hCU : C ⊆ U) (hWU : W ⊆ U) (hdisj : Disjoint W C)
    (hcut : U.card = C.card + (f + 1)) (hW : f + 1 ≤ W.card) :
    W = U \ C := by
  have hsub : W ⊆ U \ C := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hWU hx, fun hc => (Finset.disjoint_left.mp hdisj hx hc)⟩
  have hd := Finset.card_sdiff_of_subset hCU
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

/-- One replicated block is available after any f outages. -/
theorem survives {B F : Finset V} {f : ℕ} (hB : f + 1 ≤ B.card)
    (hF : F.card ≤ f) : (B \ F).Nonempty := by
  by_contra h
  have hsub : B ⊆ F := by
    intro x hx
    by_contra hnot
    exact h ⟨x, Finset.mem_sdiff.mpr ⟨hx, hnot⟩⟩
  have := Finset.card_le_card hsub
  omega

/-- Abstract obstruction to a support of at most f at exact correctness. -/
theorem support_large {S : Type*} {U W : Finset V} {f : ℕ} {s₀ s₁ : S}
    (hne : s₀ ≠ s₁)
    (decode : Finset V → S)
    (hcorrect₀ : ∀ E : Finset V, E.card ≤ f → decode (U \ E) = s₀)
    (hcorrect₁ : W.card ≤ f → decode (U \ W) = s₁) :
    f + 1 ≤ W.card := by
  by_contra hh
  have h : W.card ≤ f := by omega
  exact hne ((hcorrect₀ W h).symm.trans (hcorrect₁ h))

#print axioms support_at_cut
#print axioms survives
#print axioms support_large

end AdaptiveBlocks
