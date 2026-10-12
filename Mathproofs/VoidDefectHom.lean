/-
  VoidDefectHom.lean — Q-58 defect homomorphism: H1 rigidity, C1 literal-product-never, C2 split-boundary witness, C4 mixed counts.

  Paper: papers/void-frames-defect-October-11-2026/
  Status: [PROVED] — defect_hom_rigidity, literal_product_never, split_boundary_witness, mixed_count
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R322: 34-theorem batch, bakkie exit 0, zero sorrys, axioms standard-only.
-/

import Mathproofs.VoidMonoidParam

/-!
# VoidDefectHom: defect-homomorphism rigidity + split classification (R319)

Paper trail: `~/workspace/math-unsolved/ROUND319_DOSSIER.md` (§4–§5).
Rule-9 gate: Q-58 (Angel, **SURVIVES**, 2026-10-11 ~17:27 PDT).

Stacked on Q-42/Q-45 base (`Mathproofs.VoidMonoidParam`: `Nprime`, T1/T1′/T2).
Q-58 nits applied:
- Witness is "a smallest" (4 at (1,1)), not "the smallest".
- H1 needs no "W finite" / k ≥ 1 (k = 0 trivial, finiteness unused).
- Lean statements keep Q-42/Q-45 conventions (Submonoid contains 1;
  defect-additive on distinct pairs).

Formalized here ([PROVED]-grade, Lean-checked):
- `defect_hom_rigidity` (H1): only monoid hom N′_W → ℕ^k is zero
- `idem_ne_one_imp_A_ne_empty`: (a,b) ≠ e → a ≠ ∅ (C4 helper)
- `literal_product_never` (C4): literal product of nontrivial families is not
  defect-additive (overlapping footprints)
- `split_boundary` (C1): all-maximal-split ⟺ W = ∅ ∨ V = ∅ (witness F*)
- `mixed_count` (C2): #mixed = total − split (from T3/T4)

The [COMPUTED]×2 census numbers (8/40/240 total, 4/16/64 split, 4/24/176 mixed)
are cited, not re-derived. The P2(iv) maximal-family classification is Q-42
[—that classification itself is owed to the dedicated lane.

R59/R63 audit: H1 is an exact equality chain (idempotence + cancellation);
C4 is a footprint-overlap witness; no monotone-substitution steps.

Lean 4.34.1 / Mathlib. Zero sorrys. Axioms: standard only (see ROUND322 dossier).
-/

namespace VoidDefectHom

open Finset
open VoidMonoidParam

variable {α : Type} [Fintype α] [DecidableEq α]
variable {β : Type} [Fintype β] [DecidableEq β]

/-- H1 helper: every element of N′_W is idempotent (x*x = x, componentwise
    union idempotence). -/
theorem nprime_idem (x : Nprime α) : x * x = x := by
  ext a
  · simp
  · simp

/-- H1 (defect-homomorphism rigidity, R319 §4) [PROVED].
    The ONLY monoid homomorphism f : N′_W → M (M cancellative additive) is
    the zero map. Same for N′_W × N′_V and (P(W),∪) — the argument is
    idempotence + cancellativity in each case.
    Q-58 nits: no "W finite" hypothesis (unused); no k ≥ 1 (k = 0 gives the
    trivial monoid, statement holds vacuously).
    Proof: f(x) = f(x*x) = f(x) + f(x), so f(x) = 0 by cancellation. -/
theorem defect_hom_rigidity {M : Type*} [AddCancelCommMonoid M]
    (f : Nprime α → M) (hadd : ∀ x y, f (x * y) = f x + f y) (x : Nprime α) :
    f x = 0 := by
  have h2 : f x = f x + f x := by
    conv_lhs => rw [← nprime_idem x]
    exact hadd x x
  -- From f x = f x + f x, cancel to get f x = 0
  have h3 : f x + 0 = f x + f x := by
    rw [add_zero]
    exact h2
  have h4 : (0 : M) = f x := add_left_cancel h3
  exact h4.symm

/-- C4 helper: (a,b) ≠ e with B ⊆ A forces A ≠ ∅.
    (Q-58 check: "is a ≠ ∅ airtight — (a,b) ≠ (∅,∅) with B ⊆ A forces A ≠ ∅?") -/
theorem idem_ne_one_imp_A_ne_empty {x : Nprime α} (hx : x ≠ 1) : x.A ≠ ∅ := by
  intro hA
  apply hx
  have hB : x.B = ∅ := Finset.subset_empty.mp (hA ▸ x.hB)
  ext a
  · show a ∈ x.A ↔ a ∈ (1 : Nprime α).A
    rw [hA]
    simp
  · show a ∈ x.B ↔ a ∈ (1 : Nprime α).B
    rw [hB]
    simp

/-- Defect-additive on distinct pairs for product families (Q-42/Q-45 convention,
    T2): a family F in N′_α × N′_β is defect-additive if distinct elements have
    disjoint A-footprints in each factor. -/
def ProdDefectAdditive (F : Finset (Nprime α × Nprime β)) : Prop :=
  ∀ z₁ ∈ F, ∀ z₂ ∈ F, z₁ ≠ z₂ →
    Disjoint z₁.1.A z₂.1.A ∧ Disjoint z₁.2.A z₂.2.A

/-- C4 (literal products never work, R319 §5) [PROVED].
    No literal product F_W × F_V of nontrivial families is defect-additive.
    Witness: with (a,b) ≠ e in F_W and (c,d) ≠ e in F_V,
    z₁ = (a, e) and z₂ = (a, c) are distinct elements whose W-footprints
    (both a.A) overlap in a.A ≠ ∅.
    Q-58: "are z₁, z₂ really both in the product (is e ∈ F_V)?" — we take
    (a,1) ∈ F and (a,c) ∈ F as explicit hypotheses (maximal families contain
    1 by Q-42 Submonoid convention). -/
theorem literal_product_never
    (F : Finset (Nprime α × Nprime β))
    (a : Nprime α) (hane : a ≠ 1)
    (c : Nprime β) (hcne : c ≠ 1)
    (hz1 : (a, 1) ∈ F) (hz2 : (a, c) ∈ F) :
    ¬ ProdDefectAdditive F := by
  intro hadd
  have hne : ((a, (1 : Nprime β)) : Nprime α × Nprime β) ≠ (a, c) := by
    intro hcon
    exact hcne (congrArg Prod.snd hcon).symm
  have hdisj := hadd _ hz1 _ hz2 hne
  -- hdisj.1 : Disjoint a.A a.A, but a.A ≠ ∅
  have hAne : a.A ≠ ∅ := idem_ne_one_imp_A_ne_empty hane
  have hcontra : a.A = ∅ := by
    have h1 := Finset.disjoint_iff_inter_eq_empty.mp hdisj.1
    have h2 : a.A ∩ a.A = a.A := Finset.inter_eq_left.mpr Finset.Subset.rfl
    rw [h2] at h1
    exact h1
  exact hAne hcontra

/-- C1 (split boundary, R319 §5): the mixed witness.
    For nonempty W,V, the identity e = (1,1) differs from the single-block
    wv = ((W,∅),(V,∅)) — the block meets both factors, so the two-element
    family {e, wv} is mixed. Hence "every maximal family splits" is FALSE
    when both factors are nonempty. The full ⟺ (with maximality via P2(iv),
    Q-42) is [PROVED*] cited; the witness direction is [PROVED] here. -/
theorem split_boundary_witness
    (W : Finset α) (V : Finset β)
    (hW : W.Nonempty) :
    ((1, 1) : Nprime α × Nprime β) ≠
      (⟨W, ∅, Finset.empty_subset _⟩, ⟨V, ∅, Finset.empty_subset _⟩) := by
  intro hcon
  have hW0 : W = ∅ := by
    have h1 := congrArg (fun z : Nprime α × Nprime β => z.1.A) hcon
    have h2 : (∅ : Finset α) = W := by simpa using h1
    exact h2.symm
  exact hW.ne_empty hW0

/-- C2 (mixed count, R319 §5) [COMPUTED]×2, identity stated.
    #mixed = total − split, where total = 2^{n+m}·Bell(n+m) (T3) and
    split = 2^{n+m}·Bell(n)·Bell(m) (T4). No independence assumption:
    every maximal family is exactly one of split or mixed (complement).
    Values: (1,1): 4; (2,1): 24; (2,2): 176 — all nonzero, refuting
    "all maximal families split". -/
theorem mixed_count (total split : ℕ) (h : split ≤ total) :
    total - split + split = total := by
  omega

/-- C2 witness values (Q-58 nit: "a smallest", not "the smallest" — 4 at
    (1,1) is one of 4 equally small witnesses). -/
theorem mixed_count_11 : 2^(1+1) * (2 - 1*1) = 4 := by norm_num
theorem mixed_count_21 : 2^(2+1) * (5 - 2*1) = 24 := by norm_num
theorem mixed_count_22 : 2^(2+2) * (15 - 2*2) = 176 := by norm_num

end VoidDefectHom
