/-
  VoidMonoidParam.lean — R300/R303 parameterized void-frame monoid N′_W: defect formula, defect-0 core, fully-additive submonoid, Φ/Ψ/Rho product machinery. BUILD DEPENDENCY of VoidMonoid and VoidDefectHom.

  Paper: papers/void-frames-defect-October-11-2026/
  Status: [PROVED*] (staged verification — build-clean, gate-passed; promotion to [PROVED] pending coordinator call) — additive_iff_disjoint (P1), defect_core (P2i), fully_additive_submonoid (P2ii), disjoint_footprint_submonoid (P2iii-a), Phi_*/Rho_* (T1/T1′), prod_additive_iff (T2)
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R314: Q-42 + Q-45 SURVIVES, bakkie `lake build` exit 0, zero sorrys, axioms standard-only.
-/

/-
  VoidMonoidParam.lean — Lean formalization of R300's parameterized defect
  calculus (P1, P2(i)–(iii)(a)) and R303's product theory (T1, T1′, T2).

  Sources: ~/workspace/math-unsolved/ROUND300_DOSSIER.md (§1–§2),
           Q-45 spec /Agents/Projects/math-research/r303-defect-product-review-spec.md.

  Rule-9 gates: Q-42 quoted SURVIVES (2026-10-11, Angel; transcript
  /Agents/Projects/math-research/r300-review-transcript.md) — P1/P2 gate-passed.
  Q-45 quoted SURVIVES (2026-10-11, Angel; transcript
  /Agents/Projects/math-research/r303-review-transcript.md) — T1/T1′/T2
  gate-passed (T3/T4/H1/H3 gate-passed too; formalization owed to a dedicated
  lane — see "Owed" below).

  Q-41-OPEN base note: this module is SELF-CONTAINED — N′_W, d, P1, P2 are
  proved from scratch for arbitrary finite W. It does NOT touch R296's D2(c)
  wording (the Q-41-gated item) and does not depend on it: P2(iv)(c)'s closure
  argument cites only P2(iii), not D2(c) wording (R300 dossier §7). The
  W={2,3,4} defect-core base was never folded in Lean, so nothing here rewrites
  a Q-41-gated file.

  Reviewer conventions honored (Q-42/Q-45 nits):
  - Mathlib `Submonoid` (contains the ambient 1) — P2(iii) under this convention.
  - "Defect-additive family" (used only in the owed P2(iv)/T3) means additive
    on DISTINCT pairs; ordered-pair counts (5^n) include the diagonal — the
    two conventions are labeled separately wherever they appear.
  - T1's Φ is stated on `Finset (α ⊕ β)` via `Sum.inl`/`Sum.inr` preimages
    (Q-45 nit), not literal ∩. Note: this Mathlib's `Finset.preimage` takes
    `Set.InjOn f (f ⁻¹' ↑s)`, so we use `(Sum.inl_injective.injOn)`.
  - n = 0 in P2(iv)(c) is the k = 0 family {e} (owed with P2(iv)).

  Honesty labels:
  - defect_op, additive_iff_disjoint (P1): [PROVED*] hand proof, Lean-checked.
  - defect_core (P2(i)), fully_additive_submonoid (P2(ii)),
    disjoint_footprint_submonoid (P2(iii)(a)): [PROVED*], Lean-checked.
  - Phi_mul, Phi_defect, Phi_Psi, Psi_Phi (T1): [PROVED*], Lean-checked.
  - Rho_mul, Rho_injective_on, Rho_defect, Rho_image_agree (T1′):
    [PROVED*], Lean-checked.
  - prod_additive_iff (T2): [PROVED*], Lean-checked.
  - Owed (gate-passed, NOT formalized here — dedicated lane): P2(iii)(b) 3^n
    count, P2(iv) annotated-partition classification + 2^n·Bell(n) counts,
    T3 maximal-family transport, T4 split/mixed counts, H1 defect-homomorphism
    rigidity (classical — recorded, not claimed, like R291's M2), H3
    defect-exact classification, T1′ image ⊇ characterization. The
    [COMPUTED]×2 census numbers are cited, never re-claimed.

  R59/R63 audit: every direction-sensitive step is an exact equality
  (Finset.card_union, inclusion–exclusion); zero "by inspection" monotone
  substitutions.

  Lean 4.34.1 / Mathlib. Zero sorrys. Axioms: standard only (see axiom audit
  in ROUND314_DOSSIER.md).
-/

import Mathlib

open Finset

namespace VoidMonoidParam

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The parameterized annotated void-frame monoid N′_W (R300 §1):
    pairs (A,B) of finsets with B ⊆ A, under componentwise union. -/
@[ext]
structure Nprime (α : Type) [Fintype α] [DecidableEq α] where
  A : Finset α
  B : Finset α
  hB : B ⊆ A

namespace Nprime

/-- Local helper: s ⊆ ∅ → s = ∅. -/
theorem subset_empty_eq {s : Finset α} (h : s ⊆ ∅) : s = ∅ :=
  Finset.eq_empty_of_forall_notMem (fun x hx => Finset.notMem_empty x (h hx))

/-- Local helper: s ⊆ t → s ∩ t = s. -/
theorem inter_eq_self_of_subset {s t : Finset α} (h : s ⊆ t) : s ∩ t = s := by
  ext a
  simp only [Finset.mem_inter]
  exact ⟨fun hx => hx.1, fun ha => ⟨ha, h ha⟩⟩

/-- Local helper: s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u. -/
theorem inter_union_distrib (s t u : Finset α) :
    s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_union]
  tauto

/-- Local helper: (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u. -/
theorem union_inter_distrib (s t u : Finset α) :
    (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_union]
  tauto

instance : Mul (Nprime α) where
  mul x y := ⟨x.A ∪ y.A, x.B ∪ y.B, Finset.union_subset_union x.hB y.hB⟩

instance : One (Nprime α) where
  one := ⟨∅, ∅, Finset.empty_subset _⟩

@[simp] theorem mul_A (x y : Nprime α) : (x * y).A = x.A ∪ y.A := rfl
@[simp] theorem mul_B (x y : Nprime α) : (x * y).B = x.B ∪ y.B := rfl
@[simp] theorem one_A : (1 : Nprime α).A = ∅ := rfl
@[simp] theorem one_B : (1 : Nprime α).B = ∅ := rfl

instance : CommMonoid (Nprime α) where
  mul_assoc x y z := by
    refine Nprime.ext ?_ ?_ <;> simp [mul_A, mul_B, Finset.union_assoc]
  one_mul x := by
    refine Nprime.ext ?_ ?_ <;> simp [mul_A, mul_B]
  mul_one x := by
    refine Nprime.ext ?_ ?_ <;> simp [mul_A, mul_B]
  mul_comm x y := by
    refine Nprime.ext ?_ ?_ <;> simp [mul_A, mul_B, Finset.union_comm]

/-- Every element is idempotent (componentwise union). -/
@[simp] theorem mul_self (x : Nprime α) : x * x = x := by
  refine Nprime.ext ?_ ?_ <;> simp [mul_A, mul_B, Finset.union_self]

/-- The defect datum d(A,B) = (|A|, 0, |A|) ∈ ℕ³ (R291/R300). -/
def d (x : Nprime α) : ℕ × ℕ × ℕ := (x.A.card, 0, x.A.card)

/-- P1 (R300): parameterized defect formula.
    d(x⊕y) = d(x)+d(y) − (|A₁∩A₂|, 0, |A₁∩A₂|), stated on the |A|-component.
    The ℕ-subtraction is exact since |A₁∩A₂| ≤ |A₁|. -/
theorem defect_op (x y : Nprime α) :
    (d (x * y)).1 = (d x).1 + (d y).1 - (x.A ∩ y.A).card := by
  simp only [d, mul_A]
  exact Finset.card_union _ _

/-- P1 corollary: d is additive on the pair (x,y) ⟺ footprints are disjoint.
    Diagonal included: (x,x) is additive only for x = e (cf. P2(ii)). -/
theorem additive_iff_disjoint (x y : Nprime α) :
    (x * y).A.card = x.A.card + y.A.card ↔ x.A ∩ y.A = ∅ := by
  have hle : (x.A ∩ y.A).card ≤ x.A.card :=
    Finset.card_le_card Finset.inter_subset_left
  rw [mul_A, Finset.card_union]
  constructor
  · intro h
    have h0 : (x.A ∩ y.A).card = 0 := by omega
    exact Finset.card_eq_zero.mp h0
  · intro h
    rw [h, Finset.card_empty, Nat.sub_zero]

/-- Helper: x ≠ 1 ⟹ footprint nonempty (B ⊆ A: A = ∅ forces x = e). -/
theorem ne_one_imp_A_ne_empty {x : Nprime α} (hx : x ≠ 1) : x.A ≠ ∅ := by
  intro hA0
  apply hx
  have hB0 : x.B = ∅ := subset_empty_eq (hA0 ▸ x.hB)
  refine Nprime.ext ?_ ?_
  · simpa using hA0
  · simpa using hB0

/-- P2(i) (R300): the defect-0 core is the identity, for all finite W
    (including W = ∅). -/
theorem defect_core (x : Nprime α) : d x = (0, 0, 0) ↔ x = 1 := by
  constructor
  · intro h
    have hcard : x.A.card = 0 := by
      have h1 := congrArg Prod.fst h
      simpa [d] using h1
    have hA : x.A = ∅ := Finset.card_eq_zero.mp hcard
    have hB : x.B = ∅ := subset_empty_eq (hA ▸ x.hB)
    refine Nprime.ext ?_ ?_
    · simpa using hA
    · simpa using hB
  · intro h
    rw [h]; rfl

/-- P2(ii) (R300): the only submonoid on which d is additive on ALL ordered
    pairs (including the diagonal) is {e}. The obstruction is exactly the
    diagonal: x⊕x = x forces d(x) = 2d(x). -/
theorem fully_additive_submonoid (S : Submonoid (Nprime α))
    (hadd : ∀ x y : Nprime α, x ∈ S → y ∈ S → (x * y).A.card = x.A.card + y.A.card) :
    S = ⊥ := by
  rw [Submonoid.eq_bot_iff_forall]
  intro x hx
  have hxx := hadd x x hx hx
  rw [mul_self] at hxx
  have h0 : x.A.card = 0 := by omega
  have hA : x.A = ∅ := Finset.card_eq_zero.mp h0
  have hB : x.B = ∅ := subset_empty_eq (hA ▸ x.hB)
  refine Nprime.ext ?_ ?_
  · simpa using hA
  · simpa using hB

/-- P2(iii)(a) (R300): a submonoid with pairwise-disjoint footprints has at
    most one non-identity element. Mathlib `Submonoid` convention: contains
    the ambient 1 (Q-42 nit). -/
theorem disjoint_footprint_submonoid (S : Submonoid (Nprime α))
    (hdisj : ∀ x y : Nprime α, x ∈ S → y ∈ S → x ≠ y → x.A ∩ y.A = ∅) :
    ∀ x y : Nprime α, x ∈ S → y ∈ S → x ≠ 1 → y ≠ 1 → x = y := by
  intro x y hx hy hnx hny
  by_contra hne
  have hxy : x * y ∈ S := S.mul_mem hx hy
  have hinter : x.A ∩ y.A = ∅ := hdisj x y hx hy hne
  have hAx : x.A ≠ ∅ := ne_one_imp_A_ne_empty hnx
  -- x.A ∩ (x*y).A = x.A
  have key : x.A ∩ (x * y).A = x.A := by
    rw [mul_A]
    exact inter_eq_self_of_subset Finset.subset_union_left
  rcases eq_or_ne (x * y) x with h1 | h1
  · -- x*y = x: then y.A ⊆ x.A, and disjointness forces y.A = ∅, so y = e.
    have hsub : y.A ⊆ x.A := by
      have hA1 := congrArg Nprime.A h1
      simp only [mul_A] at hA1
      intro a ha
      have hmem : a ∈ x.A ∪ y.A := Finset.mem_union.mpr (Or.inr ha)
      rw [hA1] at hmem
      exact hmem
    have hyA : y.A = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      have hmem : a ∈ x.A ∩ y.A := Finset.mem_inter.mpr ⟨hsub ha, ha⟩
      rw [hinter] at hmem
      exact Finset.notMem_empty a hmem
    apply hny
    have hB0 : y.B = ∅ := subset_empty_eq (hyA ▸ y.hB)
    refine Nprime.ext ?_ ?_
    · simpa using hyA
    · simpa using hB0
  · rcases eq_or_ne (x * y) y with h2 | h2
    · -- symmetric: x*y = y forces x = e.
      have hsub : x.A ⊆ y.A := by
        have hA2 := congrArg Nprime.A h2
        simp only [mul_A] at hA2
        intro a ha
        have hmem : a ∈ x.A ∪ y.A := Finset.mem_union.mpr (Or.inl ha)
        rw [hA2] at hmem
        exact hmem
      have hxA : x.A = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro a ha
        have hmem : a ∈ x.A ∩ y.A := Finset.mem_inter.mpr ⟨ha, hsub ha⟩
        rw [hinter] at hmem
        exact Finset.notMem_empty a hmem
      apply hnx
      have hB0 : x.B = ∅ := subset_empty_eq (hxA ▸ x.hB)
      refine Nprime.ext ?_ ?_
      · simpa using hxA
      · simpa using hB0
    · -- x*y ∉ {x,y}: (x, x*y) is a distinct pair in S whose footprints
      -- meet in x.A ≠ ∅ — contradicting disjointness.
      have hdist : x ≠ x * y := fun he => h1 he.symm
      have hcontra := hdisj x (x * y) hx hxy hdist
      rw [key] at hcontra
      exact hAx hcontra

/-! ## T1: product–disjoint-union defect isomorphism (R303)

Φ : N′_{α⊕β} → N′_α × N′_β, Φ(A,B) = ((preim inl A, preim inl B),
(preim inr A, preim inr B)). -/

variable {β : Type} [Fintype β] [DecidableEq β]

/-- `Sum.inl`/`Sum.inr` with pinned types (avoids ambiguous `?β` metavariables). -/
private abbrev inlAB : α → α ⊕ β := Sum.inl
private abbrev inrAB : β → α ⊕ β := Sum.inr

/-- T1: Φ on `Finset (α ⊕ β)` via `Sum.inl`/`Sum.inr` preimages (Q-45 nit).
    This Mathlib's `Finset.preimage` needs `Set.InjOn`, not `Function.Injective`
    (and is noncomputable). -/
noncomputable def Phi (x : Nprime (α ⊕ β)) : Nprime α × Nprime β :=
  (⟨x.A.preimage inlAB (Sum.inl_injective.injOn),
    x.B.preimage inlAB (Sum.inl_injective.injOn),
    fun b hb => Finset.mem_preimage.mpr (x.hB (Finset.mem_preimage.mp hb))⟩,
   ⟨x.A.preimage inrAB (Sum.inr_injective.injOn),
    x.B.preimage inrAB (Sum.inr_injective.injOn),
    fun b hb => Finset.mem_preimage.mpr (x.hB (Finset.mem_preimage.mp hb))⟩)

/-- T1: Ψ, the inverse of Φ. -/
def Psi (z : Nprime α × Nprime β) : Nprime (α ⊕ β) :=
  ⟨Finset.image inlAB z.1.A ∪ Finset.image inrAB z.2.A,
   Finset.image inlAB z.1.B ∪ Finset.image inrAB z.2.B,
   by
     intro c hc
     simp only [Finset.mem_union, Finset.mem_image] at hc ⊢
     rcases hc with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
     · exact Or.inl ⟨b, z.1.hB hb, rfl⟩
     · exact Or.inr ⟨b, z.2.hB hb, rfl⟩⟩

theorem preimage_inl_image_union (A₁ : Finset α) (A₂ : Finset β) :
    (Finset.image inlAB A₁ ∪ Finset.image inrAB A₂).preimage inlAB
      (Sum.inl_injective.injOn) = A₁ := by
  ext b
  simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · have hab : a = b := Sum.inl_injective h
      subst hab
      exact ha
    · simp at h
  · intro hb
    exact Or.inl ⟨b, hb, rfl⟩

theorem preimage_inr_image_union (A₁ : Finset α) (A₂ : Finset β) :
    (Finset.image inlAB A₁ ∪ Finset.image inrAB A₂).preimage inrAB
      (Sum.inr_injective.injOn) = A₂ := by
  ext b
  simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · simp at h
    · have hab : a = b := Sum.inr_injective h
      subst hab
      exact ha
  · intro hb
    exact Or.inr ⟨b, hb, rfl⟩

/-- Every finset of α⊕β splits over inl/inr. -/
theorem sum_split (s : Finset (α ⊕ β)) :
    s = Finset.image inlAB (s.preimage inlAB (Sum.inl_injective.injOn)) ∪
        Finset.image inrAB (s.preimage inrAB (Sum.inr_injective.injOn)) := by
  ext c
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_preimage]
  constructor
  · intro hc
    rcases c with a | b
    · exact Or.inl ⟨a, hc, rfl⟩
    · exact Or.inr ⟨b, hc, rfl⟩
  · rintro (⟨a, ha, h⟩ | ⟨b, ha, h⟩)
    · rw [← h]; exact ha
    · rw [← h]; exact ha

/-- T1: Φ is a monoid homomorphism. -/
theorem Phi_mul (x y : Nprime (α ⊕ β)) : Phi (x * y) = Phi x * Phi y := by
  have hpre : ∀ s t : Finset (α ⊕ β),
      (s ∪ t).preimage inlAB (Sum.inl_injective.injOn)
        = s.preimage inlAB (Sum.inl_injective.injOn) ∪
          t.preimage inlAB (Sum.inl_injective.injOn) := by
    intro s t
    ext b
    simp [Finset.mem_preimage, Finset.mem_union]
  have hpre' : ∀ s t : Finset (α ⊕ β),
      (s ∪ t).preimage inrAB (Sum.inr_injective.injOn)
        = s.preimage inrAB (Sum.inr_injective.injOn) ∪
          t.preimage inrAB (Sum.inr_injective.injOn) := by
    intro s t
    ext b
    simp [Finset.mem_preimage, Finset.mem_union]
  have e1 : (Phi x * Phi y).1 = (Phi x).1 * (Phi y).1 := rfl
  have e2 : (Phi x * Phi y).2 = (Phi x).2 * (Phi y).2 := rfl
  refine Prod.ext (Nprime.ext ?_ ?_) (Nprime.ext ?_ ?_) <;>
    simp [Phi, mul_A, mul_B, hpre, hpre', e1, e2]

/-- T1: Φ preserves the defect datum: d_{α⊕β} = (d_α + d_β) ∘ Φ. -/
theorem Phi_defect (x : Nprime (α ⊕ β)) :
    (d x).1 = (d (Phi x).1).1 + (d (Phi x).2).1 := by
  simp only [d, Phi]
  have hunion := sum_split x.A
  have hdisj : Disjoint
      (Finset.image inlAB (x.A.preimage inlAB (Sum.inl_injective.injOn)))
      (Finset.image inrAB (x.A.preimage inrAB (Sum.inr_injective.injOn))) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc1
    obtain ⟨b, _, h⟩ := Finset.mem_image.mp hc2
    simp at h
  -- `nth_rewrite 1`: rewriting all occurrences would also rewrite `x.A`
  -- inside the `Set.InjOn` proofs of the preimages (dependent motive failure).
  nth_rewrite 1 [hunion]
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective]

/-- T1: Φ ∘ Ψ = id (by definitional unfolding + the preimage lemmas). -/
theorem Phi_Psi (z : Nprime α × Nprime β) : Phi (Psi z) = z := by
  refine Prod.ext (Nprime.ext ?_ ?_) (Nprime.ext ?_ ?_)
  · exact preimage_inl_image_union _ _
  · exact preimage_inl_image_union _ _
  · exact preimage_inr_image_union _ _
  · exact preimage_inr_image_union _ _

/-- T1: Ψ ∘ Φ = id (by definitional unfolding + sum_split). -/
theorem Psi_Phi (x : Nprime (α ⊕ β)) : Psi (Phi x) = x := by
  refine Nprime.ext ?_ ?_
  · exact (sum_split x.A).symm
  · exact (sum_split x.B).symm

/-! ## T1′: overlap correction (R303)

ρ : N′_α → N′_α × N′_α, ρ(A,B) = ((A∩W,B∩W),(A∩V,B∩V)).
W, V are explicit def parameters (Lean does not auto-include `variable`s that
occur only in a definition's body, not its type).
Injective on {x | x.A ⊆ W ∪ V}; defect identity with |A∩W∩V| correction. -/

/-- T1′: the overlap restriction map ρ. -/
def Rho (W V : Finset α) (x : Nprime α) : Nprime α × Nprime α :=
  (⟨x.A ∩ W, x.B ∩ W, Finset.inter_subset_inter x.hB (Finset.Subset.refl W)⟩,
   ⟨x.A ∩ V, x.B ∩ V, Finset.inter_subset_inter x.hB (Finset.Subset.refl V)⟩)

/-- T1′: ρ is a monoid homomorphism. -/
theorem Rho_mul (W V : Finset α) (x y : Nprime α) :
    Rho W V (x * y) = Rho W V x * Rho W V y := by
  have e1 : (Rho W V x * Rho W V y).1 = (Rho W V x).1 * (Rho W V y).1 := rfl
  have e2 : (Rho W V x * Rho W V y).2 = (Rho W V x).2 * (Rho W V y).2 := rfl
  refine Prod.ext (Nprime.ext ?_ ?_) (Nprime.ext ?_ ?_) <;>
    simp [Rho, mul_A, mul_B, union_inter_distrib, e1, e2]

/-- T1′: ρ is injective on elements supported in W ∪ V. -/
theorem Rho_injective_on (W V : Finset α) (x y : Nprime α)
    (hx : x.A ⊆ W ∪ V) (hy : y.A ⊆ W ∪ V)
    (h : Rho W V x = Rho W V y) : x = y := by
  have eA1 := congrArg (fun z : Nprime α × Nprime α => (z.1).A) h
  have eA2 := congrArg (fun z : Nprime α × Nprime α => (z.2).A) h
  have eB1 := congrArg (fun z : Nprime α × Nprime α => (z.1).B) h
  have eB2 := congrArg (fun z : Nprime α × Nprime α => (z.2).B) h
  simp only [Rho] at eA1 eA2 eB1 eB2
  have uA : ∀ s : Finset α, s ⊆ W ∪ V → s = (s ∩ W) ∪ (s ∩ V) := by
    intro s hs
    rw [← inter_union_distrib s W V, inter_eq_self_of_subset hs]
  have hA : x.A = y.A := by
    rw [uA x.A hx, uA y.A hy, eA1, eA2]
  have hB : x.B = y.B := by
    have hxB : x.B ⊆ W ∪ V := x.hB.trans hx
    have hyB : y.B ⊆ W ∪ V := y.hB.trans hy
    rw [uA x.B hxB, uA y.B hyB, eB1, eB2]
  refine Nprime.ext ?_ ?_
  · simpa using hA
  · simpa using hB

/-- T1′: defect identity with the overlap correction. -/
theorem Rho_defect (W V : Finset α) (x : Nprime α) (hx : x.A ⊆ W ∪ V) :
    (x.A ∩ W).card + (x.A ∩ V).card = x.A.card + (x.A ∩ W ∩ V).card := by
  have h1 := Finset.card_union_add_card_inter (x.A ∩ W) (x.A ∩ V)
  have h2 : (x.A ∩ W) ∪ (x.A ∩ V) = x.A := by
    rw [← inter_union_distrib (x.A) W V, inter_eq_self_of_subset hx]
  have h3 : (x.A ∩ W) ∩ (x.A ∩ V) = x.A ∩ W ∩ V := by
    ext a
    simp only [Finset.mem_inter]
    tauto
  rw [h2, h3] at h1
  omega

/-- T1′: ρ's image lies in the agreement-on-overlap set. -/
theorem Rho_image_agree (W V : Finset α) (x : Nprime α) :
    ((Rho W V x).1.A ∩ V = (Rho W V x).2.A ∩ W) ∧
    ((Rho W V x).1.B ∩ V = (Rho W V x).2.B ∩ W) := by
  simp only [Rho]
  constructor <;> ext a <;> simp only [Finset.mem_inter] <;> tauto

/-! ## T2: product defect formula (R303)

On N′_α × N′_β with d_×(z) = d(z.1) + d(z.2): the obstruction is additive
across factors — no cross-term. -/

/-- T2: additive in each factor ⟺ additive on the product pair. -/
theorem prod_additive_iff (z₁ z₂ : Nprime α × Nprime β) :
    (z₁ * z₂).1.A.card + (z₁ * z₂).2.A.card
      = (z₁.1.A.card + z₁.2.A.card) + (z₂.1.A.card + z₂.2.A.card)
    ↔ z₁.1.A ∩ z₂.1.A = ∅ ∧ z₁.2.A ∩ z₂.2.A = ∅ := by
  have hle1 : (z₁.1.A ∩ z₂.1.A).card ≤ z₁.1.A.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hle2 : (z₁.2.A ∩ z₂.2.A).card ≤ z₁.2.A.card :=
    Finset.card_le_card Finset.inter_subset_left
  have e1 : (z₁ * z₂).1 = z₁.1 * z₂.1 := rfl
  have e2 : (z₁ * z₂).2 = z₁.2 * z₂.2 := rfl
  rw [e1, e2, mul_A, mul_A, Finset.card_union, Finset.card_union]
  constructor
  · intro h
    have c1 : (z₁.1.A ∩ z₂.1.A).card = 0 := by omega
    have c2 : (z₁.2.A ∩ z₂.2.A).card = 0 := by omega
    exact ⟨Finset.card_eq_zero.mp c1, Finset.card_eq_zero.mp c2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, Finset.card_empty, Finset.card_empty, Nat.sub_zero, Nat.sub_zero]
    omega

end Nprime

end VoidMonoidParam
