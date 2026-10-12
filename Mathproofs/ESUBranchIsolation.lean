/-
  ESUBranchIsolation.lean — R163/R174 u-branch isolation: L1 isolation lemma, closed-image disjointness, u-side degree bound, H-clique bound.

  Paper: papers/sieve-inverse-branch-isolation-October-11-2026/
  Status: [PROVED] — uBranch_isolation, closeImage_disjoint_of_subset, uSide_degree_bound, r163_uSideBound_inHclique
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); bakkie `lake build` exit 0, zero sorrys, axioms standard-only.
-/

-- R174 (2026-10-08): Lean formalization of R163's L1 (u-branch isolation) and
-- u-side degree bound [PROVED*] → [PROVED].
--
-- R163 §A: C maximal H(u,v)-clique (H-clique = edgeless under H-adjacency),
-- d(u)=6, d(v)=7, V₀ = N(v)∖{u} (|V₀|=6), U₀ = N(u)∖{v} (|U₀|=5),
-- Z₀ = {c ∈ C ∖ V₀ : N(c) ∩ V₀ = ∅}, R145 trichotomy:
--   Z₀^close = {z ∈ Z₀ : N(z) ∩ U₀ ≠ ∅} with unique U₀-neighbour φ(z) (C₄-ban),
--   Z₀^mid  = Z₀ ∩ U₀,
--   Z₀^far  = {z ∈ Z₀ : dist(u,z) ≥ 3}.
--
-- L1: for z ∈ Z₀^close, φ(z) ∉ C (else z−φ(z) is an edge inside the edgeless
-- H-clique C). Corollary: φ(Z₀^close) ∩ Z₀^mid = ∅ since Z₀^mid ⊆ C.
--
-- U-side bound: |Z₀^close| + |Z₀^mid| ≤ |U₀| = d(u)−1, via φ injective on
-- close (R145) with image disjoint from mid (L1). This is the essential use
-- of d(u) < d(v): the u-fed part of Z₀ is strictly smaller than the
-- v-branch pool |V₀| = d(v)−1 = 6.
--
-- Formalized abstractly (pure combinatorics, no ES machinery): an H-clique
-- is a Finset with no internal Adj edges; φ is any map injective on the
-- close set. Every declaration takes its parameters as explicit binders
-- (per the Mathproofs convention).
--
-- Hand proofs: ~/workspace/math-unsolved/ROUND163_DOSSIER.md §A.

import Mathlib

open Finset

namespace ESUBranchIsolation

/-- An H-clique: edgeless under H-adjacency (R163 §A setup: H-adjacency ⟹ ¬Adj,
    so C is edgeless). -/
def IsHclique {V : Type*} [DecidableEq V] (Adj : V → V → Prop) (C : Finset V) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ¬ Adj x y

/-- R163 Lemma L1 (u-branch isolation): for z ∈ Z₀^close, its unique u-branch
    φ(z) ∈ U₀ is never in C. Hand proof: z − φ(z) (φ(z) ∈ N(z)) would be an
    edge with both endpoints in C, contradicting H-adjacency (¬Adj). -/
theorem uBranch_isolation {V : Type*} [DecidableEq V] (Adj : V → V → Prop)
    {C : Finset V} {z w : V}
    (hC : IsHclique Adj C) (hz : z ∈ C) (hadj : Adj z w) :
    w ∉ C :=
  fun hw => hC z hz w hw hadj

/-- L1 corollary (R163 §A): the close-image never meets any subset of C —
    in particular φ(Z₀^close) ∩ Z₀^mid = ∅ since Z₀^mid ⊆ C. -/
theorem closeImage_disjoint_of_subset {V : Type*} [DecidableEq V]
    (Adj : V → V → Prop) {C Mid : Finset V} {z w : V}
    (hC : IsHclique Adj C) (hz : z ∈ C) (hadj : Adj z w)
    (hMid : Mid ⊆ C) :
    w ∉ Mid :=
  fun hw => uBranch_isolation Adj hC hz hadj (hMid hw)

/-- R163 u-side degree bound (abstract Finset form): φ injective on the close
    set, mapping it into U, with image disjoint from the mid set (by L1) and
    the mid set inside U. Then |close| + |mid| ≤ |U|. The image of close is a
    copy of close inside U, disjoint from mid. -/
theorem uSide_degree_bound {V : Type*} [DecidableEq V]
    {Close Mid U : Finset V} {φ : V → V}
    (hInj : Set.InjOn φ ↑Close)
    (hMaps : ∀ x ∈ Close, φ x ∈ U)
    (hDisj : Disjoint (Close.image φ) Mid)
    (hMidSub : Mid ⊆ U) :
    Close.card + Mid.card ≤ U.card := by
  have hcard : (Close.image φ).card = Close.card :=
    Finset.card_image_of_injOn hInj
  have hsub : Close.image φ ∪ Mid ⊆ U :=
    Finset.union_subset (Finset.image_subset_iff.mpr (fun x hx => hMaps x hx)) hMidSub
  calc Close.card + Mid.card
      = (Close.image φ).card + Mid.card := by rw [hcard]
    _ = (Close.image φ ∪ Mid).card := (Finset.card_union_of_disjoint hDisj).symm
    _ ≤ U.card := Finset.card_le_card hsub

/-- R163's combined statement in the H-clique setting: the close set sits in
    C with its u-branches in U; the mid set sits in C ∩ U; φ injective on
    close. Then |close| + |mid| ≤ |U| — the degree-essential bound, useful
    exactly when d(u) − 1 = |U| < |V₀| = d(v) − 1 (R163 §A). -/
theorem r163_uSideBound_inHclique {V : Type*} [DecidableEq V]
    (Adj : V → V → Prop)
    {C Close Mid U : Finset V} {φ : V → V}
    (hC : IsHclique Adj C)
    (hClose : ∀ x ∈ Close, x ∈ C ∧ Adj x (φ x))
    (hMidSubC : Mid ⊆ C) (hMidSubU : Mid ⊆ U)
    (hInj : Set.InjOn φ ↑Close)
    (hMaps : ∀ x ∈ Close, φ x ∈ U) :
    Close.card + Mid.card ≤ U.card := by
  apply uSide_degree_bound hInj hMaps _ hMidSubU
  rw [Finset.disjoint_left]
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨hyC, hadj⟩ := hClose y hy
  exact fun hm => uBranch_isolation Adj hC hyC hadj (hMidSubC hm)

end ESUBranchIsolation
