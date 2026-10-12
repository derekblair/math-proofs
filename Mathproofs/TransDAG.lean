/-
  TransDAG.lean — R279/R288 D7′ dual-ascent barrier (pure order theory) + R292 L_s/C3 ascent-depth machinery.

  Paper: papers/abstract-lock-transdag-October-11-2026/
  Status: [PROVED] — no_dual_target_demote, no_dual_source_promote, dual_preserves_s_card, ascentDepth_le/promote_mono/eq_zero_iff
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R310: bakkie full-library build exit 0, zero sorrys; Q-33 part axiom-free, L_s/C3 standard axioms.
-/

/-
  TransDAG.lean — Lean formalization of R288's repaired D7′ (dual-ascent
  barrier), the exact fragment of R279's D7 that follows from fixed-span
  T7′/T8′ after Q-26's objection.

  Source: ~/workspace/math-unsolved/ROUND288_DOSSIER.md (§2).
  Rule-9 hostile review Q-33 (Bunny, #agents threads 1791706135.637449 and
  1791707275.724949, 2026-10-11 ~01:29 PDT), quoted:
  - "Q33 (a): D7′ SURVIVES for full-spectrum Pareto endpoints, or explicit
    all-duals ascent. OBJECTION to applying it to sampled-census Pareto
    endpoints from Q22 alone: the forbidden dual may be absent from that
    census."
  - "Q-33: OBJECTION to census application. D7′/D7′′ SURVIVE with
    full-spectrum Pareto endpoints or proved all-duals ascent. Complementary
    abstract models survive. Original census remains unverified."
  The rule-9 gate is OPEN for D7′ ONLY under the scoped premises
  (full-spectrum Pareto endpoints or proved all-duals ascent). The
  195-class Sidon census application is NOT cleared — it is not claimed here.

  Setting (pure finite order theory, no Sidon content): classes are (e,s)
  points. A reflection dual d of c satisfies s_d = s_c and e_c ≤ e_d (the
  T7′ shape: duals sit e-above-or-equal). A demote edge c → q satisfies
  q ≤ c (product order), q ≠ c (D1 orientation, 24/24 scripted). A promote
  edge q → a satisfies q ≤ a, q ≠ a (16/16 scripted).

  Honesty labels:
  - no_dual_target_demote (D7′(a)), no_dual_source_promote (D7′(b)):
    [PROVED*] hand proofs (R288 §2), Lean-checked below.
  - The scoped premises (full-spectrum endpoints / all-duals ascent) enter
    as the shape of the `hdual` hypothesis — the module proves the
    order-theoretic core; instantiating it on a census is application work,
    explicitly NOT done here per Q-33's objection.
  - D7-full as a general theorem: [OPEN] (both missing halves realizable in
    abstract T7′/T8′ models — R288 §2). NOT formalized.
  - D7′′ (H ⟹ full D7): [PROVED*] conditional, but H is FALSE on the census
    (39 violations [COMPUTED]×2) — recorded in the dossier, not formalized.
  - The 0-violation census audits (24 demote / 16 promote edges, both paths)
    are cited [COMPUTED]×2 data, never re-claimed here.

  Lean 4.34.1 / Mathlib (pin d13f23b). Zero sorrys. Standard axioms only.
-/

import Mathlib

namespace TransDAG

/-- A Pareto class as an (e,s) point. -/
abbrev Class := ℕ × ℕ

/-- T7′-shaped duality: d is a dual of c if s is preserved and e does not
    drop (duals sit e-above-or-equal). This is the scoped premise shape:
    it holds for full-spectrum Pareto endpoints or under proved all-duals
    ascent (Q-33 scope). -/
def IsDual (d c : Class) : Prop :=
  d.2 = c.2 ∧ c.1 ≤ d.1

/-- Demote-edge shape: target sits below source in the product order,
    strictly (D1 orientation). -/
def IsDemoteEdge (c q : Class) : Prop :=
  q.1 ≤ c.1 ∧ q.2 ≤ c.2 ∧ q ≠ c

/-- Promote-edge shape: source sits below target in the product order,
    strictly. -/
def IsPromoteEdge (q a : Class) : Prop :=
  q.1 ≤ a.1 ∧ q.2 ≤ a.2 ∧ q ≠ a

/-- D7′(a): no demote edge targets a dual of its source.
    Proof (R288 §2): dual gives e_q ≥ e_c (T7′); demote gives e_q ≤ e_c;
    hence e_q = e_c, and s_q = s_c by duality, so q = c — contradiction. -/
theorem no_dual_target_demote {c q : Class}
    (hedge : IsDemoteEdge c q) (hdual : IsDual q c) : False := by
  obtain ⟨hle1, _, hne⟩ := hedge
  obtain ⟨hs, hge⟩ := hdual
  have he : q.1 = c.1 := le_antisymm hle1 hge
  exact hne (Prod.ext he hs)

/-- D7′(b): no promote edge is sourced at a dual of its target.
    Proof (R288 §2): symmetric — dual gives e_q ≥ e_a; promote gives
    e_q ≤ e_a; hence q = a — contradiction. -/
theorem no_dual_source_promote {q a : Class}
    (hedge : IsPromoteEdge q a) (hdual : IsDual q a) : False := by
  obtain ⟨hle1, _, hne⟩ := hedge
  obtain ⟨hs, hge⟩ := hdual
  have he : q.1 = a.1 := le_antisymm hle1 hge
  exact hne (Prod.ext he hs)

/-!
## R292 ascent calculus (Q-36 review fold)

Rule-9 hostile review Q-36 (Bunny, #agents 2026-10-11 03:14–03:35 PDT),
quoted verbatim:
> "Q-36: OBJECTION to aggregate SURVIVES — L_s SURVIVES, C3 SURVIVES
>  (finite promotion DAGs, bound |C|−1), C1/C2/C4 require full-spectrum
>  endpoints or proved all-duals ascent (sampled-Pareto transfer NOT cleared)"

Folded here: **L_s + C3 ONLY**, scoped exactly to the reviewed scope
(finite promotion DAGs). Source: ROUND292_DOSSIER.md §2.
- `dual_preserves_s_card` (L_s): the reflection-card core of "duals
  preserve s" — W(Ā) = σ−W(A) as sets, w ↦ σ−w bijects [0,σ].
- `ascentDepth_le` (C3(i)), `ascentDepth_promote_mono` (C3(ii)),
  `ascentDepth_eq_zero_iff` (C3(iii)): ascent-depth basics for a finite
  acyclic promote DAG (PromoAcyclic = R292's D1b).
NOT formalized (per the verdict): C1/C2/C4 — their census transfer is
[OPEN]; they need full-spectrum endpoints or proved all-duals ascent.

Honesty labels: L_s, C3(i)/(ii)/(iii) [PROVED*] (Q-36 SURVIVES scoped;
Lean-checked below). C1/C2/C4: [OPEN] census-transfer (not formalized).
-/

/-- L_s (R292 §2): duals preserve s. The concrete mechanism is W-reflection:
    W(Ā) = σ − W(A) as sets, and w ↦ σ − w bijects [0,σ].
    The order-theoretic core: reflecting a finset in a bound preserves card. -/
theorem dual_preserves_s_card (σ : ℕ) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w ≤ σ) :
    (W.image (fun w => σ - w)).card = W.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have ha' := hW a ha
  have hb' := hW b hb
  simp only at hab
  omega

section AscentDepth

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Ep : V → V → Prop} [DecidableRel Ep]

/-- A promotion chain of length `n` sourced at `c`: vertices `f 0 = c`
    with consecutive promote edges. (R292 §1.) -/
def IsPromoChain (c : V) (n : ℕ) : Prop :=
  ∃ f : Fin (n + 1) → V, f 0 = c ∧ ∀ i : Fin n, Ep (f i.castSucc) (f i.succ)

instance IsPromoChain.decidablePred (c : V) :
    DecidablePred (IsPromoChain (Ep := Ep) c) := fun n => by
  unfold IsPromoChain
  infer_instance

/-- Acyclicity of the promote relation: no vertex reaches itself.
    (R292's D1b: (C, E_p) is acyclic.) -/
def PromoAcyclic : Prop :=
  ∀ c : V, ¬ Relation.TransGen Ep c c

omit [Fintype V] [DecidableEq V] [DecidableRel Ep] in
/-- A chain from index `a` to index `b` (a < b) yields reachability. -/
theorem promoChain_reach {n : ℕ} {f : Fin (n + 1) → V}
    (hedge : ∀ i : Fin n, Ep (f i.castSucc) (f i.succ))
    {a b : Fin (n + 1)} (hlt : a < b) :
    Relation.TransGen Ep (f a) (f b) := by
  suffices key : ∀ d : ℕ, ∀ a b : Fin (n + 1), a < b → b.val - a.val = d →
      Relation.TransGen Ep (f a) (f b) from
    key (b.val - a.val) a b hlt rfl
  intro d
  induction d with
  | zero =>
    intro a b hlt hd
    have hab : a.val < b.val := hlt
    omega
  | succ d ih =>
    intro a b hlt hd
    have ha_lt_n : a.val < n := by
      have hb1 : b.val < n + 1 := b.isLt
      have hab : a.val < b.val := hlt
      omega
    have hEp := hedge ⟨a.val, ha_lt_n⟩
    have e1 : ((⟨a.val, ha_lt_n⟩ : Fin n).castSucc : Fin (n + 1)) = a := by
      rw [Fin.ext_iff]; rfl
    have e2 : ((⟨a.val, ha_lt_n⟩ : Fin n).succ : Fin (n + 1)) = ⟨a.val + 1, by omega⟩ := by
      rw [Fin.ext_iff]; rfl
    rw [e1, e2] at hEp
    have hmid_lt : a.val + 1 < n + 1 := by
      have hb1 : b.val < n + 1 := b.isLt
      have hab : a.val < b.val := hlt
      omega
    by_cases hd0 : d = 0
    · subst hd0
      have hb_eq : b = (⟨a.val + 1, hmid_lt⟩ : Fin (n + 1)) := by
        apply Fin.ext
        show b.val = a.val + 1
        have hab : a.val < b.val := hlt
        omega
      rw [hb_eq]
      exact Relation.TransGen.single hEp
    · have hcb : (⟨a.val + 1, hmid_lt⟩ : Fin (n + 1)) < b := by
        show a.val + 1 < b.val
        have hab : a.val < b.val := hlt
        omega
      have hdiff : b.val - (⟨a.val + 1, hmid_lt⟩ : Fin (n + 1)).val = d := by
        show b.val - (a.val + 1) = d
        omega
      exact Relation.TransGen.trans (Relation.TransGen.single hEp)
        (ih _ _ hcb hdiff)

omit [Fintype V] [DecidableEq V] [DecidableRel Ep] in
/-- Chain vertices are pairwise distinct in an acyclic promote DAG. -/
theorem promoChain_injective (hac : PromoAcyclic (Ep := Ep))
    {c : V} {n : ℕ} {f : Fin (n + 1) → V}
    (_h0 : f 0 = c) (hedge : ∀ i : Fin n, Ep (f i.castSucc) (f i.succ)) :
    Function.Injective f := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hr := promoChain_reach hedge h
    rw [hij] at hr
    exact hac _ hr
  · have hr := promoChain_reach hedge h
    rw [← hij] at hr
    exact hac _ hr

omit [DecidableEq V] [DecidableRel Ep] in
/-- C3 core: every promotion chain sourced at `c` has length ≤ |V| − 1
    (chains are simple paths: n+1 distinct vertices in V). -/
theorem promoChain_length_le (hac : PromoAcyclic (Ep := Ep))
    {c : V} {n : ℕ} (h : IsPromoChain (Ep := Ep) c n) :
    n ≤ Fintype.card V - 1 := by
  obtain ⟨f, h0, hedge⟩ := h
  have hinj := promoChain_injective hac h0 hedge
  have hcard : Fintype.card (Fin (n + 1)) ≤ Fintype.card V :=
    Fintype.card_le_of_injective f hinj
  rw [Fintype.card_fin] at hcard
  omega

/-- Chain lengths sourced at `c`, bounded by |V|−1. -/
def chainLengths (c : V) : Finset ℕ :=
  (Finset.Icc 0 (Fintype.card V - 1)).filter (IsPromoChain (Ep := Ep) c)

/-- The chain-length set is nonempty (the trivial length-0 chain). -/
theorem chainLengths_nonempty (c : V) : (chainLengths (Ep := Ep) c).Nonempty := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨c⟩
  rw [chainLengths]
  refine Finset.filter_nonempty_iff.mpr ⟨0, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    omega
  · exact ⟨fun _ => c, rfl, fun i => Fin.elim0 i⟩

/-- Ascent depth: the longest promotion chain sourced at `c`. (R292 §1.) -/
noncomputable def ascentDepth (c : V) : ℕ :=
  (chainLengths (Ep := Ep) c).max' (chainLengths_nonempty c)

/-- Membership unfolds to the bound + the chain predicate. -/
theorem mem_chainLengths {c : V} {n : ℕ} :
    n ∈ chainLengths (Ep := Ep) c ↔
      n ≤ Fintype.card V - 1 ∧ IsPromoChain (Ep := Ep) c n := by
  constructor
  · intro h
    rw [chainLengths, Finset.mem_filter, Finset.mem_Icc] at h
    exact ⟨h.1.2, h.2⟩
  · intro h
    rw [chainLengths, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.zero_le n, h.1⟩, h.2⟩

/-- C3(i) (R292 §2): ad(c) ≤ |C| − 1. -/
theorem ascentDepth_le (_hac : PromoAcyclic (Ep := Ep)) (c : V) :
    ascentDepth (Ep := Ep) c ≤ Fintype.card V - 1 := by
  unfold ascentDepth
  apply Finset.max'_le
  intro n hn
  exact (mem_chainLengths.mp hn).1

/-- C3(ii) (R292 §2): promote-monotonicity — ad strictly decreases along
    promote edges: Ep q a → ad q ≥ ad a + 1. Prepend q to a longest chain
    from a; q is fresh (else a positive closed walk, contra acyclicity). -/
theorem ascentDepth_promote_mono (hac : PromoAcyclic (Ep := Ep))
    {q a : V} (hedge : Ep q a) :
    ascentDepth (Ep := Ep) a + 1 ≤ ascentDepth (Ep := Ep) q := by
  set n := ascentDepth (Ep := Ep) a with hn_def
  have hn_mem : n ∈ chainLengths (Ep := Ep) a := Finset.max'_mem _ _
  obtain ⟨hn_le, f, hf0, hfedge⟩ := mem_chainLengths.mp hn_mem
  -- q is not on the chain (else a positive closed walk q → … → q)
  have hfresh : ∀ i : Fin (n + 1), f i ≠ q := by
    intro i hi_eq
    have h1 : Relation.TransGen Ep q a := Relation.TransGen.single hedge
    by_cases hi0 : i = 0
    · subst hi0
      have haq : a = q := hf0.symm.trans hi_eq
      exact hac q (haq ▸ h1)
    · have h0i : (0 : Fin (n + 1)) < i := Fin.pos_iff_ne_zero.mpr hi0
      have h2 := promoChain_reach hfedge h0i
      rw [hf0, hi_eq] at h2
      exact hac q (Relation.TransGen.trans h1 h2)
  -- the prepended chain g : Fin (n+2) → V
  let g : Fin (n + 2) → V :=
    fun k => if k.val = 0 then q else f ⟨k.val - 1, by have := k.isLt; omega⟩
  have gval : ∀ k : Fin (n + 2), k.val = 0 → g k = q := by
    intro k hk
    show ite (k.val = 0) q (f ⟨k.val - 1, by have := k.isLt; omega⟩) = q
    simp [hk]
  have gval' : ∀ k : Fin (n + 2), k.val ≠ 0 →
      g k = f ⟨k.val - 1, by have := k.isLt; omega⟩ := by
    intro k hk
    show ite (k.val = 0) q (f ⟨k.val - 1, by have := k.isLt; omega⟩) = _
    simp [hk]
  have hgedge : ∀ t : Fin (n + 1), Ep (g t.castSucc) (g t.succ) := by
    intro t
    have hcs : (t.castSucc).val = t.val := rfl
    have hs_ne : (t.succ).val ≠ 0 := by
      have hvs : (t.succ).val = t.val + 1 := by simp
      omega
    by_cases ht0 : t.val = 0
    · rw [gval _ (by rw [hcs]; exact ht0), gval' _ hs_ne]
      have hval : (t.succ).val = 1 := by
        have hvs : (t.succ).val = t.val + 1 := by simp
        omega
      have hidx : (⟨(t.succ).val - 1, by have := t.isLt; omega⟩ : Fin (n + 1)) = 0 := by
        have h1 : (t.succ).val - 1 = 0 := by
          have hvs : (t.succ).val = t.val + 1 := by simp
          omega
        have hz : ((0 : Fin (n + 1))).val = 0 := by simp
        rw [Fin.ext_iff]
        show (t.succ).val - 1 = ((0 : Fin (n + 1))).val
        rw [h1, hz]
      rw [hidx, hf0]
      exact hedge
    · rw [gval' _ (by rw [hcs]; exact ht0), gval' _ hs_ne]
      have hkn : t.val - 1 < n := by
        have h1 := t.isLt
        have h2 : 0 < t.val := Nat.pos_of_ne_zero ht0
        omega
      have hEp := hfedge ⟨t.val - 1, hkn⟩
      have e1 : ((⟨t.val - 1, hkn⟩ : Fin n).castSucc : Fin (n + 1)) =
          ⟨t.val - 1, by omega⟩ := by
        rw [Fin.ext_iff]; rfl
      have e2 : ((⟨t.val - 1, hkn⟩ : Fin n).succ : Fin (n + 1)) =
          ⟨t.val, by omega⟩ := by
        rw [Fin.ext_iff]
        show ((⟨t.val - 1, hkn⟩ : Fin n).succ).val = t.val
        have hs1 : ((⟨t.val - 1, hkn⟩ : Fin n).succ).val = (t.val - 1) + 1 := rfl
        omega
      rw [e1, e2] at hEp
      have hidx2 : (⟨(t.succ).val - 1, by have := t.isLt; omega⟩ : Fin (n + 1)) =
          ⟨t.val, by omega⟩ := by
        apply Fin.ext
        show (t.succ).val - 1 = t.val
        have hvs : (t.succ).val = t.val + 1 := by simp
        omega
      rw [hidx2]
      exact hEp
  have hchain : IsPromoChain (Ep := Ep) q (n + 1) :=
    ⟨g, gval _ (by simp), hgedge⟩
  have hle := promoChain_length_le hac hchain
  have hmem : n + 1 ∈ chainLengths (Ep := Ep) q := mem_chainLengths.mpr ⟨hle, hchain⟩
  have hle2 := Finset.le_max' (chainLengths (Ep := Ep) q) (n + 1) hmem
  have hle2' : n + 1 ≤ ascentDepth (Ep := Ep) q := hle2
  omega

/-- C3(iii) (R292 §2): ad(c) = 0 ↔ c sources no promote edge. -/
theorem ascentDepth_eq_zero_iff (hac : PromoAcyclic (Ep := Ep)) (c : V) :
    ascentDepth (Ep := Ep) c = 0 ↔ ∀ a : V, ¬ Ep c a := by
  constructor
  · intro h a ha
    -- V has ≥ 2 elements: else a = c and Ep c c contradicts acyclicity
    have hcard2 : 1 < Fintype.card V := by
      rcases eq_or_ne (Fintype.card V) 1 with h1 | h1
      · obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp h1
        have hac_eq : a = c := (hx a).trans (hx c).symm
        rw [hac_eq] at ha
        exact absurd (Relation.TransGen.single ha) (hac c)
      · have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨c⟩
        omega
    have h1 : (1 : ℕ) ∈ chainLengths (Ep := Ep) c :=
      mem_chainLengths.mpr ⟨by omega, ⟨![c, a], rfl, fun i => by fin_cases i; exact ha⟩⟩
    have hle := Finset.le_max' (chainLengths (Ep := Ep) c) 1 h1
    have hle' : (1 : ℕ) ≤ ascentDepth (Ep := Ep) c := hle
    omega
  · intro h
    apply le_antisymm _ (Nat.zero_le _)
    have hle : (chainLengths (Ep := Ep) c).max' (chainLengths_nonempty c) ≤ 0 := by
      apply Finset.max'_le
      intro n hn
      obtain ⟨hn_le, f, hf0, hfedge⟩ := mem_chainLengths.mp hn
      by_contra hpos
      have h0lt : (0 : ℕ) < n := by omega
      have hEp := hfedge ⟨0, h0lt⟩
      have c1 : ((⟨0, h0lt⟩ : Fin n).castSucc : Fin (n + 1)) = 0 := by
        rw [Fin.ext_iff]; rfl
      rw [c1, hf0] at hEp
      exact h _ hEp
    have hle' : ascentDepth (Ep := Ep) c ≤ 0 := hle
    exact hle'

end AscentDepth
