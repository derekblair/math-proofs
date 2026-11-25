import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Cast.Order
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Seam C `S010` (`OEIS A401714 ≤ A401715`): Karttunen's Unitary/Squarefree Divisor Inequality

Statement contract frozen from `PIN-S010.md` v1 (`delta_vs_source: NONE`) for Antti Karttunen's
Nov 06 2026 conjecture on `OEIS A401714` (`%F` lines 13–14, rev `#12`) and `OEIS A401715`
(`%F` line 15, rev `#13`), proved via the three-regime primorial-core and pure-`ℚ`
harmonic-squarefree route (`SCOPING-S010.md` §2.2, Steps 1–7).
-/

namespace SeamC.A401714

/-- `OEIS A007947`: Squarefree kernel `rad(n)`, product of distinct prime factors `p` in
`n.primeFactors` (`rad 1 = 1`). -/
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

/-- `OEIS A003557`: `n` divided by its squarefree kernel `rad(n)` (`a003557 1 = 1`). -/
def a003557 (n : ℕ) : ℕ :=
  n / rad n

/-- `OEIS A053669`: Smallest prime `p` not dividing `n` (`a053669 1 = 2`, `a053669 0 = 0`). -/
noncomputable def a053669 (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ ¬ p ∣ n}

/-- `OEIS A034448`: Sum of unitary divisors of `n` (`d ∈ n.divisors` with `Nat.Coprime d (n / d)`;
`a034448 1 = 1`). -/
def a034448 (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors with Nat.Coprime d (n / d), d

/-- `OEIS A048250`: Sum of squarefree divisors of `n` (`d ∈ n.divisors` with `Squarefree d`;
`a048250 1 = 1`). -/
def a048250 (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors with Squarefree d, d

/-- `OEIS A401714`: `{0,1}`-valued Iverson indicator `if a003557 n < a053669 n then 1 else 0`
(`a401714 1 = 1`). -/
noncomputable def a401714 (n : ℕ) : ℕ :=
  if a003557 n < a053669 n then 1 else 0

/-- `OEIS A401715`: `{0,1}`-valued Iverson indicator
`if 2 * n ≤ a034448 n + a048250 n then 1 else 0` (`a401715 1 = 1`). -/
def a401715 (n : ℕ) : ℕ :=
  if 2 * n ≤ a034448 n + a048250 n then 1 else 0

/-! ### Step 1 — Divisor-Sum to Multiplicative Euler-Product Identities -/

private lemma nat_prod_le_prod {ι : Type*} {s : Finset ι} {f g : ι → ℕ}
    (h : ∀ x ∈ s, f x ≤ g x) : ∏ x ∈ s, f x ≤ ∏ x ∈ s, g x := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t _ ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    exact Nat.mul_le_mul (h a (Finset.mem_cons_self a t))
      (ih fun x hx => h x (Finset.mem_cons_of_mem hx))

private lemma rat_one_le_prod {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ x ∈ s, 1 ≤ f x) : 1 ≤ ∏ x ∈ s, f x := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t _ ih =>
    rw [Finset.prod_cons]
    have ha : 1 ≤ f a := h a (Finset.mem_cons_self a t)
    have ht : 1 ≤ ∏ x ∈ t, f x := ih fun x hx => h x (Finset.mem_cons_of_mem hx)
    nlinarith

private lemma rat_prod_le_prod_of_subset_of_one_le {ι : Type*} [DecidableEq ι]
    {s t : Finset ι} {f : ι → ℚ} (hst : s ⊆ t) (hf : ∀ x ∈ t, 1 ≤ f x) :
    ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x := by
  rw [← Finset.prod_sdiff hst]
  have hs_pos : 0 ≤ ∏ x ∈ s, f x :=
    Finset.prod_nonneg fun x hx => le_trans zero_le_one (hf x (hst hx))
  have hd_ge : 1 ≤ ∏ x ∈ t \ s, f x :=
    rat_one_le_prod fun x hx => hf x (Finset.mem_sdiff.mp hx).1
  nlinarith

private lemma rat_prod_le_pow_card {ι : Type*} (s : Finset ι) (f : ι → ℚ) (B : ℚ)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) (hB : 0 ≤ B) (hle : ∀ x ∈ s, f x ≤ B) :
    ∏ x ∈ s, f x ≤ B ^ s.card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t _ ih =>
    rw [Finset.prod_cons, Finset.card_cons, pow_succ']
    have ha0 := hf0 a (Finset.mem_cons_self a t)
    have hale := hle a (Finset.mem_cons_self a t)
    have ht0 : 0 ≤ ∏ x ∈ t, f x :=
      Finset.prod_nonneg fun x hx => hf0 x (Finset.mem_cons_of_mem hx)
    have hih := ih (fun x hx => hf0 x (Finset.mem_cons_of_mem hx))
      (fun x hx => hle x (Finset.mem_cons_of_mem hx))
    exact mul_le_mul hale hih ht0 hB

private lemma rat_pow_card_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (B : ℚ)
    (hB : 0 ≤ B) (hle : ∀ x ∈ s, B ≤ f x) :
    B ^ s.card ≤ ∏ x ∈ s, f x := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t _ ih =>
    rw [Finset.prod_cons, Finset.card_cons, pow_succ']
    have hale := hle a (Finset.mem_cons_self a t)
    have hih := ih fun x hx => hle x (Finset.mem_cons_of_mem hx)
    exact mul_le_mul hale hih (pow_nonneg hB _) (le_trans hB hale)

private lemma coprime_prod_right {a : ℕ} {s : Finset ℕ} {f : ℕ → ℕ}
    (h : ∀ x ∈ s, Nat.Coprime a (f x)) : Nat.Coprime a (∏ x ∈ s, f x) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons x t _ ih =>
    rw [Finset.prod_cons]
    exact (h x (Finset.mem_cons_self x t)).mul_right
      (ih fun y hy => h y (Finset.mem_cons_of_mem hy))

private lemma coprime_prod_left {b : ℕ} {s : Finset ℕ} {f : ℕ → ℕ}
    (h : ∀ x ∈ s, Nat.Coprime (f x) b) : Nat.Coprime (∏ x ∈ s, f x) b :=
  (coprime_prod_right fun x hx => (h x hx).symm).symm

private lemma squarefree_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.cons_induction with
  | empty => exact squarefree_one
  | cons p t hpt ih =>
    rw [Finset.prod_cons]
    have hp : p.Prime := hs p (Finset.mem_cons_self p t)
    have ht : ∀ q ∈ t, q.Prime := fun q hq => hs q (Finset.mem_cons_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ t, q) :=
      coprime_prod_right fun q hq =>
        (Nat.coprime_primes hp (ht q hq)).mpr fun h => hpt (h ▸ hq)
    exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, ih ht⟩

private lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

private lemma primeFactors_pow_primes {s : Finset ℕ} {f : ℕ → ℕ}
    (hs : ∀ p ∈ s, p.Prime) (hf : ∀ p ∈ s, 0 < f p) :
    (∏ p ∈ s, p ^ f p).primeFactors = s := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons p t _ ih =>
    rw [Finset.prod_cons]
    have hp : p.Prime := hs p (Finset.mem_cons_self p t)
    have hfp_pos : 0 < f p := hf p (Finset.mem_cons_self p t)
    obtain ⟨k, hk⟩ : ∃ k, f p = k + 1 := ⟨f p - 1, by omega⟩
    have ht : ∀ q ∈ t, q.Prime := fun q hq => hs q (Finset.mem_cons_of_mem hq)
    have hft : ∀ q ∈ t, 0 < f q := fun q hq => hf q (Finset.mem_cons_of_mem hq)
    have hp_ne : p ^ f p ≠ 0 := pow_ne_zero _ hp.ne_zero
    have ht_ne : ∏ q ∈ t, q ^ f q ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun q hq => pow_ne_zero _ (ht q hq).ne_zero
    rw [Nat.primeFactors_mul hp_ne ht_ne, hk, Nat.primeFactors_pow_succ, hp.primeFactors,
      ih ht hft]
    simp [Finset.cons_eq_insert]

private lemma eq_prod_primeFactors_factorization {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn

/-- Step 1b: Squarefree divisor sum equals the Euler product `∏ p ∈ n.primeFactors, (1 + p)`. -/
theorem a048250_eq_prod {n : ℕ} (hn : n ≠ 0) :
    a048250 n = ∏ p ∈ n.primeFactors, (1 + p) := by
  unfold a048250
  rw [Finset.prod_one_add]
  refine Finset.sum_bij (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    exact Finset.mem_powerset.mpr (Nat.primeFactors_mono hd.1.1 hn)
  · intro d₁ hd₁ d₂ hd₂ h
    rw [Finset.mem_filter] at hd₁ hd₂
    rw [← Nat.prod_primeFactors_of_squarefree hd₁.2, ← Nat.prod_primeFactors_of_squarefree hd₂.2, h]
  · intro T hT
    rw [Finset.mem_powerset] at hT
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
    refine ⟨∏ p ∈ T, p, ?_, Nat.primeFactors_prod hTp⟩
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hn⟩, squarefree_prod_primes hTp⟩
    exact dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hT) (Nat.prod_primeFactors_dvd n)
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact (Nat.prod_primeFactors_of_squarefree hd.2).symm

/-- Step 1a: Unitary divisor sum equals `∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p)`. -/
theorem a034448_eq_prod {n : ℕ} (hn : n ≠ 0) :
    a034448 n = ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  unfold a034448
  rw [Finset.prod_one_add]
  refine Finset.sum_bij (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    exact Finset.mem_powerset.mpr (Nat.primeFactors_mono hd.1.1 hn)
  · intro d₁ hd₁ d₂ hd₂ h
    have val_eq : ∀ d, d ∈ n.divisors.filter (fun d => Nat.Coprime d (n / d)) →
        d = ∏ p ∈ d.primeFactors, p ^ n.factorization p := by
      intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hn))
      have hq0 : n / d ≠ 0 := by
        intro hq
        have := Nat.mul_div_cancel' hd.1.1
        rw [hq, mul_zero] at this
        exact hn this.symm
      conv_lhs => rw [← eq_prod_primeFactors_factorization hd0]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hndvd : ¬ p ∣ (n / d) := by
        have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hp_dvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
        exact fun hpd => hp_prime.not_dvd_one (hd.2.gcd_eq_one ▸ Nat.dvd_gcd hp_dvd hpd)
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hd.1.1
      rw [← hmul, Nat.factorization_mul hd0 hq0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]
    rw [val_eq d₁ hd₁, val_eq d₂ hd₂, h]
  · intro T hT
    rw [Finset.mem_powerset] at hT
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
    have hTf : ∀ p ∈ T, 0 < n.factorization p := fun p hp =>
      Nat.Prime.factorization_pos_of_dvd (hTp p hp) hn (Nat.dvd_of_mem_primeFactors (hT hp))
    set d := ∏ p ∈ T, p ^ n.factorization p
    set c := ∏ p ∈ n.primeFactors \ T, p ^ n.factorization p
    have hdc : c * d = n := by
      dsimp [c, d]
      rw [Finset.prod_sdiff hT]
      exact eq_prod_primeFactors_factorization hn
    have hd_pos : 0 < d := Finset.prod_pos fun p hp => pow_pos (hTp p hp).pos _
    have hdiv : n / d = c := by
      rw [← hdc, mul_comm]
      exact Nat.mul_div_right c hd_pos
    have hcop : Nat.Coprime d c := by
      refine coprime_prod_left fun p hp => ?_
      refine coprime_prod_right fun q hq => ?_
      rw [Finset.mem_sdiff] at hq
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq.1
      have hpq : p ≠ q := fun heq => hq.2 (heq ▸ hp)
      exact Nat.coprime_pow_primes _ _ (hTp p hp) hq_prime hpq
    refine ⟨d, ?_, primeFactors_pow_primes hTp hTf⟩
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨⟨c, by rw [← hdc, mul_comm]⟩, hn⟩, hdiv ▸ hcop⟩
  · intro d hd
    have hsub : d ∈ n.divisors.filter (fun d => Nat.Coprime d (n / d)) := hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hsub
    have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hsub.1.1 (Nat.pos_of_ne_zero hn))
    have hq0 : n / d ≠ 0 := by
      intro hq
      have := Nat.mul_div_cancel' hsub.1.1
      rw [hq, mul_zero] at this
      exact hn this.symm
    conv_lhs => rw [← eq_prod_primeFactors_factorization hd0]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hndvd : ¬ p ∣ (n / d) := by
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      exact fun hpd => hp_prime.not_dvd_one (hsub.2.gcd_eq_one ▸ Nat.dvd_gcd hp_dvd hpd)
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hsub.1.1
    rw [← hmul, Nat.factorization_mul hd0 hq0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]

/-- Multiplicativity of `a034448` on coprime nonzero inputs. -/
theorem a034448_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    a034448 (a * b) = a034448 a * a034448 b := by
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  rw [a034448_eq_prod hab0, a034448_eq_prod ha, a034448_eq_prod hb, hab.primeFactors_mul]
  have hdisj : Disjoint a.primeFactors b.primeFactors := hab.disjoint_primeFactors
  rw [Finset.prod_union hdisj]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpb : ¬ p ∣ b := fun h =>
      (Nat.prime_of_mem_primeFactors hp).not_dvd_one
        (hab.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) h)
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpb, add_zero]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpa : ¬ p ∣ a := fun h =>
      (Nat.prime_of_mem_primeFactors hp).not_dvd_one
        (hab.gcd_eq_one ▸ Nat.dvd_gcd h (Nat.dvd_of_mem_primeFactors hp))
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpa, zero_add]

/-- Multiplicativity of `a048250` on coprime nonzero inputs. -/
theorem a048250_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    a048250 (a * b) = a048250 a * a048250 b := by
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  rw [a048250_eq_prod hab0, a048250_eq_prod ha, a048250_eq_prod hb, hab.primeFactors_mul,
    Finset.prod_union hab.disjoint_primeFactors]

/-- On squarefree `s`, `a034448 s = a048250 s` and `s ≤ a048250 s`. -/
theorem squarefree_a034448_eq_a048250 {s : ℕ} (hs : Squarefree s) :
    a034448 s = a048250 s ∧ s ≤ a048250 s := by
  have hs0 : s ≠ 0 := hs.ne_zero
  rw [a034448_eq_prod hs0, a048250_eq_prod hs0]
  refine ⟨Finset.prod_congr rfl fun p hp => ?_, ?_⟩
  · have hle : s.factorization p ≤ 1 := hs.natFactorization_le_one p
    have hpos : 0 < s.factorization p :=
      Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hs0
        (Nat.dvd_of_mem_primeFactors hp)
    have heq : s.factorization p = 1 := by omega
    rw [heq, pow_one]
  · conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hs]
    exact nat_prod_le_prod fun p _ => by omega

/-- Parity exactness (`PIN-S010.md` fidelity note 4): `a034448 n + a048250 n` is even for all
`n ≥ 1`, so `A325973(n) = (a034448 n + a048250 n) / 2` has zero rounding loss. -/
theorem even_a034448_add_a048250 {n : ℕ} (hn : 1 ≤ n) :
    Even (a034448 n + a048250 n) := by
  have hn0 : n ≠ 0 := by omega
  rw [a034448_eq_prod hn0, a048250_eq_prod hn0]
  by_cases hodd : ∃ p ∈ n.primeFactors, p ≠ 2
  · rcases hodd with ⟨p, hp, hp2⟩
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_odd : Odd p := hp_prime.odd_of_ne_two hp2
    rcases hp_odd.pow (n := n.factorization p) with ⟨u1, hu1⟩
    rcases hp_odd with ⟨u2, hu2⟩
    rcases Finset.dvd_prod_of_mem (fun q => 1 + q ^ n.factorization q) hp with ⟨v1, hv1⟩
    rcases Finset.dvd_prod_of_mem (fun q => 1 + q) hp with ⟨v2, hv2⟩
    refine ⟨(u1 + 1) * v1 + (u2 + 1) * v2, ?_⟩
    rw [hv1, hv2, hu1, hu2]
    ring
  · push Not at hodd
    have hsub : n.primeFactors ⊆ {2} := fun p hp =>
      Finset.mem_singleton.mpr (hodd p hp)
    rcases Finset.subset_singleton_iff.mp hsub with hemp | htwo
    · simp [hemp]
    · rw [htwo, Finset.prod_singleton, Finset.prod_singleton]
      have hf2 : 0 < n.factorization 2 := by
        have hmem : 2 ∈ n.primeFactors := htwo ▸ Finset.mem_singleton_self 2
        exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 (Nat.dvd_of_mem_primeFactors hmem)
      obtain ⟨k, hk⟩ : ∃ k, n.factorization 2 = k + 1 := ⟨n.factorization 2 - 1, by omega⟩
      rw [hk, pow_succ]
      exact ⟨2 ^ k + 2, by ring⟩

/-! ### Step 3 — Primorial-Core / Squarefree-Cofactor Factorization (`n = n_{<q} · s_{>q}`) -/

private lemma a053669_spec {n : ℕ} (hn : 1 ≤ n) :
    (a053669 n).Prime ∧ ¬ a053669 n ∣ n ∧ ∀ p : ℕ, p.Prime → p < a053669 n → p ∣ n := by
  have hne : ({p : ℕ | p.Prime ∧ ¬ p ∣ n}).Nonempty := by
    obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (n + 1)
    refine ⟨p, hp_prime, fun hdvd => ?_⟩
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun p hp hlt => ?_⟩
  by_contra hndvd
  exact not_le_of_gt hlt (Nat.sInf_le ⟨hp, hndvd⟩)

private lemma a003557_eq_prod {n : ℕ} (hn : 1 ≤ n) :
    a003557 n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) := by
  have hn0 : n ≠ 0 := by omega
  have hfact : n = rad n * ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) := by
    unfold rad
    rw [← Finset.prod_mul_distrib]
    conv_lhs => rw [← eq_prod_primeFactors_factorization hn0]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpos : 0 < n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn0
        (Nat.dvd_of_mem_primeFactors hp)
    conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ']
  exact (congrArg (· / rad n) hfact).trans (Nat.mul_div_right _ (rad_pos n))

private lemma a003557_pos {n : ℕ} (hn : 1 ≤ n) : 0 < a003557 n := by
  rw [a003557_eq_prod hn]
  exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _

private lemma filter_primeFactors_lt_a053669 {n : ℕ} (hn : 1 ≤ n) :
    n.primeFactors.filter (· < a053669 n) = Nat.primesLE (a053669 n - 1) := by
  have ⟨hq_prime, _, hsmall⟩ := a053669_spec hn
  have hq2 : 2 ≤ a053669 n := hq_prime.two_le
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp, _, _⟩, hlt⟩
    exact ⟨by omega, hp⟩
  · rintro ⟨hle, hp⟩
    have hlt : p < a053669 n := by omega
    exact ⟨⟨hp, hsmall p hp hlt, by omega⟩, hlt⟩

/-- Key exponent lemma (`SCOPING-S010.md` §2.2 Step 3): if `a003557 n < a053669 n`, every prime
divisor `p` of `n` with `¬ p < a053669 n` has `n.factorization p = 1`. -/
private lemma factorization_eq_one_of_ge_a053669 {n p : ℕ} (hn : 1 ≤ n)
    (hmq : a003557 n < a053669 n) (hp : p ∈ n.primeFactors) (hge : ¬ p < a053669 n) :
    n.factorization p = 1 := by
  have hn0 : n ≠ 0 := by omega
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < n.factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp_prime hn0 (Nat.dvd_of_mem_primeFactors hp)
  by_contra hne1
  have hge2 : 2 ≤ n.factorization p := by omega
  have hdvd : p ^ (n.factorization p - 1) ∣ a003557 n := by
    rw [a003557_eq_prod hn]
    exact Finset.dvd_prod_of_mem _ hp
  have hp_dvd_m : p ∣ a003557 n := by
    refine dvd_trans ?_ hdvd
    conv_lhs => rw [← pow_one p]
    exact pow_dvd_pow p (by omega)
  have hpm : p ≤ a003557 n := Nat.le_of_dvd (a003557_pos hn) hp_dvd_m
  omega

/-- Primorial-core reduction: if `1 ≤ n` and `m := a003557 n < q := a053669 n`, then `1 ≤ m` and
`n = (m * primorial (q - 1)) * s` for a coprime squarefree cofactor `s`, reducing `2 * n ≤ ...`
to the primorial core `c = m * primorial (q - 1)`. -/
theorem primorial_core_reduction {n : ℕ} (hn : 1 ≤ n) (hmq : a003557 n < a053669 n)
    (hcore : 2 * (a003557 n * primorial (a053669 n - 1)) ≤
      a034448 (a003557 n * primorial (a053669 n - 1)) +
        a048250 (a003557 n * primorial (a053669 n - 1))) :
    2 * n ≤ a034448 n + a048250 n := by
  have hn0 : n ≠ 0 := by omega
  set q := a053669 n
  set m := a003557 n
  set S_lt := n.primeFactors.filter (· < q)
  set S_ge := n.primeFactors.filter (fun p => ¬ p < q)
  set c := ∏ p ∈ S_lt, p ^ n.factorization p
  set s := ∏ p ∈ S_ge, p ^ n.factorization p
  have hcs : c * s = n := by
    dsimp [c, s, S_lt, S_ge]
    rw [Finset.prod_filter_mul_prod_filter_not]
    exact eq_prod_primeFactors_factorization hn0
  have hs_simp : s = ∏ p ∈ S_ge, p := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [factorization_eq_one_of_ge_a053669 hn hmq hp.1 hp.2, pow_one]
  have hs_sq : Squarefree s := by
    rw [hs_simp]
    exact squarefree_prod_primes fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hm_eq : m = ∏ p ∈ S_lt, p ^ (n.factorization p - 1) := by
    have hsplit := Finset.prod_filter_mul_prod_filter_not n.primeFactors (· < q)
      (fun p => p ^ (n.factorization p - 1))
    have hge1 : ∏ p ∈ S_ge, p ^ (n.factorization p - 1) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      rw [Finset.mem_filter] at hp
      rw [factorization_eq_one_of_ge_a053669 hn hmq hp.1 hp.2]
      simp
    dsimp [m]
    rw [a003557_eq_prod hn, ← hsplit, hge1, mul_one]
  have hc_eq : c = m * primorial (q - 1) := by
    have hprim : primorial (q - 1) = ∏ p ∈ S_lt, p := by
      dsimp [S_lt, q]
      rw [primorial_eq_prod_primesLE, filter_primeFactors_lt_a053669 hn]
    dsimp [c]
    rw [hm_eq, mul_comm, hprim, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_mem : p ∈ n.primeFactors := (Finset.mem_filter.mp hp).1
    have hpos : 0 < n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp_mem) hn0
        (Nat.dvd_of_mem_primeFactors hp_mem)
    conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ']
  have hcop : Nat.Coprime c s := by
    rw [hs_simp]
    refine coprime_prod_left fun p hp => ?_
    refine coprime_prod_right fun r hr => ?_
    rw [Finset.mem_filter] at hp hr
    have hp_prime := Nat.prime_of_mem_primeFactors hp.1
    have hr_prime := Nat.prime_of_mem_primeFactors hr.1
    have hpr : p ≠ r := by omega
    exact (Nat.coprime_primes hp_prime hr_prime).mpr hpr |>.pow_left _
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at hcs
    exact hn0 hcs.symm
  have hs0 : s ≠ 0 := hs_sq.ne_zero
  have ⟨hus_eq, hs_le⟩ := squarefree_a034448_eq_a048250 hs_sq
  rw [← hcs, a034448_mul_of_coprime hc0 hs0 hcop, a048250_mul_of_coprime hc0 hs0 hcop,
    hus_eq, ← add_mul, hc_eq]
  calc
    2 * (m * primorial (q - 1) * s) = (2 * (m * primorial (q - 1))) * s := by ring
    _ ≤ (a034448 (m * primorial (q - 1)) + a048250 (m * primorial (q - 1))) * s :=
      Nat.mul_le_mul_right s hcore
    _ ≤ (a034448 (m * primorial (q - 1)) + a048250 (m * primorial (q - 1))) * a048250 s :=
      Nat.mul_le_mul_left _ hs_le

/-- Explicit Euler products for any primorial core `m * primorial (q - 1)` (`1 ≤ m < q`). -/
theorem primorial_core_euler_products {q m : ℕ} (hm1 : 1 ≤ m) (hmq : m < q) :
    a034448 (m * primorial (q - 1)) =
      ∏ p ∈ Nat.primesLE (q - 1), (1 + p ^ (m.factorization p + 1)) ∧
    a048250 (m * primorial (q - 1)) =
      ∏ p ∈ Nat.primesLE (q - 1), (1 + p) := by
  have hm0 : m ≠ 0 := by omega
  have hp0 : primorial (q - 1) ≠ 0 := primorial_ne_zero (q - 1)
  have hmp0 : m * primorial (q - 1) ≠ 0 := mul_ne_zero hm0 hp0
  have hm_sub : m.primeFactors ⊆ Nat.primesLE (q - 1) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    have hle : p ≤ m := Nat.le_of_dvd (by omega) hp.2.1
    exact ⟨by omega, hp.1⟩
  have hpf : (m * primorial (q - 1)).primeFactors = Nat.primesLE (q - 1) := by
    rw [Nat.primeFactors_mul hm0 hp0, primeFactors_primorial]
    exact Finset.union_eq_right.mpr hm_sub
  have hsq_prim : Squarefree (primorial (q - 1)) := by
    rw [primorial_eq_prod_primesLE]
    exact squarefree_prod_primes fun _ hp => Nat.prime_of_mem_primesLE hp
  rw [a034448_eq_prod hmp0, a048250_eq_prod hmp0, hpf]
  refine ⟨Finset.prod_congr rfl fun p hp => ?_, rfl⟩
  rw [Nat.factorization_mul hm0 hp0, Finsupp.add_apply]
  have hp_mem : p ∈ (primorial (q - 1)).primeFactors := by rwa [primeFactors_primorial]
  have hle1 : (primorial (q - 1)).factorization p ≤ 1 := hsq_prim.natFactorization_le_one p
  have hpos1 : 0 < (primorial (q - 1)).factorization p :=
    Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primesLE hp) hp0
      (Nat.dvd_of_mem_primeFactors hp_mem)
  have hf1 : (primorial (q - 1)).factorization p = 1 := by omega
  rw [hf1]

private lemma m_mul_primorial_eq_prod {q m : ℕ} (hm1 : 1 ≤ m) (hmq : m < q) :
    m * primorial (q - 1) =
      ∏ p ∈ Nat.primesLE (q - 1), p ^ (m.factorization p + 1) := by
  have hm0 : m ≠ 0 := by omega
  have hm_sub : m.primeFactors ⊆ Nat.primesLE (q - 1) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    have hle : p ≤ m := Nat.le_of_dvd (by omega) hp.2.1
    exact ⟨by omega, hp.1⟩
  have hm_prod : m = ∏ p ∈ Nat.primesLE (q - 1), p ^ m.factorization p := by
    conv_lhs => rw [← eq_prod_primeFactors_factorization hm0]
    exact Finset.prod_subset hm_sub fun p _ hp_not => by
      have hf0 : m.factorization p = 0 := Finsupp.notMem_support_iff.mp hp_not
      rw [hf0, pow_zero]
  conv_lhs => rw [hm_prod, primorial_eq_prod_primesLE]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => by rw [pow_succ]

/-- Rational Euler-product identity for `a034448 (m * primorial (q - 1)) / (m * primorial (q - 1))`. -/
private lemma ustar_core_rat_eq {q m : ℕ} (hm1 : 1 ≤ m) (hmq : m < q) :
    (a034448 (m * primorial (q - 1)) : ℚ) / (m * primorial (q - 1) : ℚ) =
      ∏ p ∈ Nat.primesLE (q - 1),
        (1 + 1 / ((p : ℚ) ^ (m.factorization p + 1))) := by
  have heul := (primorial_core_euler_products hm1 hmq).1
  have hden := m_mul_primorial_eq_prod hm1 hmq
  have hcast_num : (a034448 (m * primorial (q - 1)) : ℚ) =
      ∏ p ∈ Nat.primesLE (q - 1), (1 + (p : ℚ) ^ (m.factorization p + 1)) := by
    rw [heul]
    push_cast
    rfl
  have hcast_den : ((m * primorial (q - 1) : ℕ) : ℚ) =
      ∏ p ∈ Nat.primesLE (q - 1), (p : ℚ) ^ (m.factorization p + 1) := by
    rw [hden]
    push_cast
    rfl
  rw [← Nat.cast_mul, hcast_num, hcast_den, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp_pos : (0 : ℚ) < p := Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE hp).pos
  have hpow_ne : ((p : ℚ) ^ (m.factorization p + 1)) ≠ 0 := pow_ne_zero _ hp_pos.ne'
  field_simp [hpow_ne]
  ring

/-- Subset-deletion lower bound on the `ℚ` Euler product: for `2 ≤ m < q`,
`∏_{p ∈ primesLE(q-1) \ m.primeFactors} (1 + 1/p) < a034448(c)/c`. -/
private lemma ustar_core_rat_gt_sdiff {q m : ℕ} (hm2 : 2 ≤ m) (hmq : m < q) :
    ∏ p ∈ Nat.primesLE (q - 1) \ m.primeFactors, (1 + 1 / (p : ℚ)) <
      (a034448 (m * primorial (q - 1)) : ℚ) / (m * primorial (q - 1) : ℚ) := by
  have hm1 : 1 ≤ m := by omega
  have hm_sub : m.primeFactors ⊆ Nat.primesLE (q - 1) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨le_trans (Nat.le_of_dvd (by omega) hp.2.1) (by omega), hp.1⟩
  rw [ustar_core_rat_eq hm1 hmq, ← Finset.prod_sdiff hm_sub]
  have hsdiff_eq :
      ∏ p ∈ Nat.primesLE (q - 1) \ m.primeFactors,
        (1 + 1 / ((p : ℚ) ^ (m.factorization p + 1))) =
      ∏ p ∈ Nat.primesLE (q - 1) \ m.primeFactors, (1 + 1 / (p : ℚ)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Finset.mem_sdiff] at hp
    have hf0 : m.factorization p = 0 := Finsupp.notMem_support_iff.mp hp.2
    rw [hf0, zero_add, pow_one]
  rw [hsdiff_eq]
  have hsdiff_pos :
      0 < ∏ p ∈ Nat.primesLE (q - 1) \ m.primeFactors, (1 + 1 / (p : ℚ)) :=
    Finset.prod_pos fun p hp => by
      have hp_pos : (0 : ℚ) < p :=
        Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1).pos
      positivity
  have hB_nonempty : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hm2
  obtain ⟨p0, hp0⟩ := hB_nonempty
  have hB_gt1 :
      1 < ∏ p ∈ m.primeFactors, (1 + 1 / ((p : ℚ) ^ (m.factorization p + 1))) := by
    rw [← Finset.mul_prod_erase _ _ hp0]
    have hp0_pos : (0 : ℚ) < p0 :=
      Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp0).pos
    have h1 : 1 < 1 + 1 / ((p0 : ℚ) ^ (m.factorization p0 + 1)) := by
      have : (0 : ℚ) < 1 / ((p0 : ℚ) ^ (m.factorization p0 + 1)) := by positivity
      linarith
    have h2 : 1 ≤ ∏ p ∈ m.primeFactors.erase p0,
        (1 + 1 / ((p : ℚ) ^ (m.factorization p + 1))) :=
      rat_one_le_prod fun p hp => by
        have hp_pos : (0 : ℚ) < p :=
          Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).pos
        have : (0 : ℚ) ≤ 1 / ((p : ℚ) ^ (m.factorization p + 1)) := by positivity
        linarith
    nlinarith
  nlinarith

/-! ### Structural Kernel-Computable `ordPow` and `√p` Trial-Division `isPrimeB` -/

private def ordPowAux (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, m =>
    if decide (2 ≤ p) && decide (0 < m) && (m % p == 0) then
      p * ordPowAux p fuel (m / p)
    else 1

private def ordPow (p m : ℕ) : ℕ :=
  ordPowAux p m m

private lemma ordPowAux_eq_pow_factorization {p : ℕ} (hp : p.Prime) :
    ∀ fuel m : ℕ, m ≠ 0 → m ≤ fuel → ordPowAux p fuel m = p ^ m.factorization p
  | 0, m, hm0, hle => absurd (Nat.eq_zero_of_le_zero hle) hm0
  | fuel + 1, m, hm0, hle => by
    unfold ordPowAux
    have hp2 : 2 ≤ p := hp.two_le
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    by_cases hdvd : p ∣ m
    · have hmod : m % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have hcond : (decide (2 ≤ p) && decide (0 < m) && (m % p == 0)) = true := by
        simp [hp2, hm_pos, hmod]
      rw [hcond]
      simp only [↓reduceIte]
      have hdiv_lt : m / p < m := Nat.div_lt_self hm_pos hp2
      have hmul : p * (m / p) = m := Nat.mul_div_cancel' hdvd
      have hdiv0 : m / p ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at hmul
        exact hm0 hmul.symm
      rw [ordPowAux_eq_pow_factorization hp fuel (m / p) hdiv0 (by omega)]
      conv_rhs => rw [← hmul, Nat.factorization_mul hp.ne_zero hdiv0, Finsupp.add_apply,
        hp.factorization_self, add_comm, pow_succ']
    · have hmod : m % p ≠ 0 := fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
      have hcond : (decide (2 ≤ p) && decide (0 < m) && (m % p == 0)) = false := by
        simp [hmod]
      rw [hcond]
      simp [Nat.factorization_eq_zero_of_not_dvd hdvd]

private lemma ordPow_eq_pow_factorization {p m : ℕ} (hp : p.Prime) (hm0 : m ≠ 0) :
    ordPow p m = p ^ m.factorization p :=
  ordPowAux_eq_pow_factorization hp m m hm0 le_rfl

private def noDivFrom (p d : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
    if decide (p < d * d) then true
    else (p % d != 0) && noDivFrom p (d + 1) fuel

private lemma noDivFrom_spec (p : ℕ) :
    ∀ fuel d : ℕ, 2 ≤ d → p ≤ d + fuel →
      (noDivFrom p d fuel = true ↔ ∀ m : ℕ, d ≤ m → m * m ≤ p → p % m ≠ 0)
  | 0, d, hd2, hpd => by
    unfold noDivFrom
    simp only [true_iff]
    intro m hdm hm2
    nlinarith
  | fuel + 1, d, hd2, hpd => by
    unfold noDivFrom
    by_cases hlt : p < d * d
    · simp only [decide_eq_true hlt, ↓reduceIte, true_iff]
      intro m hdm hm2
      nlinarith
    · simp only [decide_eq_false hlt, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, bne_iff_ne]
      have ih := noDivFrom_spec p fuel (d + 1) (by omega) (by omega)
      rw [ih]
      constructor
      · rintro ⟨h0, hrest⟩ m hdm hm2
        by_cases hmd : m = d
        · subst hmd; exact h0
        · exact hrest m (by omega) hm2
      · intro hall
        exact ⟨hall d le_rfl (by omega), fun m hdm hm2 => hall m (by omega) hm2⟩

private def isPrimeB (p : ℕ) : Bool :=
  decide (2 ≤ p) && noDivFrom p 2 p

private lemma isPrimeB_iff_prime (p : ℕ) : isPrimeB p = true ↔ p.Prime := by
  unfold isPrimeB
  rw [Bool.and_eq_true, decide_eq_true_eq, noDivFrom_spec p p 2 le_rfl (by omega),
    Nat.prime_def_lt']
  constructor
  · rintro ⟨hp2, hall⟩
    refine ⟨hp2, fun m hm2 hmp hdvd => ?_⟩
    rcases hdvd with ⟨q, hmq⟩
    have hq2 : 2 ≤ q := by
      by_contra hlt2
      have hq01 : q = 0 ∨ q = 1 := by omega
      rcases hq01 with rfl | rfl <;> omega
    by_cases hmq_le : m ≤ q
    · have hmsq : m * m ≤ p := by nlinarith
      exact hall m hm2 hmsq (by rw [hmq, Nat.mul_mod_right])
    · have hqsq : q * q ≤ p := by nlinarith
      exact hall q hq2 hqsq (by rw [hmq, mul_comm, Nat.mul_mod_right])
  · rintro ⟨hp2, hndvd⟩
    refine ⟨hp2, fun m hm2 hmsq hmod => ?_⟩
    have hmp : m < p := by
      by_contra hge
      have hmeq : m = p := by nlinarith
      subst hmeq
      nlinarith
    exact hndvd m hm2 hmp (Nat.dvd_of_mod_eq_zero hmod)

private lemma list_prod_pos {l : List ℕ} (h : ∀ x ∈ l, 0 < x) : 0 < l.prod := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    rw [List.prod_cons]
    exact mul_pos (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

private def isSortedLt : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: xs => decide (a < b) && isSortedLt (b :: xs)

private lemma pairwise_lt_of_isSortedLt : ∀ l : List ℕ, isSortedLt l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: xs, h => by
    unfold isSortedLt at h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_lt_of_isSortedLt (b :: xs) h.2
    have ih_head : ∀ x ∈ xs, b < x := (List.pairwise_cons.mp ih).1
    refine List.pairwise_cons.mpr ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.mp hx with rfl | hxs
    · exact h.1
    · exact lt_trans h.1 (ih_head x hxs)

/-! ### Step 5 — Regime I (`q ≤ 13`: All `35` Finite Primorial Cores) -/

private def checkRegimeOneCore (prim : ℕ) (ps : List ℕ) (m : ℕ) : Bool :=
  decide (2 * (m * prim) ≤
    (ps.map (fun p => 1 + p * ordPow p m)).prod + (ps.map (fun p => 1 + p)).prod)

private lemma regime_one_core_via_list {q prim : ℕ} {ps : List ℕ}
    (hprim : primorial (q - 1) = prim) (hnodup : ps.Nodup)
    (hps : ps.toFinset = Nat.primesLE (q - 1))
    (hall : ((List.range (q - 1)).map (· + 1)).all (checkRegimeOneCore prim ps) = true)
    {m : ℕ} (hm1 : 1 ≤ m) (hmq : m < q) :
    2 * (m * primorial (q - 1)) ≤
      a034448 (m * primorial (q - 1)) + a048250 (m * primorial (q - 1)) := by
  have hm0 : m ≠ 0 := by omega
  have ⟨hu, hs⟩ := primorial_core_euler_products hm1 hmq
  have hu_list : a034448 (m * primorial (q - 1)) =
      (ps.map (fun p => 1 + p * ordPow p m)).prod := by
    rw [hu, ← hps, List.prod_toFinset _ hnodup]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    have hp_mem : p ∈ Nat.primesLE (q - 1) := hps ▸ List.mem_toFinset.mpr hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primesLE hp_mem
    rw [ordPow_eq_pow_factorization hp_prime hm0, pow_succ']
  have hs_list : a048250 (m * primorial (q - 1)) = (ps.map (fun p => 1 + p)).prod := by
    rw [hs, ← hps, List.prod_toFinset _ hnodup]
  rw [hu_list, hs_list, hprim]
  have hmem : m ∈ (List.range (q - 1)).map (· + 1) := by
    rw [List.mem_map]
    exact ⟨m - 1, List.mem_range.mpr (by omega), by omega⟩
  have hchk := List.all_eq_true.mp hall m hmem
  unfold checkRegimeOneCore at hchk
  exact of_decide_eq_true hchk

private lemma regime_one_core_bound {q m : ℕ} (hq : q.Prime) (hq13 : q ≤ 13)
    (hm1 : 1 ≤ m) (hmq : m < q) :
    2 * (m * primorial (q - 1)) ≤
      a034448 (m * primorial (q - 1)) + a048250 (m * primorial (q - 1)) := by
  have hq2 : 2 ≤ q := hq.two_le
  interval_cases q
  · exact regime_one_core_via_list (prim := 1) (ps := []) (by decide) (by decide) (by decide) (by decide) hm1 hmq
  · exact regime_one_core_via_list (prim := 2) (ps := [2]) (by decide) (by decide) (by decide) (by decide) hm1 hmq
  · exact absurd hq (by norm_num)
  · exact regime_one_core_via_list (prim := 6) (ps := [2, 3]) (by decide) (by decide) (by decide) (by decide) hm1 hmq
  · exact absurd hq (by norm_num)
  · exact regime_one_core_via_list (prim := 30) (ps := [2, 3, 5]) (by decide) (by decide) (by decide) (by decide) hm1 hmq
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact regime_one_core_via_list (prim := 210) (ps := [2, 3, 5, 7]) (by decide) (by decide) (by decide) (by decide) hm1 hmq
  · exact absurd hq (by norm_num)
  · exact regime_one_core_via_list (prim := 2310) (ps := [2, 3, 5, 7, 11]) (by decide) (by decide) (by decide) (by decide) hm1 hmq

/-! ### Step 7 — Regime III (`k ≥ 11`: Pure-`ℚ` Harmonic-Squarefree + Telescoping + Cauchy Dyadic) -/

/-- Prime-set max bound via `p ↦ (p + 1) / 2`: any nonempty `B` of primes has
`2 * B.card - 1 ≤ B.max' hB`. -/
private lemma two_mul_card_sub_one_le_max_primes {B : Finset ℕ} (hB : B.Nonempty)
    (hpB : ∀ p ∈ B, p.Prime) :
    2 * B.card - 1 ≤ B.max' hB := by
  set pmax := B.max' hB
  let g : ℕ → ℕ := fun p => (p + 1) / 2
  have hinj : Set.InjOn g ↑B := by
    intro x hx y hy hxy
    dsimp [g] at hxy
    have hxp := hpB x hx
    have hyp := hpB y hy
    have hx2 := hxp.two_le
    have hy2 := hyp.two_le
    by_cases h1 : x = 2
    · subst h1; omega
    · by_cases h2 : y = 2
      · subst h2; omega
      · rcases hxp.odd_of_ne_two h1 with ⟨a, rfl⟩
        rcases hyp.odd_of_ne_two h2 with ⟨b, rfl⟩
        omega
  have hsub : B.image g ⊆ Finset.Icc 1 ((pmax + 1) / 2) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    dsimp [g]
    have hx2 := (hpB x hx).two_le
    have hx_le : x ≤ pmax := Finset.le_max' B x hx
    rw [Finset.mem_Icc]
    omega
  have hcard : B.card ≤ (pmax + 1) / 2 := by
    calc
      B.card = (B.image g).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 ((pmax + 1) / 2)).card := Finset.card_le_card hsub
      _ = (pmax + 1) / 2 := by simp [Nat.card_Icc]
  omega

private def oddProd (n : ℕ) : ℕ :=
  2 * ∏ j ∈ Finset.Icc 1 n, (2 * j + 1)

private lemma oddProd_succ (n : ℕ) : oddProd (n + 1) = oddProd n * (2 * n + 3) := by
  unfold oddProd
  have hmem : n + 1 ∉ Finset.Icc 1 n := by simp
  have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc, Finset.prod_insert hmem]
  ring

/-- Product of `k ≥ 1` distinct primes is at least `2 * ∏_{j=1}^{k-1} (2j + 1)`. -/
private lemma prod_primes_ge_oddProd :
    ∀ k : ℕ, 1 ≤ k → ∀ B : Finset ℕ, B.card = k → (∀ p ∈ B, p.Prime) →
      oddProd (k - 1) ≤ ∏ p ∈ B, p := by
  intro k hk
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction d with
  | zero =>
    intro B hcard hpB
    obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
    simp only [Nat.add_sub_cancel, oddProd, Finset.Icc_eq_empty (by omega : ¬ 1 ≤ 0),
      Finset.prod_empty, mul_one, Finset.prod_singleton]
    exact (hpB p (Finset.mem_singleton_self p)).two_le
  | succ d ih =>
    intro B hcard hpB
    have hB : B.Nonempty := Finset.card_pos.mp (by omega)
    set pmax := B.max' hB
    have hpmax_mem : pmax ∈ B := Finset.max'_mem B hB
    have hpmax_ge : 2 * d + 3 ≤ pmax := by
      have := two_mul_card_sub_one_le_max_primes hB hpB
      omega
    have hcard' : (B.erase pmax).card = d + 1 := by
      rw [Finset.card_erase_of_mem hpmax_mem, hcard, Nat.add_sub_cancel]
    have hpB' : ∀ p ∈ B.erase pmax, p.Prime := fun p hp => hpB p (Finset.mem_of_mem_erase hp)
    have ihB := ih (B.erase pmax) hcard' hpB'
    simp only [Nat.add_sub_cancel] at ihB ⊢
    rw [← Finset.mul_prod_erase B (fun p => p) hpmax_mem, mul_comm, oddProd_succ]
    exact Nat.mul_le_mul ihB hpmax_ge

/-- Odd-prime telescoping upper bound: `(∏_{p ∈ B} (1 + 1/p))^2 ≤ (9/4) * |B|`. -/
private lemma sq_prod_one_add_inv_primes_le :
    ∀ k : ℕ, 1 ≤ k → ∀ B : Finset ℕ, B.card = k → (∀ p ∈ B, p.Prime) →
      (∏ p ∈ B, (1 + 1 / (p : ℚ))) ^ 2 ≤ (9 : ℚ) / 4 * k := by
  intro k hk
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction d with
  | zero =>
    intro B hcard hpB
    obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
    simp only [Finset.prod_singleton]
    have hp2 : (2 : ℚ) ≤ p := Nat.ofNat_le_cast.mpr (hpB p (Finset.mem_singleton_self p)).two_le
    have hinv : 1 / (p : ℚ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    have hpos : (0 : ℚ) ≤ 1 + 1 / (p : ℚ) := by positivity
    push_cast
    nlinarith
  | succ d ih =>
    intro B hcard hpB
    have hB : B.Nonempty := Finset.card_pos.mp (by omega)
    set pmax := B.max' hB
    have hpmax_mem : pmax ∈ B := Finset.max'_mem B hB
    have hpmax_ge_nat : 2 * d + 3 ≤ pmax := by
      have := two_mul_card_sub_one_le_max_primes hB hpB
      omega
    have hpmax_ge : (2 * (d : ℚ) + 3) ≤ (pmax : ℚ) := by exact_mod_cast hpmax_ge_nat
    have hcard' : (B.erase pmax).card = d + 1 := by
      rw [Finset.card_erase_of_mem hpmax_mem, hcard, Nat.add_sub_cancel]
    have hpB' : ∀ p ∈ B.erase pmax, p.Prime := fun p hp => hpB p (Finset.mem_of_mem_erase hp)
    have ihB := ih (B.erase pmax) hcard' hpB'
    rw [← Finset.mul_prod_erase B (fun p : ℕ => (1 + 1 / (p : ℚ))) hpmax_mem, mul_pow]
    have hd_pos : (0 : ℚ) < 2 * (d : ℚ) + 3 := by positivity
    have hinv : 1 / (pmax : ℚ) ≤ 1 / (2 * (d : ℚ) + 3) :=
      one_div_le_one_div_of_le hd_pos hpmax_ge
    have hfac_nonneg : (0 : ℚ) ≤ 1 + 1 / (pmax : ℚ) := by positivity
    have hfac_le : (1 + 1 / (pmax : ℚ)) ^ 2 ≤
        ((2 * (d : ℚ) + 4) / (2 * (d : ℚ) + 3)) ^ 2 := by
      have heq : 1 + 1 / (2 * (d : ℚ) + 3) = (2 * (d : ℚ) + 4) / (2 * (d : ℚ) + 3) := by
        field_simp [hd_pos.ne']
        ring
      rw [← heq]
      nlinarith
    have hprod_sq_nonneg : (0 : ℚ) ≤ (∏ x ∈ B.erase pmax, (1 + 1 / (x : ℚ))) ^ 2 := sq_nonneg _
    have htele : ((2 * (d : ℚ) + 4) / (2 * (d : ℚ) + 3)) ^ 2 * ((9 : ℚ) / 4 * ((d : ℚ) + 1)) ≤
        (9 : ℚ) / 4 * ((d : ℚ) + 1 + 1) := by
      rw [div_pow]
      have hden_pos : (0 : ℚ) < (2 * (d : ℚ) + 3) ^ 2 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
      have hd0 : (0 : ℚ) ≤ d := Nat.cast_nonneg d
      nlinarith
    push_cast at ihB ⊢
    calc
      (1 + 1 / (pmax : ℚ)) ^ 2 * (∏ x ∈ B.erase pmax, (1 + 1 / (x : ℚ))) ^ 2
          ≤ ((2 * (d : ℚ) + 4) / (2 * (d : ℚ) + 3)) ^ 2 * ((9 : ℚ) / 4 * ((d : ℚ) + 1)) :=
            mul_le_mul hfac_le ihB hprod_sq_nonneg (by positivity)
      _ ≤ (9 : ℚ) / 4 * ((d : ℚ) + 1 + 1) := htele

private def harm (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 N, (1 : ℚ) / (j : ℚ)

private lemma harm_mono {M N : ℕ} (h : M ≤ N) : harm M ≤ harm N := by
  unfold harm
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro x hx
  rw [Finset.mem_Icc] at hx ⊢
  omega

/-- Cauchy dyadic lower bound: `1 + L / 2 ≤ H(2^L)`. -/
private lemma harm_two_pow_ge (L : ℕ) : 1 + (L : ℚ) / 2 ≤ harm (2 ^ L) := by
  induction L with
  | zero =>
    unfold harm
    norm_num
  | succ L ih =>
    set S_lo : Finset ℕ := Finset.Icc 1 (2 ^ L)
    set S_hi : Finset ℕ := Finset.Icc (2 ^ L + 1) (2 ^ (L + 1))
    have hdisj : Disjoint S_lo S_hi := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_Icc] at hx1 hx2
      omega
    have hunion : Finset.Icc 1 (2 ^ (L + 1)) = S_lo ∪ S_hi := by
      have hpos : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      have hle : 2 ^ L ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      ext x
      simp only [S_lo, S_hi, Finset.mem_Icc, Finset.mem_union]
      omega
    have hcard : S_hi.card = 2 ^ L := by
      dsimp [S_hi]
      rw [Nat.card_Icc, pow_succ]
      omega
    have hterm : ∀ j ∈ S_hi,
        (1 : ℚ) / ((2 ^ (L + 1) : ℕ) : ℚ) ≤ (1 : ℚ) / (j : ℚ) := by
      intro j hj
      dsimp [S_hi] at hj
      rw [Finset.mem_Icc] at hj
      have hj_pos : (0 : ℚ) < j := by exact_mod_cast (show 0 < j by omega)
      have hj_le : (j : ℚ) ≤ ((2 ^ (L + 1) : ℕ) : ℚ) := by exact_mod_cast hj.2
      exact one_div_le_one_div_of_le hj_pos hj_le
    have hconst_sum : ∑ _j ∈ S_hi, ((1 : ℚ) / ((2 ^ (L + 1) : ℕ) : ℚ)) = (1 : ℚ) / 2 := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      push_cast [pow_succ]
      have h2L : ((2 : ℚ) ^ L) ≠ 0 := pow_ne_zero L (by norm_num)
      field_simp [h2L]
    have htail : (1 : ℚ) / 2 ≤ ∑ j ∈ S_hi, (1 : ℚ) / (j : ℚ) := by
      rw [← hconst_sum]
      exact Finset.sum_le_sum hterm
    unfold harm at ih ⊢
    rw [hunion, Finset.sum_union hdisj]
    dsimp [S_lo] at *
    push_cast
    linarith

private lemma sum_inv_sq_lt (N : ℕ) (hN : 3 ≤ N) :
    ∑ b ∈ Finset.Icc 1 N, (1 : ℚ) / (b : ℚ) ^ 2 < 61 / 36 := by
  suffices h : ∑ b ∈ Finset.Icc 1 N, (1 : ℚ) / (b : ℚ) ^ 2 ≤ 61 / 36 - 1 / (N : ℚ) by
    have hNpos : (0 : ℚ) < 1 / (N : ℚ) := by
      have : (0 : ℚ) < N := by exact_mod_cast (show 0 < N by omega)
      positivity
    linarith
  obtain ⟨d, rfl⟩ : ∃ d, N = d + 3 := ⟨N - 3, by omega⟩
  clear hN
  induction d with
  | zero =>
    have hIcc : Finset.Icc 1 3 = {1, 2, 3} := by decide
    rw [hIcc]
    norm_num
  | succ d ih =>
    have hmem : d + 4 ∉ Finset.Icc 1 (d + 3) := by simp
    have hIcc : Finset.Icc 1 (d + 1 + 3) = insert (d + 4) (Finset.Icc 1 (d + 3)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert hmem]
    have hstep : 61 / 36 - 1 / ((d + 3 : ℕ) : ℚ) + 1 / ((d + 4 : ℕ) : ℚ) ^ 2 ≤
        61 / 36 - 1 / ((d + 1 + 3 : ℕ) : ℚ) := by
      have h1 : (0 : ℚ) < ((d + 3 : ℕ) : ℚ) := by positivity
      have h2 : (0 : ℚ) < ((d + 4 : ℕ) : ℚ) := by positivity
      have heq4 : ((d + 1 + 3 : ℕ) : ℚ) = ((d + 4 : ℕ) : ℚ) := by push_cast; ring
      rw [heq4]
      suffices hdiff : 1 / ((d + 4 : ℕ) : ℚ) ^ 2 ≤
          1 / ((d + 3 : ℕ) : ℚ) - 1 / ((d + 4 : ℕ) : ℚ) by linarith
      rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      nlinarith
    linarith

private lemma sum_inv_divisors_primorial (N : ℕ) :
    ∑ a ∈ (primorial N).divisors, (1 : ℚ) / (a : ℚ) =
      ∏ p ∈ Nat.primesLE N, (1 + 1 / (p : ℚ)) := by
  have hp0 : primorial N ≠ 0 := primorial_ne_zero N
  have hsq_prim : Squarefree (primorial N) := by
    rw [primorial_eq_prod_primesLE]
    exact squarefree_prod_primes fun _ hp => Nat.prime_of_mem_primesLE hp
  rw [Finset.prod_one_add]
  refine Finset.sum_bij (fun a _ => a.primeFactors) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Nat.mem_divisors] at ha
    rw [Finset.mem_powerset, ← primeFactors_primorial]
    exact Nat.primeFactors_mono ha.1 hp0
  · intro a₁ ha₁ a₂ ha₂ h
    rw [Nat.mem_divisors] at ha₁ ha₂
    have hs1 : Squarefree a₁ := hsq_prim.squarefree_of_dvd ha₁.1
    have hs2 : Squarefree a₂ := hsq_prim.squarefree_of_dvd ha₂.1
    rw [← Nat.prod_primeFactors_of_squarefree hs1, ← Nat.prod_primeFactors_of_squarefree hs2, h]
  · intro T hT
    rw [Finset.mem_powerset] at hT
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primesLE (hT hp)
    refine ⟨∏ p ∈ T, p, ?_, Nat.primeFactors_prod hTp⟩
    rw [Nat.mem_divisors]
    refine ⟨?_, hp0⟩
    rw [primorial_eq_prod_primesLE]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hT
  · intro a ha
    rw [Nat.mem_divisors] at ha
    have hsa : Squarefree a := hsq_prim.squarefree_of_dvd ha.1
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsa]
    push_cast
    simp [one_div, Finset.prod_inv_distrib]

/-- Harmonic-squarefree cover (`SCOPING-S010.md` §2.2 Step 7): for `N ≥ 3`,
`harm N < (61 / 36) * ∏_{p ≤ N} (1 + 1 / p)`. -/
private lemma harm_lt_zeta2_mul_primorial_prod {N : ℕ} (hN : 3 ≤ N) :
    harm N < (61 : ℚ) / 36 * ∏ p ∈ Nat.primesLE N, (1 + 1 / (p : ℚ)) := by
  have hp0 : primorial N ≠ 0 := primorial_ne_zero N
  have hex : ∀ j : ℕ, ∃ p : ℕ × ℕ,
      (0 < j → 0 < p.1 ∧ 0 < p.2 ∧ p.2 ^ 2 * p.1 = j ∧ Squarefree p.1) := by
    intro j
    by_cases hj : 0 < j
    · obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hj
      exact ⟨(a, b), fun _ => ⟨ha, hb, hab, hsq⟩⟩
    · exact ⟨(1, 1), fun h => absurd h hj⟩
  choose φ hφ using hex
  have hinj : Set.InjOn φ ↑(Finset.Icc 1 N) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_Icc] at hi hj
    have ⟨_, _, eq_i, _⟩ := hφ i (by omega)
    have ⟨_, _, eq_j, _⟩ := hφ j (by omega)
    rw [← eq_i, ← eq_j, hij]
  have hsub : (Finset.Icc 1 N).image φ ⊆ (primorial N).divisors ×ˢ Finset.Icc 1 N := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    rw [Finset.mem_Icc] at hj
    have ⟨ha_pos, hb_pos, hab, ha_sq⟩ := hφ j (by omega)
    rw [Finset.mem_product, Nat.mem_divisors, Finset.mem_Icc]
    have hb2_pos : 1 ≤ (φ j).2 ^ 2 := by nlinarith
    have ha_le : (φ j).1 ≤ N := by nlinarith
    have hb_le : (φ j).2 ≤ N := by nlinarith
    have ha_dvd : (φ j).1 ∣ primorial N :=
      dvd_trans ha_sq.dvd_primorial (primorial_dvd_primorial ha_le)
    exact ⟨⟨ha_dvd, hp0⟩, ⟨by omega, hb_le⟩⟩
  have hcover : harm N ≤
      (∑ a ∈ (primorial N).divisors, (1 : ℚ) / (a : ℚ)) *
        (∑ b ∈ Finset.Icc 1 N, (1 : ℚ) / (b : ℚ) ^ 2) := by
    unfold harm
    have hsum_eq : ∑ j ∈ Finset.Icc 1 N, (1 : ℚ) / (j : ℚ) =
        ∑ x ∈ (Finset.Icc 1 N).image φ, ((1 : ℚ) / (x.1 : ℚ)) * ((1 : ℚ) / (x.2 : ℚ) ^ 2) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      have ⟨_, _, hab, _⟩ := hφ j (by omega)
      conv_lhs => rw [← hab]
      push_cast
      ring
    rw [hsum_eq, Finset.sum_mul_sum, ← Finset.sum_product']
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  rw [sum_inv_divisors_primorial] at hcover
  have hprod_pos : 0 < ∏ p ∈ Nat.primesLE N, (1 + 1 / (p : ℚ)) :=
    Finset.prod_pos fun p hp => by
      have : (0 : ℚ) < p := Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE hp).pos
      positivity
  have hsq_lt := sum_inv_sq_lt N hN
  nlinarith

private lemma oddProd_ge_two_pow {k : ℕ} (hk : 11 ≤ k) :
    2 ^ (34 + 4 * (k - 11)) ≤ oddProd (k - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = 11 + d := ⟨k - 11, by omega⟩
  clear hk
  induction d with
  | zero =>
    have hIcc : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
    change 2 ^ 34 ≤ oddProd 10
    unfold oddProd
    rw [hIcc]
    norm_num
  | succ d ih =>
    have hsub1 : 11 + (d + 1) - 1 = (11 + d - 1) + 1 := by omega
    have hsub2 : 11 + (d + 1) - 11 = d + 1 := by omega
    have hsub3 : 11 + d - 11 = d := by omega
    rw [hsub1, hsub2, oddProd_succ]
    rw [hsub3] at ih
    have hexp : 34 + 4 * (d + 1) = (34 + 4 * d) + 4 := by ring
    rw [hexp, pow_add]
    have hfactor : 2 ^ 4 ≤ 2 * (11 + d - 1) + 3 := by omega
    exact Nat.mul_le_mul ih hfactor

/-- Regime III (`k = m.primeFactors.card ≥ 11`, `q ≥ 17`): pure-`ℚ` closure without Mertens,
Bertrand, `Real.log`, or `native_decide`. -/
private lemma regime_three_ustar_gt_two {q m : ℕ} (hq : 17 ≤ q) (hm1 : 1 ≤ m) (hmq : m < q)
    (hk11 : 11 ≤ m.primeFactors.card) :
    2 * (m * primorial (q - 1)) < a034448 (m * primorial (q - 1)) := by
  set B := m.primeFactors
  set k := B.card
  have hm2 : 2 ≤ m := by
    by_contra hm_le1
    have hmeq : m = 1 := by omega
    subst hmeq
    simp [B, k] at hk11
  have hB_sub : B ⊆ Nat.primesLE (q - 1) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨le_trans (Nat.le_of_dvd (by omega) hp.2.1) (by omega), hp.1⟩
  have hq1_ge : 2 ^ (34 + 4 * (k - 11)) ≤ q - 1 := by
    have h1 : oddProd (k - 1) ≤ ∏ p ∈ B, p :=
      prod_primes_ge_oddProd k (by omega) B rfl fun _ hp => Nat.prime_of_mem_primeFactors hp
    have h2 : ∏ p ∈ B, p ≤ m := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd m)
    exact le_trans (oddProd_ge_two_pow hk11) (le_trans h1 (by omega))
  have hharm_ge : 18 + 2 * ((k : ℚ) - 11) ≤ harm (q - 1) := by
    have h1 := harm_two_pow_ge (34 + 4 * (k - 11))
    have h2 := harm_mono hq1_ge
    have hcast : ((34 + 4 * (k - 11) : ℕ) : ℚ) = 34 + 4 * ((k : ℚ) - 11) := by
      have hk_le : 11 ≤ k := hk11
      push_cast [Nat.cast_sub hk_le]
      ring
    rw [hcast] at h1
    linarith
  have hharm_lt := harm_lt_zeta2_mul_primorial_prod (N := q - 1) (by omega)
  have hfull_gt : (36 : ℚ) / 61 * (2 * (k : ℚ) - 4) <
      ∏ p ∈ Nat.primesLE (q - 1), (1 + 1 / (p : ℚ)) := by
    linarith
  have hsplit : ∏ p ∈ Nat.primesLE (q - 1), (1 + 1 / (p : ℚ)) =
      (∏ p ∈ Nat.primesLE (q - 1) \ B, (1 + 1 / (p : ℚ))) *
        (∏ p ∈ B, (1 + 1 / (p : ℚ))) := (Finset.prod_sdiff hB_sub).symm
  have hB_sq := sq_prod_one_add_inv_primes_le k (by omega) B rfl
      (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  have hsdiff_gt_two : 2 < ∏ p ∈ Nat.primesLE (q - 1) \ B, (1 + 1 / (p : ℚ)) := by
    set X := ∏ p ∈ Nat.primesLE (q - 1) \ B, (1 + 1 / (p : ℚ))
    set Y := ∏ p ∈ B, (1 + 1 / (p : ℚ))
    have hX_pos : 0 < X := Finset.prod_pos fun p hp => by
      have : (0 : ℚ) < p :=
        Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1).pos
      positivity
    have hY_pos : 0 < Y := Finset.prod_pos fun p hp => by
      have : (0 : ℚ) < p := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
      positivity
    have hk_rat : (11 : ℚ) ≤ k := by exact_mod_cast hk11
    have hLHS_pos : (0 : ℚ) < (36 : ℚ) / 61 * (2 * (k : ℚ) - 4) := by linarith
    have hXY_sq : ((36 : ℚ) / 61 * (2 * (k : ℚ) - 4)) ^ 2 < X ^ 2 * Y ^ 2 := by
      rw [← mul_pow, ← hsplit]
      nlinarith
    have hpoly : 4 * ((9 : ℚ) / 4 * (k : ℚ)) < ((36 : ℚ) / 61 * (2 * (k : ℚ) - 4)) ^ 2 := by
      obtain ⟨d, hd⟩ : ∃ d, k = 11 + d := ⟨k - 11, by omega⟩
      have hd_rat : (k : ℚ) = 11 + (d : ℚ) := by exact_mod_cast hd
      rw [hd_rat]
      have hd0 : (0 : ℚ) ≤ d := Nat.cast_nonneg d
      nlinarith
    have hX2_gt4 : 4 < X ^ 2 := by nlinarith
    by_contra hle2
    push Not at hle2
    nlinarith
  have hrat_gt := lt_trans hsdiff_gt_two (ustar_core_rat_gt_sdiff hm2 hmq)
  have hden_pos : (0 : ℚ) < (m * primorial (q - 1) : ℚ) := by
    have : 0 < m * primorial (q - 1) := mul_pos (by omega) (primorial_pos _)
    exact_mod_cast this
  have hmul_lt : 2 * (m * primorial (q - 1) : ℚ) < (a034448 (m * primorial (q - 1)) : ℚ) :=
    (lt_div_iff₀ hden_pos).mp hrat_gt
  exact_mod_cast hmul_lt

/-! ### Step 6 — Regime II (`q ≥ 17`, `k = m.primeFactors.card ≤ 10`: Prime-Tail + Residual Bounds) -/

/-- General subset-deletion inequality: if `A, T` are disjoint finite sets of positive naturals
with `A` nonempty, `∀ a ∈ A, ∀ t ∈ T, a ≤ t`, `A ∪ T ⊆ P`, and `B.card ≤ A.card`, then
`∏_{t ∈ T} (1 + 1/t) ≤ ∏_{p ∈ P \ B} (1 + 1/p)`. -/
private lemma subset_deletion_prod_ge_tail {A T P B : Finset ℕ}
    (hA : A.Nonempty) (hdisj : Disjoint A T)
    (hA_pos : ∀ a ∈ A, 0 < a) (hAT : ∀ a ∈ A, ∀ t ∈ T, a ≤ t)
    (hsub : A ∪ T ⊆ P) (hP_pos : ∀ p ∈ P, 0 < p) (hcard : B.card ≤ A.card) :
    ∏ t ∈ T, (1 + 1 / (t : ℚ)) ≤ ∏ p ∈ P \ B, (1 + 1 / (p : ℚ)) := by
  let f : ℕ → ℚ := fun p => 1 + 1 / (p : ℚ)
  set S := A ∪ T
  set C := S ∩ B
  have hC_sub : C ⊆ S := Finset.inter_subset_left
  have hC_card : C.card ≤ A.card := le_trans (Finset.card_le_card Finset.inter_subset_right) hcard
  set amax := A.max' hA
  have hamax_mem : amax ∈ A := Finset.max'_mem A hA
  have hamax_pos : 0 < amax := hA_pos amax hamax_mem
  have hfamax_ge1 : (1 : ℚ) ≤ f amax := by
    dsimp [f]
    have : (0 : ℚ) < amax := Nat.cast_pos.mpr hamax_pos
    have : (0 : ℚ) ≤ 1 / (amax : ℚ) := by positivity
    linarith
  have hCA_le : ∏ x ∈ C \ A, f x ≤ ∏ y ∈ A \ C, f y := by
    have hcard_diff : (C \ A).card ≤ (A \ C).card := by
      have h1 := Finset.card_sdiff_add_card_inter C A
      have h2 := Finset.card_sdiff_add_card_inter A C
      rw [Finset.inter_comm] at h2
      omega
    have hupper : ∀ x ∈ C \ A, f x ≤ f amax := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      have hxS : x ∈ A ∪ T := hC_sub hx.1
      have hxT : x ∈ T := by
        rcases Finset.mem_union.mp hxS with h | h
        · exact absurd h hx.2
        · exact h
      have hle : amax ≤ x := hAT amax hamax_mem x hxT
      dsimp [f]
      have : (0 : ℚ) < amax := Nat.cast_pos.mpr hamax_pos
      have : (amax : ℚ) ≤ x := by exact_mod_cast hle
      linarith [one_div_le_one_div_of_le ‹0 < (amax : ℚ)› ‹(amax : ℚ) ≤ x›]
    have hlower : ∀ y ∈ A \ C, f amax ≤ f y := by
      intro y hy
      rw [Finset.mem_sdiff] at hy
      have hy_pos : 0 < y := hA_pos y hy.1
      have hle : y ≤ amax := Finset.le_max' A y hy.1
      dsimp [f]
      have : (0 : ℚ) < y := Nat.cast_pos.mpr hy_pos
      have : (y : ℚ) ≤ amax := by exact_mod_cast hle
      linarith [one_div_le_one_div_of_le ‹0 < (y : ℚ)› ‹(y : ℚ) ≤ amax›]
    calc
      ∏ x ∈ C \ A, f x ≤ (f amax) ^ (C \ A).card :=
        rat_prod_le_pow_card _ _ _ (fun x _ => by dsimp [f]; positivity)
          (le_trans zero_le_one hfamax_ge1) hupper
      _ ≤ (f amax) ^ (A \ C).card := pow_le_pow_right₀ hfamax_ge1 hcard_diff
      _ ≤ ∏ y ∈ A \ C, f y := rat_pow_card_le_prod _ _ _ (le_trans zero_le_one hfamax_ge1) hlower
  have hC_le_A : ∏ x ∈ C, f x ≤ ∏ y ∈ A, f y := by
    have h1 := (Finset.prod_sdiff (Finset.inter_subset_left : C ∩ A ⊆ C) (f := f)).symm
    have h2 := (Finset.prod_sdiff (Finset.inter_subset_right : C ∩ A ⊆ A) (f := f)).symm
    have hs1 : C \ (C ∩ A) = C \ A := by ext z; simp
    have hs2 : A \ (C ∩ A) = A \ C := by ext z; simp
    rw [hs1] at h1
    rw [hs2] at h2
    rw [h1, h2]
    have hinter_nonneg : 0 ≤ ∏ z ∈ C ∩ A, f z :=
      Finset.prod_nonneg fun z _ => by dsimp [f]; positivity
    exact mul_le_mul_of_nonneg_right hCA_le hinter_nonneg
  have hT_le_SC : ∏ t ∈ T, f t ≤ ∏ p ∈ S \ C, f p := by
    have hA_prod_pos : 0 < ∏ y ∈ A, f y :=
      Finset.prod_pos fun y hy => by
        dsimp [f]; have : (0 : ℚ) < y := Nat.cast_pos.mpr (hA_pos y hy); positivity
    have hSC_nonneg : 0 ≤ ∏ p ∈ S \ C, f p :=
      Finset.prod_nonneg fun p _ => by dsimp [f]; positivity
    have hprod_eq : (∏ y ∈ A, f y) * (∏ t ∈ T, f t) =
        (∏ p ∈ S \ C, f p) * (∏ x ∈ C, f x) := by
      rw [← Finset.prod_union hdisj, Finset.prod_sdiff hC_sub]
    nlinarith
  have hSC_sub : S \ C ⊆ P \ B := by
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hsub hx.1, fun hxB => hx.2 (Finset.mem_inter.mpr ⟨hx.1, hxB⟩)⟩
  exact le_trans hT_le_SC
    (rat_prod_le_prod_of_subset_of_one_le hSC_sub fun p hp => by
      rw [Finset.mem_sdiff] at hp
      dsimp [f]
      have : (0 : ℚ) < p := Nat.cast_pos.mpr (hP_pos p hp.1)
      have : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
      linarith)

/-- First `21` primes (`≤ 73`), covering all `1 ≤ m ≤ 78` (`17 ≤ q ≤ 79` and all `17` residual
`m`-cases at `k = 2, 3`). -/
private def primes21 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

private def checkSmallM (m : ℕ) : Bool :=
  let ps := primes21.filter (· ≤ max 13 m)
  decide (2 * (ps.map (fun p => p * ordPow p m)).prod <
    (ps.map (fun p => 1 + p * ordPow p m)).prod)

private lemma small_m_ustar_gt_two {q m : ℕ} (hq : 17 ≤ q) (hm1 : 1 ≤ m) (hm78 : m ≤ 78)
    (hmq : m < q) :
    2 * (m * primorial (q - 1)) < a034448 (m * primorial (q - 1)) := by
  have hall : ((List.range 78).map (· + 1)).all checkSmallM = true := by decide
  have hm_mem : m ∈ (List.range 78).map (· + 1) := by
    rw [List.mem_map]
    exact ⟨m - 1, List.mem_range.mpr (by omega), by omega⟩
  have hchk : checkSmallM m = true := List.all_eq_true.mp hall m hm_mem
  unfold checkSmallM at hchk
  set ps := primes21.filter (· ≤ max 13 m)
  have hineq_nat : 2 * (ps.map (fun p => p * ordPow p m)).prod <
      (ps.map (fun p => 1 + p * ordPow p m)).prod := of_decide_eq_true hchk
  have h21_nodup : primes21.Nodup := by decide
  have h21_prime : primes21.all isPrimeB = true := by decide
  have hps_nodup : ps.Nodup := h21_nodup.filter _
  have hps_sub : ps.toFinset ⊆ Nat.primesLE (q - 1) := by
    intro p hp
    rw [List.mem_toFinset] at hp
    have hflt := List.mem_filter.mp hp
    have hp_prime : p.Prime :=
      (isPrimeB_iff_prime p).mp (List.all_eq_true.mp h21_prime p hflt.1)
    have hp_le : p ≤ max 13 m := of_decide_eq_true hflt.2
    rw [Nat.mem_primesLE]
    exact ⟨by omega, hp_prime⟩
  have hm0 : m ≠ 0 := by omega
  have hsub_rat :
      ((ps.map (fun p => 1 + p * ordPow p m)).prod : ℚ) /
        ((ps.map (fun p => p * ordPow p m)).prod : ℚ) ≤
      (a034448 (m * primorial (q - 1)) : ℚ) / (m * primorial (q - 1) : ℚ) := by
    rw [ustar_core_rat_eq hm1 hmq]
    have hps_eq :
        ((ps.map (fun p => 1 + p * ordPow p m)).prod : ℚ) /
          ((ps.map (fun p => p * ordPow p m)).prod : ℚ) =
        ∏ p ∈ ps.toFinset, (1 + 1 / ((p : ℚ) ^ (m.factorization p + 1))) := by
      have hnum : ((ps.map (fun p => 1 + p * ordPow p m)).prod : ℚ) =
          ∏ p ∈ ps.toFinset, (1 + (p : ℚ) ^ (m.factorization p + 1)) := by
        have hnat : (ps.map (fun p => 1 + p * ordPow p m)).prod =
            ∏ p ∈ ps.toFinset, (1 + p ^ (m.factorization p + 1)) := by
          rw [← List.prod_toFinset _ hps_nodup]
          refine Finset.prod_congr rfl fun p hp => ?_
          have hp_prime : p.Prime := Nat.prime_of_mem_primesLE (hps_sub hp)
          rw [ordPow_eq_pow_factorization hp_prime hm0, pow_succ']
        rw [hnat]
        push_cast
        rfl
      have hden : ((ps.map (fun p => p * ordPow p m)).prod : ℚ) =
          ∏ p ∈ ps.toFinset, (p : ℚ) ^ (m.factorization p + 1) := by
        have hnat : (ps.map (fun p => p * ordPow p m)).prod =
            ∏ p ∈ ps.toFinset, p ^ (m.factorization p + 1) := by
          rw [← List.prod_toFinset _ hps_nodup]
          refine Finset.prod_congr rfl fun p hp => ?_
          have hp_prime : p.Prime := Nat.prime_of_mem_primesLE (hps_sub hp)
          rw [ordPow_eq_pow_factorization hp_prime hm0, pow_succ']
        rw [hnat]
        push_cast
        rfl
      rw [hnum, hden, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_pos : (0 : ℚ) < p := Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE (hps_sub hp)).pos
      have hpow_ne : ((p : ℚ) ^ (m.factorization p + 1)) ≠ 0 := pow_ne_zero _ hp_pos.ne'
      field_simp [hpow_ne]
      ring
    rw [hps_eq]
    exact rat_prod_le_prod_of_subset_of_one_le hps_sub fun p hp => by
      have hp_pos : (0 : ℚ) < p := Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE hp).pos
      have : (0 : ℚ) ≤ 1 / ((p : ℚ) ^ (m.factorization p + 1)) := by positivity
      linarith
  have hps_den_pos_nat : 0 < (ps.map (fun p => p * ordPow p m)).prod := by
    refine list_prod_pos fun x hx => ?_
    rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hp_prime : p.Prime :=
      Nat.prime_of_mem_primesLE (hps_sub (List.mem_toFinset.mpr hp))
    rw [ordPow_eq_pow_factorization hp_prime hm0]
    exact mul_pos hp_prime.pos (pow_pos hp_prime.pos _)
  have hps_den_pos : (0 : ℚ) < ((ps.map (fun p => p * ordPow p m)).prod : ℚ) := by
    exact_mod_cast hps_den_pos_nat
  have hgt2 : (2 : ℚ) <
      ((ps.map (fun p => 1 + p * ordPow p m)).prod : ℚ) /
        ((ps.map (fun p => p * ordPow p m)).prod : ℚ) := by
    rw [lt_div_iff₀ hps_den_pos]
    exact_mod_cast hineq_nat
  have hcore_pos : (0 : ℚ) < (m * primorial (q - 1) : ℚ) := by
    have : 0 < m * primorial (q - 1) := mul_pos (by omega) (primorial_pos _)
    exact_mod_cast this
  have hfinal_rat : 2 * (m * primorial (q - 1) : ℚ) < (a034448 (m * primorial (q - 1)) : ℚ) :=
    (lt_div_iff₀ hcore_pos).mp (lt_of_lt_of_le hgt2 hsub_rat)
  exact_mod_cast hfinal_rat

/-- First `204` primes (`2` through `1249`), providing certified prime-tail witnesses for `k ≤ 10`. -/
private def primes204 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
   179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
   283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
   419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
   547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
   661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809,
   811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
   947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
   1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223,
   1229, 1231, 1237, 1249]

private lemma primes204_pairwise_lt : primes204.Pairwise (· < ·) :=
  pairwise_lt_of_isSortedLt primes204 (by decide)

set_option maxRecDepth 4096 in
private lemma primes204_all_prime : ∀ p ∈ primes204, p.Prime := by
  have hall : primes204.all isPrimeB = true := by decide
  intro p hp
  exact (isPrimeB_iff_prime p).mp (List.all_eq_true.mp hall p hp)

private def tailIdx (k : ℕ) : ℕ :=
  match k with
  | 0 => 6 | 1 => 6 | 2 => 11 | 3 => 21 | 4 => 35 | 5 => 51
  | 6 => 73 | 7 => 98 | 8 => 130 | 9 => 167 | _ => 204

private def tailMaxPrime (k : ℕ) : ℕ :=
  match k with
  | 0 => 13 | 1 => 13 | 2 => 31 | 3 => 73 | 4 => 149 | 5 => 233
  | 6 => 367 | 7 => 521 | 8 => 733 | 9 => 991 | _ => 1249

private def checkTail (k : ℕ) : Bool :=
  let sub := primes204.take (tailIdx k)
  let A := sub.take k
  let T := sub.drop k
  decide (A.length == k && sub.all (· ≤ tailMaxPrime k) &&
    2 * T.prod < (T.map (fun t => t + 1)).prod)

set_option maxRecDepth 4096 in
private lemma checkTail_all_1_to_10 :
    ((List.range 10).map (· + 1)).all checkTail = true := by decide

private lemma list_prod_one_add_inv_gt_two {T : List ℕ} (hnodup : T.Nodup)
    (hpos : ∀ t ∈ T, 0 < t) (hprod : 2 * T.prod < (T.map (fun t => t + 1)).prod) :
    (2 : ℚ) < ∏ t ∈ T.toFinset, (1 + 1 / (t : ℚ)) := by
  have hnum_nat : (T.map (fun t => t + 1)).prod = ∏ t ∈ T.toFinset, (t + 1) :=
    (List.prod_toFinset (fun t => t + 1) hnodup).symm
  have hden_nat : T.prod = ∏ t ∈ T.toFinset, t := by
    simpa using (List.prod_toFinset (fun t => t) hnodup).symm
  have hnum : (((T.map (fun t => t + 1)).prod : ℕ) : ℚ) = ∏ t ∈ T.toFinset, ((t : ℚ) + 1) := by
    rw [hnum_nat]
    push_cast
    rfl
  have hden : ((T.prod : ℕ) : ℚ) = ∏ t ∈ T.toFinset, (t : ℚ) := by
    rw [hden_nat]
    push_cast
    rfl
  have hden_pos_nat : 0 < T.prod := list_prod_pos hpos
  have hden_pos : (0 : ℚ) < (T.prod : ℚ) := by exact_mod_cast hden_pos_nat
  have hdiv : (((T.map (fun t => t + 1)).prod : ℕ) : ℚ) / (T.prod : ℚ) =
      ∏ t ∈ T.toFinset, (1 + 1 / (t : ℚ)) := by
    rw [hnum, hden, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht_pos : (0 : ℚ) < t := Nat.cast_pos.mpr (hpos t (List.mem_toFinset.mp ht))
    field_simp [ht_pos.ne']
  rw [← hdiv, lt_div_iff₀ hden_pos]
  exact_mod_cast hprod

private lemma regime_two_large_m_ustar_gt_two {q m : ℕ} (hm79 : 79 ≤ m) (hmq : m < q)
    (hk10 : m.primeFactors.card ≤ 10) :
    2 * (m * primorial (q - 1)) < a034448 (m * primorial (q - 1)) := by
  set B := m.primeFactors
  set k := B.card
  have hm2 : 2 ≤ m := by omega
  have hB_ne : B.Nonempty := Nat.nonempty_primeFactors.mpr hm2
  have hk1 : 1 ≤ k := Finset.card_pos.mpr hB_ne
  have hk_mem : k ∈ (List.range 10).map (· + 1) := by
    rw [List.mem_map]
    exact ⟨k - 1, List.mem_range.mpr (by omega), by omega⟩
  have hchk : checkTail k = true := List.all_eq_true.mp checkTail_all_1_to_10 k hk_mem
  unfold checkTail at hchk
  set sub := primes204.take (tailIdx k)
  set A_list := sub.take k
  set T_list := sub.drop k
  have hdec := of_decide_eq_true hchk
  simp only [Bool.and_eq_true, beq_iff_eq] at hdec
  rcases hdec with ⟨⟨hlenA, hall_le⟩, hprod_T_dec⟩
  have hprod_T : 2 * T_list.prod < (T_list.map (fun t => t + 1)).prod :=
    of_decide_eq_true hprod_T_dec
  have hsub_pw : sub.Pairwise (· < ·) := primes204_pairwise_lt.take
  have hsplit_sub : A_list ++ T_list = sub := List.take_append_drop k sub
  rw [← hsplit_sub, List.pairwise_append] at hsub_pw
  rcases hsub_pw with ⟨hA_pw, hT_pw, hAT_lt⟩
  have hA_nodup : A_list.Nodup := hA_pw.imp ne_of_lt
  have hT_nodup : T_list.Nodup := hT_pw.imp ne_of_lt
  set A := A_list.toFinset
  set T := T_list.toFinset
  have hA_card : A.card = k := by rw [List.toFinset_card_of_nodup hA_nodup, hlenA]
  have hA_ne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hdisj : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro x hxA hxT
    rw [List.mem_toFinset] at hxA hxT
    exact lt_irrefl x (hAT_lt x hxA x hxT)
  have hAT : ∀ a ∈ A, ∀ t ∈ T, a ≤ t := by
    intro a ha t ht
    rw [List.mem_toFinset] at ha ht
    exact le_of_lt (hAT_lt a ha t ht)
  have hmax_le_q1 : tailMaxPrime k ≤ q - 1 := by
    have hodd : oddProd (k - 1) ≤ m := by
      have h1 := prod_primes_ge_oddProd k hk1 B rfl fun _ hp => Nat.prime_of_mem_primeFactors hp
      have h2 : ∏ p ∈ B, p ≤ m := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd m)
      exact le_trans h1 h2
    interval_cases k
    · change 13 ≤ q - 1; omega
    · change 31 ≤ q - 1; omega
    · change 73 ≤ q - 1; omega
    · have hv : oddProd (4 - 1) = 210 := by decide
      change 149 ≤ q - 1; omega
    · have hv : oddProd (5 - 1) = 1890 := by decide
      change 233 ≤ q - 1; omega
    · have hv : oddProd (6 - 1) = 20790 := by decide
      change 367 ≤ q - 1; omega
    · have hv : oddProd (7 - 1) = 270270 := by decide
      change 521 ≤ q - 1; omega
    · have hv : oddProd (8 - 1) = 4054050 := by decide
      change 733 ≤ q - 1; omega
    · have hv : oddProd (9 - 1) = 68918850 := by decide
      change 991 ≤ q - 1; omega
    · have hv : oddProd (10 - 1) = 1309458150 := by decide
      change 1249 ≤ q - 1; omega
  have hAT_sub_P : A ∪ T ⊆ Nat.primesLE (q - 1) := by
    intro p hp
    have hp_sub : p ∈ sub := by
      rcases Finset.mem_union.mp hp with hpA | hpT
      · rw [List.mem_toFinset] at hpA
        exact List.mem_of_mem_take hpA
      · rw [List.mem_toFinset] at hpT
        exact List.mem_of_mem_drop hpT
    have hp_prime : p.Prime := primes204_all_prime p (List.mem_of_mem_take hp_sub)
    have hp_le : p ≤ tailMaxPrime k := of_decide_eq_true (List.all_eq_true.mp hall_le p hp_sub)
    rw [Nat.mem_primesLE]
    exact ⟨le_trans hp_le hmax_le_q1, hp_prime⟩
  have hA_pos : ∀ a ∈ A, 0 < a := fun a ha =>
    (Nat.prime_of_mem_primesLE (hAT_sub_P (Finset.mem_union_left T ha))).pos
  have hT_pos : ∀ t ∈ T_list, 0 < t := fun t ht =>
    (Nat.prime_of_mem_primesLE (hAT_sub_P (Finset.mem_union_right A (List.mem_toFinset.mpr ht)))).pos
  have hP_pos : ∀ p ∈ Nat.primesLE (q - 1), 0 < p := fun _ hp => (Nat.prime_of_mem_primesLE hp).pos
  have htail_gt2 : (2 : ℚ) < ∏ t ∈ T, (1 + 1 / (t : ℚ)) :=
    list_prod_one_add_inv_gt_two hT_nodup hT_pos hprod_T
  have hsdiff_ge : ∏ t ∈ T, (1 + 1 / (t : ℚ)) ≤
      ∏ p ∈ Nat.primesLE (q - 1) \ B, (1 + 1 / (p : ℚ)) :=
    subset_deletion_prod_ge_tail hA_ne hdisj hA_pos hAT hAT_sub_P hP_pos (by omega)
  have hrat_gt : (2 : ℚ) <
      (a034448 (m * primorial (q - 1)) : ℚ) / (m * primorial (q - 1) : ℚ) :=
    lt_of_lt_of_le (lt_of_lt_of_le htail_gt2 hsdiff_ge) (le_of_lt (ustar_core_rat_gt_sdiff hm2 hmq))
  have hden_pos : (0 : ℚ) < (m * primorial (q - 1) : ℚ) := by
    have : 0 < m * primorial (q - 1) := mul_pos (by omega) (primorial_pos _)
    exact_mod_cast this
  have hmul_lt : 2 * (m * primorial (q - 1) : ℚ) < (a034448 (m * primorial (q - 1)) : ℚ) :=
    (lt_div_iff₀ hden_pos).mp hrat_gt
  exact_mod_cast hmul_lt

/-- Hardest lemma (`SCOPING-S010.md` §5.2): for every `q ≥ 17` and `1 ≤ m < q`,
`2 * (m * primorial (q - 1)) < a034448 (m * primorial (q - 1))`. -/
theorem ustar_core_gt_two_of_ge_seventeen {q m : ℕ} (hq : 17 ≤ q) (hm1 : 1 ≤ m) (hmq : m < q) :
    2 * (m * primorial (q - 1)) < a034448 (m * primorial (q - 1)) := by
  by_cases hm78 : m ≤ 78
  · exact small_m_ustar_gt_two hq hm1 hm78 hmq
  · by_cases hk10 : m.primeFactors.card ≤ 10
    · exact regime_two_large_m_ustar_gt_two (by omega) hmq hk10
    · exact regime_three_ustar_gt_two hq hm1 hmq (by omega)

/-! ### Step 2 & Main Pinned Theorems (`a401714_imp_a401715` and `a401714_le_a401715`) -/

/-- Equivalent implication form (`PIN-S010.md` v1): for all `n : ℕ`,
`1 ≤ n → a003557 n < a053669 n → 2 * n ≤ a034448 n + a048250 n`. -/
theorem a401714_imp_a401715 :
    ∀ n : ℕ, 1 ≤ n → a003557 n < a053669 n → 2 * n ≤ a034448 n + a048250 n := by
  intro n hn hmq
  refine primorial_core_reduction hn hmq ?_
  have ⟨hq_prime, _, _⟩ := a053669_spec hn
  have hm1 : 1 ≤ a003557 n := a003557_pos hn
  by_cases hq13 : a053669 n ≤ 13
  · exact regime_one_core_bound hq_prime hq13 hm1 hmq
  · have hq17 : 17 ≤ a053669 n := by
      by_contra hlt17
      have h14_16 : a053669 n = 14 ∨ a053669 n = 15 ∨ a053669 n = 16 := by omega
      rcases h14_16 with heq | heq | heq <;> rw [heq] at hq_prime <;>
        exact absurd hq_prime (by norm_num)
    have hgt := ustar_core_gt_two_of_ge_seventeen hq17 hm1 hmq
    omega

/-- Canonical form (`PIN-S010.md` v1): for all `n : ℕ`, `1 ≤ n → a401714 n ≤ a401715 n`. -/
theorem a401714_le_a401715 :
    ∀ n : ℕ, 1 ≤ n → a401714 n ≤ a401715 n := by
  intro n hn
  unfold a401714 a401715
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (a401714_imp_a401715 n hn h1) h2
  · exact Nat.zero_le _
  · exact le_rfl

/-! ### Computable Mirror & Non-Vacuity / OEIS `1..105` & Boundary Spot Checks -/

private def primeFactorsCompute (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun p => isPrimeB p && (n % p == 0))

private lemma primeFactorsCompute_nodup (n : ℕ) : (primeFactorsCompute n).Nodup :=
  List.nodup_range.filter _

private lemma primeFactorsCompute_toFinset {n : ℕ} (hn : n ≠ 0) :
    (primeFactorsCompute n).toFinset = n.primeFactors := by
  ext p
  simp only [primeFactorsCompute, List.mem_toFinset, List.mem_filter, List.mem_range,
    Bool.and_eq_true, isPrimeB_iff_prime, beq_iff_eq, Nat.mem_primeFactors, ne_eq]
  constructor
  · rintro ⟨_, hp, hmod⟩
    exact ⟨hp, Nat.dvd_of_mod_eq_zero hmod, hn⟩
  · rintro ⟨hp, hdvd, _⟩
    have hle : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    exact ⟨by omega, hp, Nat.mod_eq_zero_of_dvd hdvd⟩

def radCompute (n : ℕ) : ℕ :=
  (primeFactorsCompute n).prod

def a003557Compute (n : ℕ) : ℕ :=
  n / radCompute n

def a034448Compute (n : ℕ) : ℕ :=
  ((primeFactorsCompute n).map (fun p => 1 + ordPow p n)).prod

def a048250Compute (n : ℕ) : ℕ :=
  ((primeFactorsCompute n).map (fun p => 1 + p)).prod

def a401715Compute (n : ℕ) : ℕ :=
  if 2 * n ≤ a034448Compute n + a048250Compute n then 1 else 0

theorem rad_eq_compute {n : ℕ} (hn : 1 ≤ n) : rad n = radCompute n := by
  have hn0 : n ≠ 0 := by omega
  unfold rad radCompute
  rw [← primeFactorsCompute_toFinset hn0]
  simpa using (List.prod_toFinset (fun p => p) (primeFactorsCompute_nodup n))

theorem a003557_eq_compute {n : ℕ} (hn : 1 ≤ n) : a003557 n = a003557Compute n := by
  unfold a003557 a003557Compute
  rw [rad_eq_compute hn]

theorem a034448_eq_compute {n : ℕ} (hn : 1 ≤ n) : a034448 n = a034448Compute n := by
  have hn0 : n ≠ 0 := by omega
  unfold a034448Compute
  rw [a034448_eq_prod hn0, ← primeFactorsCompute_toFinset hn0,
    List.prod_toFinset _ (primeFactorsCompute_nodup n)]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hp_mem : p ∈ n.primeFactors :=
    primeFactorsCompute_toFinset hn0 ▸ List.mem_toFinset.mpr hp
  rw [ordPow_eq_pow_factorization (Nat.prime_of_mem_primeFactors hp_mem) hn0]

theorem a048250_eq_compute {n : ℕ} (hn : 1 ≤ n) : a048250 n = a048250Compute n := by
  have hn0 : n ≠ 0 := by omega
  unfold a048250Compute
  rw [a048250_eq_prod hn0, ← primeFactorsCompute_toFinset hn0,
    List.prod_toFinset _ (primeFactorsCompute_nodup n)]

theorem a401715_eq_compute {n : ℕ} (hn : 1 ≤ n) : a401715 n = a401715Compute n := by
  unfold a401715 a401715Compute
  rw [a034448_eq_compute hn, a048250_eq_compute hn]

/-- Bounded least-non-dividing-prime finder on `{0, ..., 19}` (sufficient whenever `a053669 n < 20`,
which holds for all `n < 9,699,690`, in particular `1..105` and `349,440`). -/
def a053669SmallCompute (n : ℕ) : ℕ :=
  match (List.range 20).find? (fun p => isPrimeB p && (n % p != 0)) with
  | some q => q
  | none => 0

private lemma a053669_eq_of_witness {n q : ℕ} (hn : 1 ≤ n) (hq_prime : isPrimeB q = true)
    (hq_ndvd : n % q != 0)
    (hsmall : ∀ p ∈ List.range q, (isPrimeB p = true → n % p = 0)) :
    a053669 n = q := by
  have ⟨ha_prime, ha_ndvd, _⟩ := a053669_spec hn
  have hqp : q.Prime := (isPrimeB_iff_prime q).mp hq_prime
  have hq_not_dvd : ¬ q ∣ n := by
    simp only [bne_iff_ne, ne_eq] at hq_ndvd
    exact fun hdvd => hq_ndvd (Nat.mod_eq_zero_of_dvd hdvd)
  have hle : a053669 n ≤ q := Nat.sInf_le ⟨hqp, hq_not_dvd⟩
  have hge : q ≤ a053669 n := by
    by_contra hlt
    have hmem : a053669 n ∈ List.range q := List.mem_range.mpr (by omega)
    have hmod := hsmall (a053669 n) hmem ((isPrimeB_iff_prime _).mpr ha_prime)
    exact ha_ndvd (Nat.dvd_of_mod_eq_zero hmod)
  omega

theorem a053669_eq_smallCompute {n : ℕ} (hn : 1 ≤ n)
    (hok : ((List.range 20).find? (fun p => isPrimeB p && (n % p != 0))).isSome = true) :
    a053669 n = a053669SmallCompute n := by
  unfold a053669SmallCompute
  cases hfind : (List.range 20).find? (fun p => isPrimeB p && (n % p != 0)) with
  | none => simp [hfind] at hok
  | some q =>
    dsimp only
    have hpred := List.find?_some hfind
    simp only [Bool.and_eq_true] at hpred
    refine a053669_eq_of_witness hn hpred.1 hpred.2 fun p hp hprime => ?_
    rw [List.mem_range] at hp
    have hlt := List.find?_eq_some_iff_append.mp hfind
    rcases hlt with ⟨_, xs, ys, hrange_eq, hnot⟩
    have hp_in_range : p ∈ List.range 20 := by
      have hq_mem : q ∈ List.range 20 := List.mem_of_find?_eq_some hfind
      rw [List.mem_range] at hq_mem ⊢
      omega
    rw [hrange_eq, List.mem_append, List.mem_cons] at hp_in_range
    rcases hp_in_range with hp_xs | hp_q | hp_ys
    · have hfalse := hnot p hp_xs
      simpa [hprime] using hfalse
    · omega
    · exfalso
      have hpw : (List.range 20).Pairwise (· < ·) := List.pairwise_lt_range
      rw [hrange_eq, List.pairwise_append] at hpw
      have hqy : q < p := (List.pairwise_cons.mp hpw.2.1).1 p hp_ys
      omega

def a401714SmallCompute (n : ℕ) : ℕ :=
  if a003557Compute n < a053669SmallCompute n then 1 else 0

theorem a401714_eq_smallCompute {n : ℕ} (hn : 1 ≤ n)
    (hok : ((List.range 20).find? (fun p => isPrimeB p && (n % p != 0))).isSome = true) :
    a401714 n = a401714SmallCompute n := by
  unfold a401714 a401714SmallCompute
  rw [a003557_eq_compute hn, a053669_eq_smallCompute hn hok]

/-- Verbatim `%S/%T/%U` printed terms `n = 1..105` of `OEIS A401714` and `OEIS A401715`. -/
def oeisPrinted105 : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1,
   0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1,
   1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1]

/-- Kernel verification of all `105` printed terms of `OEIS A401714` (`n = 1..105`, `0` mismatches). -/
theorem oeis_a401714_1_to_105 :
    (List.range 105).map (fun i => a401714 (i + 1)) = oeisPrinted105 := by
  have hall_ok : (List.range 105).all (fun i =>
      ((List.range 20).find? (fun p => isPrimeB p && ((i + 1) % p != 0))).isSome) = true := by
    decide
  have hmap : (List.range 105).map (fun i => a401714 (i + 1)) =
      (List.range 105).map (fun i => a401714SmallCompute (i + 1)) :=
    List.map_congr_left fun i hi =>
      a401714_eq_smallCompute (by omega) (List.all_eq_true.mp hall_ok i hi)
  rw [hmap]
  rfl

/-- Kernel verification of all `105` printed terms of `OEIS A401715` (`n = 1..105`, `0` mismatches). -/
theorem oeis_a401715_1_to_105 :
    (List.range 105).map (fun i => a401715 (i + 1)) = oeisPrinted105 := by
  have hmap : (List.range 105).map (fun i => a401715 (i + 1)) =
      (List.range 105).map (fun i => a401715Compute (i + 1)) :=
    List.map_congr_left fun _ _ => a401715_eq_compute (by omega)
  rw [hmap]
  rfl

set_option maxRecDepth 4096 in
/-- Non-vacuity and boundary spot checks (`BRIEF` §1 / §2.3):
- `n = 1` equality (`a034448 1 + a048250 1 = 1 + 1 = 2 = 2 * 1`, `a401714 1 = a401715 1 = 1`);
- `n = 4` equality (`5 + 3 = 8 = 2 * 4`, `a401714 4 = a401715 4 = 1`);
- `n = 24` equality (`36 + 12 = 48 = 2 * 24`, `a401714 24 = a401715 24 = 1`);
- `n = 240` first strict inequality (`a401714 240 = 0 < 1 = a401715 240`, `408 + 72 = 480 = 2 * 240`);
- `n = 270` second strict inequality (`a401714 270 = 0 < 1 = a401715 270`, `504 + 72 = 576 > 540`);
- `n = 8, 9` prime-power vacuous zero cases (`a401714 8 = a401715 8 = 0`, `a401714 9 = a401715 9 = 0`);
- `n = 349440` fifth `A325963` equality (`690816 + 8064 = 698880 = 2 * 349440`, `a401714 349440 = 0`,
  `a401715 349440 = 1`). -/
theorem boundary_and_equality_spot_checks :
    (a034448 1 = 1 ∧ a048250 1 = 1 ∧ a401714 1 = 1 ∧ a401715 1 = 1) ∧
    (a034448 4 = 5 ∧ a048250 4 = 3 ∧ a401714 4 = 1 ∧ a401715 4 = 1) ∧
    (a034448 24 = 36 ∧ a048250 24 = 12 ∧ a401714 24 = 1 ∧ a401715 24 = 1) ∧
    (a034448 240 = 408 ∧ a048250 240 = 72 ∧ a401714 240 = 0 ∧ a401715 240 = 1) ∧
    (a034448 270 = 504 ∧ a048250 270 = 72 ∧ a401714 270 = 0 ∧ a401715 270 = 1) ∧
    (a401714 8 = 0 ∧ a401715 8 = 0 ∧ a401714 9 = 0 ∧ a401715 9 = 0) ∧
    (a034448 349440 = 690816 ∧ a048250 349440 = 8064 ∧
      a401714 349440 = 0 ∧ a401715 349440 = 1) := by
  have hsmall : ∀ n ∈ ([1, 4, 24, 240, 270, 8, 9] : List ℕ),
      a034448 n = a034448Compute n ∧ a048250 n = a048250Compute n ∧
      a401714 n = a401714SmallCompute n ∧ a401715 n = a401715Compute n := by
    intro n hn
    have hn1 : 1 ≤ n := by
      rcases List.mem_cons.mp hn with rfl | hn; · omega
      rcases List.mem_cons.mp hn with rfl | hn; · omega
      rcases List.mem_cons.mp hn with rfl | hn; · omega
      rcases List.mem_cons.mp hn with rfl | hn; · omega
      rcases List.mem_cons.mp hn with rfl | hn; · omega
      rcases List.mem_cons.mp hn with rfl | hn; · omega
      rcases List.mem_cons.mp hn with rfl | hn; · omega
      nomatch hn
    have hok_all : ([1, 4, 24, 240, 270, 8, 9] : List ℕ).all (fun m =>
        ((List.range 20).find? (fun p => isPrimeB p && (m % p != 0))).isSome) = true := by decide
    exact ⟨a034448_eq_compute hn1, a048250_eq_compute hn1,
      a401714_eq_smallCompute hn1 (List.all_eq_true.mp hok_all n hn),
      a401715_eq_compute hn1⟩
  have h1 := hsmall 1 (by simp)
  have h4 := hsmall 4 (by simp)
  have h24 := hsmall 24 (by simp)
  have h240 := hsmall 240 (by simp)
  have h270 := hsmall 270 (by simp)
  have h8 := hsmall 8 (by simp)
  have h9 := hsmall 9 (by simp)
  -- Factor 349440 = 256 * 105 * 13 into coprime factors ≤ 256 for shallow recursion:
  have h349440_eq : (349440 : ℕ) = 256 * (105 * 13) := by norm_num
  have hcop1 : Nat.Coprime 256 (105 * 13) := by decide
  have hcop2 : Nat.Coprime 105 13 := by decide
  have hu349440 : a034448 349440 = 690816 := by
    rw [h349440_eq, a034448_mul_of_coprime (by omega) (by omega) hcop1,
      a034448_mul_of_coprime (by omega) (by omega) hcop2,
      a034448_eq_compute (by omega : 1 ≤ 256), a034448_eq_compute (by omega : 1 ≤ 105),
      a034448_eq_compute (by omega : 1 ≤ 13)]
    rfl
  have hs349440 : a048250 349440 = 8064 := by
    rw [h349440_eq, a048250_mul_of_coprime (by omega) (by omega) hcop1,
      a048250_mul_of_coprime (by omega) (by omega) hcop2,
      a048250_eq_compute (by omega : 1 ≤ 256), a048250_eq_compute (by omega : 1 ≤ 105),
      a048250_eq_compute (by omega : 1 ≤ 13)]
    rfl
  have hrad349440 : rad 349440 = 2730 := by
    unfold rad
    rw [h349440_eq, hcop1.primeFactors_mul, Finset.prod_union hcop1.disjoint_primeFactors,
      hcop2.primeFactors_mul, Finset.prod_union hcop2.disjoint_primeFactors]
    change rad 256 * (rad 105 * rad 13) = 2730
    rw [rad_eq_compute (by omega : 1 ≤ 256), rad_eq_compute (by omega : 1 ≤ 105),
      rad_eq_compute (by omega : 1 ≤ 13)]
    rfl
  have hm349440 : a003557 349440 = 128 := by
    unfold a003557
    rw [hrad349440]
  have hq349440 : a053669 349440 = 11 := by
    rw [a053669_eq_smallCompute (by omega) (by decide)]
    rfl
  have ha714_349440 : a401714 349440 = 0 := by
    unfold a401714
    rw [hm349440, hq349440]
    norm_num
  have ha715_349440 : a401715 349440 = 1 := by
    unfold a401715
    rw [hu349440, hs349440]
    norm_num
  rw [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2,
      h4.1, h4.2.1, h4.2.2.1, h4.2.2.2,
      h24.1, h24.2.1, h24.2.2.1, h24.2.2.2,
      h240.1, h240.2.1, h240.2.2.1, h240.2.2.2,
      h270.1, h270.2.1, h270.2.2.1, h270.2.2.2,
      h8.2.2.1, h8.2.2.2, h9.2.2.1, h9.2.2.2,
      hu349440, hs349440, ha714_349440, ha715_349440]
  decide

/-- Kernel refutation of the intake's `q ≥ 11` unitary-only threshold sketch (`SCOPING-S010.md`
§2.1 / §2.2 Step 4): at `n = 1260` (`q = 11, m = 6`) and `n = 27720` (`q = 13, m = 12`),
`a003557 n < a053669 n` holds, yet `a034448 n < 2 * n` (`2400 < 2520` and `51840 < 55440`);
the combined sum `a034448 n + a048250 n` still clears `2 * n` (`2976 > 2520` and `58752 > 55440`). -/
theorem refute_intake_q11_ustar_claim :
    (a003557 1260 = 6 ∧ a053669 1260 = 11 ∧ a034448 1260 = 2400 ∧
      a034448 1260 < 2 * 1260 ∧ 2 * 1260 < a034448 1260 + a048250 1260) ∧
    (a003557 27720 = 12 ∧ a053669 27720 = 13 ∧ a034448 27720 = 51840 ∧
      a034448 27720 < 2 * 27720 ∧ 2 * 27720 < a034448 27720 + a048250 27720) := by
  have h1260 : (1260 : ℕ) = 36 * 35 := by norm_num
  have hc1260 : Nat.Coprime 36 35 := by decide
  have hu1260 : a034448 1260 = 2400 := by
    rw [h1260, a034448_mul_of_coprime (by omega) (by omega) hc1260,
      a034448_eq_compute (by omega : 1 ≤ 36), a034448_eq_compute (by omega : 1 ≤ 35)]
    rfl
  have hs1260 : a048250 1260 = 576 := by
    rw [h1260, a048250_mul_of_coprime (by omega) (by omega) hc1260,
      a048250_eq_compute (by omega : 1 ≤ 36), a048250_eq_compute (by omega : 1 ≤ 35)]
    rfl
  have hrad1260 : rad 1260 = 210 := by
    unfold rad
    rw [h1260, hc1260.primeFactors_mul, Finset.prod_union hc1260.disjoint_primeFactors]
    change rad 36 * rad 35 = 210
    rw [rad_eq_compute (by omega : 1 ≤ 36), rad_eq_compute (by omega : 1 ≤ 35)]
    rfl
  have hm1260 : a003557 1260 = 6 := by unfold a003557; rw [hrad1260]
  have hq1260 : a053669 1260 = 11 := by rw [a053669_eq_smallCompute (by omega) (by decide)]; rfl
  have h27720 : (27720 : ℕ) = 72 * (35 * 11) := by norm_num
  have hc27720a : Nat.Coprime 72 (35 * 11) := by decide
  have hc27720b : Nat.Coprime 35 11 := by decide
  have hu27720 : a034448 27720 = 51840 := by
    rw [h27720, a034448_mul_of_coprime (by omega) (by omega) hc27720a,
      a034448_mul_of_coprime (by omega) (by omega) hc27720b,
      a034448_eq_compute (by omega : 1 ≤ 72), a034448_eq_compute (by omega : 1 ≤ 35),
      a034448_eq_compute (by omega : 1 ≤ 11)]
    rfl
  have hs27720 : a048250 27720 = 6912 := by
    rw [h27720, a048250_mul_of_coprime (by omega) (by omega) hc27720a,
      a048250_mul_of_coprime (by omega) (by omega) hc27720b,
      a048250_eq_compute (by omega : 1 ≤ 72), a048250_eq_compute (by omega : 1 ≤ 35),
      a048250_eq_compute (by omega : 1 ≤ 11)]
    rfl
  have hrad27720 : rad 27720 = 2310 := by
    unfold rad
    rw [h27720, hc27720a.primeFactors_mul, Finset.prod_union hc27720a.disjoint_primeFactors,
      hc27720b.primeFactors_mul, Finset.prod_union hc27720b.disjoint_primeFactors]
    change rad 72 * (rad 35 * rad 11) = 2310
    rw [rad_eq_compute (by omega : 1 ≤ 72), rad_eq_compute (by omega : 1 ≤ 35),
      rad_eq_compute (by omega : 1 ≤ 11)]
    rfl
  have hm27720 : a003557 27720 = 12 := by unfold a003557; rw [hrad27720]
  have hq27720 : a053669 27720 = 13 := by rw [a053669_eq_smallCompute (by omega) (by decide)]; rfl
  rw [hm1260, hq1260, hu1260, hs1260, hm27720, hq27720, hu27720, hs27720]
  decide

end SeamC.A401714
