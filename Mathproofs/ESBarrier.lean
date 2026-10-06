import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Divisibility.Units

/-!
# Round 16 barrier theorem — Erdős–Straus finite-identity barrier

Source: `~/workspace/math-unsolved/ROUND16_DOSSIER.md`
Preprint: `~/workspace/math-unsolved/preprints/erdos-straus-finite-identity-barrier.tex`
(Theorem 1 there).

**Theorem (R16).** Let `S = {(Aᵢ,Bᵢ)}` be progressions arising from a finite family
of polynomial identities `4/(Aᵢt+Bᵢ) = Σⱼ 1/Fᵢⱼ(t)`, `Fᵢⱼ ∈ ℤ[t]` of positive
leading coefficient, valid for all `t`, with `gcd(Aᵢ,Bᵢ) = 1` and `8 ∣ Aᵢ`.
Then `⋃ᵢ (Aᵢℕ + Bᵢ)` does *not* contain all primes `p ≡ r (mod 840)` for any
square class `r ∈ {1,121,169,289,361,529}`. Infinitely many such primes lie
outside every progression.

The classical Schinzel–Mordell lemma is taken as an axiom (see `schinzel_mordell`
below); Dirichlet's theorem on arithmetic progressions is taken as a second
axiom (see `dirichlet_arith_prog` below — Mathlib 4.34.1 only contains the
special case of primes ≡ 1 mod k); the CRT construction is fully proved.

Checked with Lean 4.34.1 (`leanprover/lean4:stable`) + Mathlib, modulo the two
axioms.
-/

/-- Coprimality is preserved when replacing a number by a congruent one. -/
lemma coprime_of_modEq {a b n : ℕ} (h : a ≡ b [MOD n]) (hc : Nat.Coprime b n) :
    Nat.Coprime a n := by
  have e1 : Nat.gcd a n = Nat.gcd (a % n) n := by
    rw [Nat.gcd_comm a n, Nat.gcd_rec]
  have e2 : Nat.gcd b n = Nat.gcd (b % n) n := by
    rw [Nat.gcd_comm b n, Nat.gcd_rec]
  have h' : a % n = b % n := h
  show Nat.gcd a n = 1
  rw [e1, h', ← e2]
  exact hc

/-- A prime not dividing `n` is coprime to it. -/
lemma coprime_of_prime_not_dvd {p n : ℕ} (hpp : p.Prime) (h : ¬ p ∣ n) :
    Nat.Coprime p n := by
  have h1 : Nat.gcd p n ∣ p := Nat.gcd_dvd_left p n
  rcases hpp.eq_one_or_self_of_dvd _ h1 with h2 | h2
  · exact h2
  · exfalso
    exact h (h2 ▸ Nat.gcd_dvd_right p n)

/-- CRT for a pairwise-coprime finset of moduli. -/
lemma crt_finset_coprime (S : Finset ℕ) (g : ℕ → ℕ) :
    Set.Pairwise (S : Set ℕ) Nat.Coprime →
    ∃ T, ∀ p ∈ S, T ≡ g p [MOD p] := by
  induction S using Finset.induction with
  | empty =>
    intro _
    exact ⟨0, by simp⟩
  | insert p S' h_notmem ih =>
    intro hS
    have hS' : Set.Pairwise (S' : Set ℕ) Nat.Coprime := by
      intro x hx y hy hne
      exact hS (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx)))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hy))) hne
    obtain ⟨T', hT'⟩ := ih hS'
    have hMc : Nat.Coprime (∏ q ∈ S', q) p := by
      rw [Nat.coprime_comm]
      apply Nat.Coprime.prod_right
      intro q hq
      have hne : p ≠ q := fun h => h_notmem (h.symm ▸ hq)
      exact hS (Finset.mem_coe.mpr (Finset.mem_insert_self p S'))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hq)) hne
    obtain ⟨T, hT1, hT2⟩ := Nat.chineseRemainder hMc T' (g p)
    refine ⟨T, fun q hq => ?_⟩
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · exact hT2
    · have hdvd : q ∣ ∏ q' ∈ S', q' := Finset.dvd_prod_of_mem (fun q' => q') hq
      exact (Nat.ModEq.of_dvd hdvd hT1).trans (hT' q hq)

/-- **Schinzel–Mordell obstruction (classical input, taken as an axiom).**

The classical lemma (Schinzel 1956, Mordell 1967) says that a polynomial identity
`4/(At+B) = Σⱼ 1/Fⱼ(t)`, valid for all `t`, with `Fⱼ ∈ ℤ[t]` (here viewed over ℚ)
of positive leading coefficient, forces the Jacobi symbol `(B/A) = -1`.
For `8 ∣ A` (as in our progressions, where `A = 24m'`), this implies the
disjunction below: either an odd prime divisor witnesses the non-residuosity,
or the obstruction is 2-adic (`B ≢ 1 mod 8`). The derivation of this disjunction
from `(B/A) = -1` is elementary and is packaged here as part of the classical
input. This is the *first* of two unproved classical inputs in the barrier
formalization. -/
axiom schinzel_mordell (A B : ℕ) (hA : 1 < A) (hgcd : Nat.Coprime A B) (h8 : 8 ∣ A)
    (hident : ∃ F : Fin 3 → Polynomial ℚ, (∀ j, 0 < (F j).leadingCoeff) ∧
      ∀ t : ℕ, (4:ℚ)/(A*t+B) = ∑ j, 1/((F j).eval (t:ℚ))) :
    (∃ q, q.Prime ∧ Odd q ∧ q ∣ A ∧ ¬ IsSquare (B : ZMod q)) ∨ (¬ (B ≡ 1 [MOD 8]))

/-- **Dirichlet's theorem on arithmetic progressions (classical input, taken as
an axiom).**

Infinitely many primes lie in any residue class coprime to the modulus.
Mathlib 4.34.1 only proves the special case of primes `≡ 1 [MOD k]`
(`infinite_setOfPred_prime_modEq_one` in
`Mathlib/NumberTheory/PrimesCongruentOne.lean`); the general statement is
packaged here as a classical input. This is the *second* of two unproved
classical inputs in the barrier formalization. -/
axiom dirichlet_arith_prog (M c : ℕ) (hcop : Nat.Coprime c M) :
    Set.Infinite { p : ℕ | p.Prime ∧ p ≡ c [MOD M] }

/-- The Round 16 barrier theorem: no finite polynomial-identity system covers
all primes of a square class mod 840; infinitely many escape. -/
theorem es_barrier {t : ℕ} (A B : Fin t → ℕ)
    (hA : ∀ i, 1 < A i) (hgcd : ∀ i, Nat.Coprime (A i) (B i))
    (h8 : ∀ i, 8 ∣ A i)
    (hident : ∀ i, ∃ F : Fin 3 → Polynomial ℚ, (∀ j, 0 < (F j).leadingCoeff) ∧
      ∀ s : ℕ, (4:ℚ)/((A i)*s + (B i)) = ∑ j, 1/((F j).eval (s:ℚ)))
    (r : ℕ) (hr : r = 1 ∨ r = 121 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529) :
    Set.Infinite { p : ℕ | p.Prime ∧ p ≡ r [MOD 840] ∧
      ∀ i, ¬ (p ≡ B i [MOD (A i)]) } := by
  -- Basic facts about the square class r
  have hr840 : Nat.Coprime r 840 := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr8 : r ≡ 1 [MOD 8] := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr_sq : ∀ q₀ : ℕ, IsSquare (r : ZMod q₀) := by
    intro q₀
    have hsq : ∀ (s : ℕ) (hs : r = s ^ 2), IsSquare (r : ZMod q₀) := by
      intro s hs
      have h : IsSquare (((s ^ 2 : ℕ)) : ZMod q₀) := ⟨(s : ZMod q₀), by push_cast; ring⟩
      rwa [← hs] at h
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsq 1 (by norm_num)
    · exact hsq 11 (by norm_num)
    · exact hsq 13 (by norm_num)
    · exact hsq 17 (by norm_num)
    · exact hsq 19 (by norm_num)
    · exact hsq 23 (by norm_num)
  -- Per-progression obstruction from the axiom, unified into one witness per i:
  -- either an odd prime with Bᵢ a nonsquare mod q, or the marker q = 2 for the
  -- 2-adic case (Bᵢ ≢ 1 mod 8).
  have hdisj : ∀ i, (∃ q, q.Prime ∧ Odd q ∧ q ∣ A i ∧ ¬ IsSquare (B i : ZMod q))
      ∨ ¬ (B i ≡ 1 [MOD 8]) :=
    fun i => schinzel_mordell (A i) (B i) (hA i) (hgcd i) (h8 i) (hident i)
  have hwit : ∀ i, ∃ qq, (qq.Prime ∧ Odd qq ∧ qq ∣ A i ∧ ¬ IsSquare (B i : ZMod qq))
      ∨ (qq = 2 ∧ ¬ (B i ≡ 1 [MOD 8])) := by
    intro i
    rcases hdisj i with h | h
    · obtain ⟨qq, h1, h2, h3, h4⟩ := h
      exact ⟨qq, Or.inl ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨2, Or.inr ⟨rfl, h⟩⟩
  choose q hq using hwit
  have hqp : ∀ i, (q i).Prime := by
    intro i
    rcases hq i with ⟨h1, _, _, _⟩ | h2
    · exact h1
    · obtain ⟨h2eq, _⟩ := h2
      rw [h2eq]; exact Nat.prime_two
  have hqdvd : ∀ i, q i ∣ A i := by
    intro i
    rcases hq i with ⟨_, _, hd, _⟩ | h2
    · exact hd
    · obtain ⟨h2eq, _⟩ := h2
      rw [h2eq]
      exact dvd_trans (by decide) (h8 i)
  -- The deduped set of witness primes
  set Q : Finset ℕ := Finset.univ.image q with hQ_def
  have hQprime : ∀ p ∈ Q, p.Prime := by
    intro p hp
    rw [hQ_def] at hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hqp i
  -- The chosen residue mod p: 1 if p ∣ r (then r ≡ 0, use 1 which is a square),
  -- else r % p (a square since r itself is a square)
  set cres : ℕ → ℕ := fun p => if p ∣ r then 1 else r % p with hcres_def
  have hcres_eq : ∀ p, cres p = (if p ∣ r then 1 else r % p) := fun p => rfl
  have hcres_sq : ∀ (p : ℕ) [NeZero p], IsSquare ((cres p : ℕ) : ZMod p) := by
    intro p _
    by_cases hpr : p ∣ r
    · have e : cres p = 1 := by rw [hcres_eq p, if_pos hpr]
      rw [e]
      simpa using IsSquare.one
    · have e : cres p = r % p := by rw [hcres_eq p, if_neg hpr]
      rw [e]
      have e2 : ((r % p : ℕ) : ZMod p) = (r : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq r p)
      rw [e2]; exact hr_sq p
  -- The witness prime really does block its progression's residue
  have hesc : ∀ (i : Fin t) (qq : ℕ), qq.Prime → qq ∣ A i →
      ¬ IsSquare (B i : ZMod qq) → ¬ (cres qq ≡ B i [MOD qq]) := by
    intro i qq hqq' _ hqns hcon
    haveI : NeZero qq := ⟨hqq'.ne_zero⟩
    apply hqns
    have heq : ((cres qq : ℕ) : ZMod qq) = ((B i : ℕ) : ZMod qq) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcon
    have hsq : IsSquare ((cres qq : ℕ) : ZMod qq) := hcres_sq qq
    rwa [heq] at hsq
  -- Primes whose residue we must control via CRT (those not dividing 840)
  set S : Finset ℕ := Q.filter (fun p => ¬ p ∣ 840) with hS_def
  have hSprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    rw [hS_def] at hp
    exact hQprime p (Finset.mem_filter.mp hp).1
  have hSpair : Set.Pairwise (S : Set ℕ) Nat.Coprime := by
    intro a ha b hb hne
    have hpa := hSprime a ha
    have hpb := hSprime b hb
    apply coprime_of_prime_not_dvd hpa
    intro hdvd
    rcases hpb.eq_one_or_self_of_dvd a hdvd with h | h
    · exact hpa.ne_one h
    · exact hne h
  have hScop : ∀ p ∈ S, Nat.Coprime 840 p := by
    intro p hpS
    rw [hS_def] at hpS
    have hpQ := (Finset.mem_filter.mp hpS).1
    have hp840 := (Finset.mem_filter.mp hpS).2
    have hpp := hQprime p hpQ
    have h1 : Nat.gcd 840 p ∣ p := Nat.gcd_dvd_right 840 p
    rcases hpp.eq_one_or_self_of_dvd _ h1 with h | h
    · exact h
    · exfalso; exact hp840 (h ▸ Nat.gcd_dvd_left 840 p)
  -- For p ∈ S, solve 840 * t ≡ cres p - r (in ZMod p) via the unit 840
  have hex : ∀ p ∈ S, ∃ tt : ℕ, (840 : ZMod p) * (tt : ZMod p)
      = ((cres p : ℕ) : ZMod p) - (r : ZMod p) := by
    intro p hpS
    have hpp := hSprime p hpS
    haveI : NeZero p := ⟨hpp.ne_zero⟩
    have hcop := hScop p hpS
    set u : (ZMod p)ˣ := ZMod.unitOfCoprime 840 hcop with hu_def
    have hcoe : ((u : (ZMod p)ˣ) : ZMod p) = (840 : ZMod p) :=
      ZMod.coe_unitOfCoprime 840 hcop
    have h1 : ((u : (ZMod p)ˣ) : ZMod p) * (((u⁻¹ : (ZMod p)ˣ) : ZMod p)) = 1 := by
      simp
    set Y : ZMod p :=
      (((u⁻¹ : (ZMod p)ˣ) : ZMod p)) * (((cres p : ℕ) : ZMod p) - (r : ZMod p)) with hY_def
    refine ⟨Y.val, ?_⟩
    rw [ZMod.natCast_zmod_val, hY_def, ← hcoe]
    linear_combination (((cres p : ℕ) : ZMod p) - (r : ZMod p)) * h1
  -- Turn the dependent choice into a plain function `g' : ℕ → ℕ` for the CRT lemma
  have key : ∀ p : ℕ, ∃ tt : ℕ, p ∈ S →
      (840 : ZMod p) * (tt : ZMod p) = ((cres p : ℕ) : ZMod p) - (r : ZMod p) := by
    intro p
    by_cases hpS : p ∈ S
    · exact ⟨Classical.choose (hex p hpS),
        fun _ => Classical.choose_spec (hex p hpS)⟩
    · exact ⟨0, fun h => (hpS h).elim⟩
  choose g' hg' using key
  obtain ⟨T, hT⟩ := crt_finset_coprime S g' hSpair
  -- The merged residue class and modulus
  set c : ℕ := r + 840 * T with hc_def
  set M : ℕ := 840 * ∏ p ∈ Q, p with hM_def
  -- c hits the chosen residue at every witness prime
  have hczmod : ∀ p ∈ Q, ((c : ℕ) : ZMod p) = ((cres p : ℕ) : ZMod p) := by
    intro p hpQ
    have hpp := hQprime p hpQ
    haveI : NeZero p := ⟨hpp.ne_zero⟩
    by_cases hp840 : p ∣ 840
    · have hpr : ¬ p ∣ r := by
        intro hpr
        have hgcd : Nat.gcd r 840 = 1 := hr840
        have hdvd : p ∣ Nat.gcd r 840 := Nat.dvd_gcd hpr hp840
        rw [hgcd, Nat.dvd_one] at hdvd
        exact hpp.ne_one hdvd
      have e1 : ((c : ℕ) : ZMod p) = (r : ZMod p) := by
        have h0 : ((840 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff 840 p).mpr hp840
        show ((r + 840 * T : ℕ) : ZMod p) = _
        rw [Nat.cast_add, Nat.cast_mul, h0, zero_mul, add_zero]
      have e2 : ((cres p : ℕ) : ZMod p) = (r : ZMod p) := by
        have e : cres p = r % p := by rw [hcres_eq p, if_neg hpr]
        rw [e]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq r p)
      rw [e1, e2]
    · have hpS : p ∈ S := by rw [hS_def]; exact Finset.mem_filter.mpr ⟨hpQ, hp840⟩
      have eT : ((T : ℕ) : ZMod p) = ((g' p : ℕ) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hT p hpS)
      have hgp := hg' p hpS
      show ((r + 840 * T : ℕ) : ZMod p) = ((cres p : ℕ) : ZMod p)
      rw [Nat.cast_add, Nat.cast_mul, eT]
      linear_combination hgp
  have h4 : ∀ p ∈ Q, c ≡ cres p [MOD p] := by
    intro p hp
    haveI : NeZero p := ⟨(hQprime p hp).ne_zero⟩
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (hczmod p hp)
  -- c is coprime to the modulus
  have hcc840 : Nat.Coprime c 840 := by
    show Nat.Coprime (r + 840 * T) 840
    rw [mul_comm (840:ℕ) T]
    exact (Nat.coprime_add_mul_right_left r 840 T).mpr hr840
  have hccp : ∀ p ∈ Q, Nat.Coprime c p := by
    intro p hpQ
    have hpp := hQprime p hpQ
    apply coprime_of_modEq (h4 p hpQ)
    by_cases hpr : p ∣ r
    · have e : cres p = 1 := by rw [hcres_eq p, if_pos hpr]
      rw [e]
      exact (Nat.coprime_one_left_iff p).mpr trivial
    · have e : cres p = r % p := by rw [hcres_eq p, if_neg hpr]
      rw [e]
      apply coprime_of_modEq (Nat.mod_modEq r p)
      exact (coprime_of_prime_not_dvd hpp hpr).symm
  have hcopM : Nat.Coprime c M := by
    have h2 : IsRelPrime c (∏ p ∈ Q, p) :=
      Nat.coprime_iff_isRelPrime.mp (Nat.Coprime.prod_right hccp)
    have h1 : IsRelPrime c 840 := Nat.coprime_iff_isRelPrime.mp hcc840
    rw [hM_def, Nat.coprime_iff_isRelPrime]
    exact IsRelPrime.mul_right h1 h2
  -- Dirichlet: infinitely many primes in the class
  have hMpos : 0 < M := by
    rw [hM_def]
    apply Nat.mul_pos (by norm_num)
    apply Finset.prod_pos
    intro p hpQ
    exact (hQprime p hpQ).pos
  haveI : NeZero M := ⟨hMpos.ne'⟩
  have hinf := dirichlet_arith_prog M c hcopM
  apply Set.Infinite.mono _ hinf
  intro p hp
  rw [Set.mem_setOf_eq] at hp
  obtain ⟨hpprime, hpc⟩ := hp
  haveI : NeZero (840:ℕ) := ⟨by norm_num⟩
  have hpr840 : p ≡ r [MOD 840] := by
    have h1 : p ≡ c [MOD 840] :=
      Nat.ModEq.of_dvd (by rw [hM_def]; exact dvd_mul_right 840 _) hpc
    have h2 : c ≡ r [MOD 840] := by
      have e : ((c : ℕ) : ZMod 840) = (r : ZMod 840) := by
        have h0 : ((840 : ℕ) : ZMod 840) = 0 :=
          (ZMod.natCast_eq_zero_iff 840 840).mpr (dvd_refl 840)
        show ((r + 840 * T : ℕ) : ZMod 840) = _
        rw [Nat.cast_add, Nat.cast_mul, h0, zero_mul, add_zero]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp e
    exact h1.trans h2
  refine ⟨hpprime, hpr840, ?_⟩
  intro i
  rcases hq i with hleft | hright
  · -- odd witness prime case: p would have to hit Bᵢ mod qᵢ, but qᵢ blocks it
    obtain ⟨hqp', _, hqd, hqns⟩ := hleft
    intro hcon
    have h2 : p ≡ B i [MOD q i] := Nat.ModEq.of_dvd hqd hcon
    have hqiQ : q i ∈ Q := by
      rw [hQ_def]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have h3 : p ≡ c [MOD q i] := by
      apply Nat.ModEq.of_dvd _ hpc
      rw [hM_def]
      exact dvd_trans (Finset.dvd_prod_of_mem (fun p => p) hqiQ) (dvd_mul_left _ _)
    have h5 : B i ≡ cres (q i) [MOD q i] :=
      (h2.symm.trans h3).trans (h4 (q i) hqiQ)
    exact (hesc i (q i) hqp' hqd hqns) h5.symm
  · -- 2-adic case: p ≡ r ≡ 1 (mod 8) but Bᵢ ≢ 1 (mod 8)
    obtain ⟨-, h2adic⟩ := hright
    intro hcon
    have h1 : p ≡ B i [MOD 8] := Nat.ModEq.of_dvd (h8 i) hcon
    have h2 : p ≡ r [MOD 8] := Nat.ModEq.of_dvd (by decide) hpr840
    have h3 : B i ≡ 1 [MOD 8] := h1.symm.trans (h2.trans hr8)
    exact h2adic h3
