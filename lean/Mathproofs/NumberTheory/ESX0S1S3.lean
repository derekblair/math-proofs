import Mathlib

/-!
# Lemma X0 and Lemma S1S3 (R104; R107 sharpening)

Source: `~/workspace/math-unsolved/ROUND104_DOSSIER.md` §2 (Round 104, [PROVED*]);
`~/workspace/math-unsolved/lean_handoff_r107_X0S1S3.md` (Round 107, full equivalence).

Setup: a branch-2 Erdős–Straus identity `(A, r₁, m, s)` at `M′` in R67's
cubic framework. Write `A = d₀A′`, `r₁ = d₀B′` with `d₀ = gcd(A, r₁)`,
so `gcd(A′, B′) = 1`. The s-conditions are:
- (S1): `M′ ∣ p·(s+m)` (read as `p·(s+m) ∈ M′·ℕ`, integrality included)
- (S3): `m·A·r₁ ∣ x₀·(A+r₁)` (q-integrality)

**Lemma X0 (x₀-divisibility).** `A′·B′` divides `x₀`.
The q-integrality condition is `m·A·r₁ ∣ x₀(A+r₁)`, i.e.
`m·d₀·A′B′ ∣ x₀(A′+B′)`. Since `gcd(A′B′, A′+B′) = 1` (a prime dividing
both would divide both `A′` and `B′`), we get `A′B′ ∣ x₀`.

**Lemma S1S3 (s-condition collapse).** Writing `x₀ = A′B′·y` (Lemma X0),
the s-dependent conditions collapse: R104 proved `(S3) ⟹ (S1)` in reduced
divisibility form: `m·d₀·A′B′ ∣ A′B′·y·(A′+B′)` implies
`m·d₀ ∣ y·(A′+B′)` (for `A′B′ > 0`).

R107 strengthened this to a **full equivalence** (pure divisibility, no
monotone substitutions — R59-class direction bugs inapplicable). The two
s-conditions reduce to the same divisibility `m·d₀ ∣ y·(A′+B′)`:
- `lemma_S1S3_i`: `(S1) ⟺ m·d₀ ∣ (A′+B′)·y`, via the cross-multiplied
  framework relation `p·(s+m)·(m·d₀) = M′·((A′+B′)·y)` (avoids division;
  from `p = XSTEP′(A′+B′)/(m·d₀·A′B′)`, `s+m = 4·A′B′·y`, `M′ = 4·XSTEP′`).
- `lemma_S1S3_ii`: `(S3) ⟺ m·d₀ ∣ y·(A′+B′)`, by substituting
  `A = d₀A′`, `r₁ = d₀B′`, `x₀ = A′B′·y` and cancelling `d₀·(A′B′) > 0`.
- `lemma_S1S3_collapse`: `(S1) ⟺ (S3)` — the two directions share the
  same target divisibility up to `mul_comm`.
-/

namespace ESX0S1S3

/-- `gcd(A′B′, A′+B′) = 1` from `gcd(A′, B′) = 1`. -/
theorem coprime_mul_add (A' B' : ℕ) (hcop : Nat.Coprime A' B') :
    Nat.Coprime (A' * B') (A' + B') := by
  rw [Nat.coprime_mul_iff_left]
  refine ⟨Nat.coprime_self_add_right.mpr hcop, ?_⟩
  have h := Nat.coprime_self_add_right.mpr hcop.symm
  rwa [add_comm B' A'] at h

/-- Lemma X0 (R104): `A′·B′ ∣ x₀`. -/
theorem lemma_X0 {m d₀ A' B' x₀ : ℕ} (hcop : Nat.Coprime A' B')
    (hdvd : m * d₀ * (A' * B') ∣ x₀ * (A' + B')) : A' * B' ∣ x₀ := by
  have hmid : A' * B' ∣ x₀ * (A' + B') :=
    Nat.dvd_trans ⟨m * d₀, by ring⟩ hdvd
  rw [mul_comm x₀ (A' + B')] at hmid
  exact (coprime_mul_add A' B' hcop).dvd_of_dvd_mul_left hmid

/-- Lemma S1S3 (R104): `(S3) ⟹ (S1)` — the s-condition collapse, in
reduced divisibility form. -/
theorem lemma_S1S3 {m d₀ A' B' y : ℕ} (hpos : 0 < A' * B')
    (hS3 : m * d₀ * (A' * B') ∣ (A' * B') * y * (A' + B')) :
    m * d₀ ∣ y * (A' + B') := by
  obtain ⟨k, hk⟩ := hS3
  have h1 : (A' * B') * (y * (A' + B')) = (A' * B') * ((m * d₀) * k) := by
    linear_combination hk
  have hcancel : y * (A' + B') = (m * d₀) * k :=
    Nat.mul_left_cancel hpos h1
  exact ⟨k, hcancel⟩

/-- Lemma S1S3(i) (R107): `(S1) ⟺ m·d₀ ∣ (A′+B′)·y`, via the
cross-multiplied framework relation. -/
theorem lemma_S1S3_i {p s m M' d₀ A' B' y : ℕ}
    (hd₀ : 0 < d₀) (hm : 0 < m) (hM : 0 < M')
    (hrel : p * (s + m) * (m * d₀) = M' * ((A' + B') * y)) :
    (M' ∣ p * (s + m)) ↔ (m * d₀ ∣ (A' + B') * y) := by
  constructor
  · -- (→): p*(s+m) = M'*k. Then M'*(k*(m*d₀)) = M'*((A'+B')*y); cancel M'.
    rintro ⟨k, hk⟩
    have h1 : M' * (k * (m * d₀)) = M' * ((A' + B') * y) := by
      calc M' * (k * (m * d₀)) = (M' * k) * (m * d₀) := by ring
        _ = (p * (s + m)) * (m * d₀) := by rw [hk]
        _ = p * (s + m) * (m * d₀) := by ring
        _ = M' * ((A' + B') * y) := hrel
    have h2 : k * (m * d₀) = (A' + B') * y := Nat.mul_left_cancel hM h1
    exact ⟨k, by rw [mul_comm (m * d₀) k]; exact h2.symm⟩
  · -- (←): (A'+B')*y = (m*d₀)*k. Then p*(s+m)*(m*d₀) = (M'*k)*(m*d₀); cancel (m*d₀).
    rintro ⟨k, hk⟩
    have h1 : p * (s + m) * (m * d₀) = (M' * k) * (m * d₀) := by
      calc p * (s + m) * (m * d₀) = M' * ((A' + B') * y) := hrel
        _ = M' * ((m * d₀) * k) := by rw [hk]
        _ = (M' * k) * (m * d₀) := by ring
    have h2 : p * (s + m) = M' * k := Nat.mul_right_cancel (Nat.mul_pos hm hd₀) h1
    exact ⟨k, h2⟩

/-- Lemma S1S3(ii) (R107): `(S3) ⟺ m·d₀ ∣ y·(A′+B′)`, by substitution
and cancellation of `d₀·(A′B′) > 0`. -/
theorem lemma_S1S3_ii {m A r₁ x₀ d₀ A' B' y : ℕ}
    (hd₀ : 0 < d₀) (hAB : 0 < A' * B')
    (hA : A = d₀ * A') (hr : r₁ = d₀ * B') (hx : x₀ = A' * B' * y) :
    (m * A * r₁ ∣ x₀ * (A + r₁)) ↔ (m * d₀ ∣ y * (A' + B')) := by
  have e1 : m * A * r₁ = (m * d₀) * (d₀ * (A' * B')) := by rw [hA, hr]; ring
  have e2 : x₀ * (A + r₁) = (y * (A' + B')) * (d₀ * (A' * B')) := by
    rw [hA, hr, hx]; ring
  rw [e1, e2]
  exact Nat.mul_dvd_mul_iff_right (Nat.mul_pos hd₀ hAB)

/-- Lemma S1S3 collapse (R107): the s-conditions are equivalent —
`(S1) ⟺ (S3)`. Both reduce to the same divisibility `m·d₀ ∣ y·(A′+B′)`. -/
theorem lemma_S1S3_collapse {p s m M' A r₁ x₀ d₀ A' B' y : ℕ}
    (hd₀ : 0 < d₀) (hm : 0 < m) (hM : 0 < M') (hAB : 0 < A' * B')
    (hA : A = d₀ * A') (hr : r₁ = d₀ * B') (hx : x₀ = A' * B' * y)
    (hrel : p * (s + m) * (m * d₀) = M' * ((A' + B') * y)) :
    (M' ∣ p * (s + m)) ↔ (m * A * r₁ ∣ x₀ * (A + r₁)) := by
  rw [lemma_S1S3_i hd₀ hm hM hrel, mul_comm (A' + B') y,
    ← lemma_S1S3_ii hd₀ hAB hA hr hx]

end ESX0S1S3
