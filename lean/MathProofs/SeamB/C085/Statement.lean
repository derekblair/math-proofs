import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

/-!
# Seam B Entry C085 (OEIS A294912): Frozen Statement File

Verbatim transcription of the definition and three theorem signatures from the frozen
pin manifest `PIN-C085.md` v2
(`sha256: a40073c9a7a613f93535ebe7506920f188aba9ee31820696dbebd3072717d154`),
which supersedes `PIN-C085.md` v1 (`NO-GO`: Hilko Koning's Dec 09 2019 composite
characterization of OEIS `A294912` is refuted by `k = 93,041,293,345`,
`n = 2*k + 1 = 186,082,586,691 = 3 * 131 * 281 * 617 * 2731`) and pins both the formal
refutation (`c085_refutation`, `c085_witness`) and the salvaged true characterization
(`c085_positive_characterization`, Koning's uncorrupted `A244628` conjecture).

All proofs live in `MathProofs/SeamB/C085/Solution.lean` with zero `sorry`.
-/

namespace C085

/-- Defining four-congruence predicate of OEIS `A294912` on `n : ℕ` (Jonas Kaiser,
Nov 10 2017), with `ceiling((3/4)*n)` pinned to `(3 * n + 3) / 4` and `floor((1/4)*n)`
pinned to `n / 4` verbatim from `PIN-C085.md` v1/v2. -/
def inA294912 (n : ℕ) : Prop :=
  Nat.ModEq n (2 ^ (n - 1)) 1 ∧
  Nat.ModEq n ((2 * n - 1) * (2 ^ ((n - 1) / 2))) 1 ∧
  Nat.ModEq n (4 * ((3 * n + 3) / 4) - 2) 1 ∧
  Nat.ModEq n (2 ^ ((n + 1) / 2) + (n / 4) * 2 ^ (((n + 1) / 2) + 1)) 1

/-- Formal refutation of Hilko Koning's Dec 09 2019 `A294912` composite characterization
(`PIN-C085.md` v1): the biconditional fails at `k = 93,041,293,345`. -/
theorem c085_refutation :
    ¬ (∀ k : ℕ, 1 < k → ¬Nat.Prime (2 * k + 1) →
      (inA294912 (2 * k + 1) ↔ (3 * (2 * k + 1)) ∣ (2 ^ k + 1))) := by
  sorry

/-- Smallest counterexample witness (`k = 93,041,293,345`, `n = 2*k + 1 = 186,082,586,691 =
3 * 131 * 281 * 617 * 2731`, `A244628(1138)` = `A376255(2)`): `n` belongs to `A294912`,
while `(3 * n) ∣ (2 ^ k + 1)` fails. -/
theorem c085_witness :
    inA294912 186082586691 ∧ ¬ ((3 * 186082586691) ∣ (2 ^ 93041293345 + 1)) := by
  sorry

/-- Salvaged true characterization of odd composites in `A294912` (Koning's uncorrupted
Dec 05 2019 / Jan 27 2022 `A244628` conjecture, omitting the spurious factor of `3`). -/
theorem c085_positive_characterization :
    ∀ k : ℕ, 1 < k → ¬Nat.Prime (2 * k + 1) →
      (inA294912 (2 * k + 1) ↔ (k % 2 = 1 ∧ (2 * k + 1) ∣ (2 ^ k + 1))) := by
  sorry

end C085
