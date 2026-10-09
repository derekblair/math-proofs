import Mathproofs.ESPrimeSquareT2
import Mathproofs.EST1TwoCase

/-!
# R140 QR-core theorem (Round 154, Lean formalization lane)

Formalizes R140's QR-core theorem §2: the hard core H = frontier ∖ (T1∪T2∪cubic)
contains the QR-core Q = {s ∈ S : x² ≡ s (mod M) is solvable}, and every
s ∈ Q is missed by the Type-I and Type-II systems.

Built on the machine-checked reciprocity kernels:
- T2: R134 Theorem 1, `ESPrimeSquareT2.t2_class_nonsquare`: the T2 class residue
  γ = −a·c⁻¹ ≡ −4a²d (mod q) is a nonsquare mod q (via `t2_jacobi_neg_one`).
- T1: R134 Theorem 2, `EST1TwoCase.t1_two_case`: x² ≡ −f (mod 4ad) is unsolvable.

New content (R140 §2, the two halves of the proof):
1. `isSquare_of_dvd_of_isSquare`: the reduction "s QR mod M ⟹ s QR mod
   every divisor m | M" (via the canonical `ZMod.castHom`).
2. `t2_class_transfer`: the class-equality transfer γ = −a·c⁻¹ = −4a²d in
   `ZMod q` (wraps `ESPrimeSquareT2.t2_classmap_simplify`, restated in the
   `t2_class_nonsquare` normal form).
3. `qr_core_t2_misses`: no s QR mod M lies in a T2 class.
4. `qr_core_t1_misses`: no s QR mod M lies in a T1 class.

The class conditions (s ≡ γ mod q / s ≡ −f mod 4ad ⟺ coverage) are R126
Thm 3 / Thm 1(b) with R131's b(0)-vacuity; the census direction is cited,
not re-formalized.
-/

namespace ESQRCore

/-- QR reduction (R140 §2): s QR mod M implies s QR mod every divisor m | M.
The canonical ring hom `ZMod.castHom` sends a square root mod M to a square
root mod m. -/
lemma isSquare_of_dvd_of_isSquare {M m s : ℕ} (hMm : m ∣ M)
    (hsq : IsSquare ((s : ℕ) : ZMod M)) :
    IsSquare ((s : ℕ) : ZMod m) := by
  obtain ⟨r, hr⟩ := hsq
  refine ⟨ZMod.castHom hMm (ZMod m) r, ?_⟩
  have hFr : ZMod.castHom hMm (ZMod m) r * ZMod.castHom hMm (ZMod m) r
      = ((s : ℕ) : ZMod m) := by
    rw [← map_mul, ← hr, map_natCast]
  exact hFr.symm

/-- T2 class-equality transfer (R140 §2): the T2 class γ = −a·c⁻¹ equals
−4a²d in `ZMod q`, since c·(4ad) = 4acd = q+1 ≡ 1 (mod q). Restates
`ESPrimeSquareT2.t2_classmap_simplify` in the `t2_class_nonsquare` normal
form. -/
lemma t2_class_transfer {q a c d : ℕ}
    (hfac : 4 * a * c * d = q + 1)
    (u : (ZMod q)ˣ) (hu : (u : ZMod q) = (c : ZMod q)) :
    -((a : ZMod q)) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)
      = (((-4 * (a : ℤ) ^ 2 * (d : ℤ)) : ℤ) : ZMod q) := by
  rw [ESPrimeSquareT2.t2_classmap_simplify hfac u hu]
  push_cast
  ring

/-- R140 QR-core theorem, T2 half: no s QR mod M lies in a T2 class.
If s is QR mod M it is QR mod q (reduction), but s ≡ γ (mod q) would make
the nonsquare γ = −a·c⁻¹ a square — contradicting `t2_class_nonsquare`. -/
theorem qr_core_t2_misses {M q a c d s : ℕ}
    (hqM : q ∣ M) (hq4 : q % 4 = 3)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hfac : 4 * a * c * d = q + 1)
    (hsq : IsSquare ((s : ℕ) : ZMod M))
    (u : (ZMod q)ˣ) (hu : (u : ZMod q) = (c : ZMod q))
    (hcov : ((s : ℕ) : ZMod q)
      = -((a : ZMod q)) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) :
    False := by
  have hsqQ : IsSquare ((s : ℕ) : ZMod q) := isSquare_of_dvd_of_isSquare hqM hsq
  rw [hcov, t2_class_transfer hfac u hu] at hsqQ
  exact ESPrimeSquareT2.t2_class_nonsquare hq4 ha hc hd hfac hsqQ

/-- R140 QR-core theorem, T1 half: no s QR mod M lies in a T1 class.
If s is QR mod M it is QR mod 4ad (reduction), but s ≡ −f (mod 4ad) would
make x² ≡ −f (mod 4ad) solvable — contradicting `t1_two_case`. -/
theorem qr_core_t1_misses {M a d f s : ℕ}
    (h4adM : 4 * a * d ∣ M)
    (ha : 1 ≤ a) (hd : 1 ≤ d)
    (hdvd : f ∣ 4 * a ^ 2 * d + 1)
    (hsq : IsSquare ((s : ℕ) : ZMod M))
    (hcov : ((s : ℕ) : ZMod (4 * a * d)) = -(((f : ℕ)) : ZMod (4 * a * d))) :
    False := by
  have hsq4 : IsSquare ((s : ℕ) : ZMod (4 * a * d)) :=
    isSquare_of_dvd_of_isSquare h4adM hsq
  obtain ⟨w, hw⟩ := hsq4
  have hne := EST1TwoCase.t1_two_case ha hd hdvd w
  apply hne
  rw [pow_two, ← hw]
  exact hcov

end ESQRCore
