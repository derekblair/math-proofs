import HaarClass4Gate
import Mathlib.GroupTheory.PGroup

namespace HaarClass4Prime
open HaarClass4Normal HaarClass4Table HaarClass4Projection HaarClass4Certificates HaarClass4Gate HaarAllNoncommuting

variable {G H K : Type*} [Group G] [Group H] [Group K]

theorem prime_detect {p : ℕ} [Fact p.Prime] (HP : IsPGroup p H) {g : H} (hg : g≠1)
    {n : ℤ} (hn : ¬ (p:ℤ) ∣ n) : g^n≠1 := by
  intro e
  have a : (p:ℤ) ∣ (orderOf g:ℤ) := Int.natCast_dvd_natCast.mpr (HP.dvd_orderOf hg)
  exact hn (a.trans (orderOf_dvd_iff_zpow_eq_one.mpr e))

theorem small_ndvd {p : ℕ} (hp : p.Prime) (np : p≠2) {n : ℤ} (s : small n) :
    ¬ (p:ℤ) ∣ n := by
  intro d
  have h := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr d)
  have ee : |n| = (n.natAbs:ℤ) := (Int.natCast_natAbs n).symm
  have ss : n.natAbs=1 ∨ n.natAbs=2 ∨ n.natAbs=4 := by
    rcases s with s|s|s
    · left; omega
    · right; left; omega
    · right; right; omega
  rcases ss with ss | ss | ss
  · rw [ss] at h
    exact hp.ne_one (Nat.dvd_one.mp h)
  · rw [ss] at h
    exact np ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  · rw [ss,show (4:ℕ)=2^2 by decide] at h
    exact np ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem prime_certificate (M : Data G) (φ : G →* H) (ψ : G →* K)
    (hφ : KillsMid M φ) (hψ : KillsTail M ψ)
    {p : ℕ} [Fact p.Prime] (HP : IsPGroup p H) (np : p≠2)
    (hc : φ M.c≠1) (deep : ψ M.u≠1) :
    HasCycle M.x M.y 32 := by
  have ord (n : ℤ) (h : small n) : (φ M.c)^n≠1 :=
    prime_detect HP hc (small_ndvd Fact.out np h)
  by_cases he : p=3
  · have ord3 (n : ℤ) (h : n%3≠0) : (φ M.c)^n≠1 := by
      apply prime_detect HP hc
      rw [he]
      intro d
      exact h (Int.emod_eq_zero_of_dvd d)
    exact certificate M φ ψ hφ hψ ord ord3 deep
  · have hn : ¬ (p:ℤ) ∣ 3 := by
      intro h
      have hh : p∣3 := Int.natCast_dvd_natCast.mp h
      exact he ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide : Nat.Prime 3)).mp hh)
    have noF : M.c^3≠M.u*M.v := by
      intro eq
      have pp : (φ M.c)^(3:ℕ)=1 := by simpa [hφ.u,hφ.v] using congrArg φ eq
      exact (prime_detect HP hc hn) (by simpa using pp)
    exact ordinary_simple M φ ψ hφ hψ ord deep
      (fun h => noF ((first_is_one M).mp h)) (fun h => noF (second_implies_first M h))

end HaarClass4Prime

#print axioms HaarClass4Prime.prime_certificate
