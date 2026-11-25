import Mathlib

/-! # Translation march rigidity and hole-sweeping theorems (SS-003) -/

namespace TranslationMarch

open Finset

def pairSums (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p : ℤ × ℤ => p.1 + p.2)

def rawBlocked (A : Finset ℤ) : Finset ℤ :=
  A ∪ (((pairSums A) ×ˢ A).image (fun p : ℤ × ℤ => p.1 - p.2)
    ∪ ((pairSums A).filter (fun s => s % 2 = 0)).image (fun s => s / 2))

def blocked (A : Finset ℤ) (N : ℤ) : Finset ℤ :=
  rawBlocked A ∩ Finset.Icc 1 N

def holes (A : Finset ℤ) (N : ℤ) : Finset ℤ :=
  Finset.Icc 1 N \ blocked A N

theorem rigidity (A : Finset ℤ) (N t : ℤ) :
    blocked (A.image (· + t)) N
      = (rawBlocked A).image (· + t) ∩ Finset.Icc 1 N := by
  sorry

theorem march (A : Finset ℤ) (N t : ℤ)
    (hN : 1 ≤ N)
    (hA : A ⊆ Finset.Icc 1 N)
    (hsat : Finset.Icc 1 N ⊆ rawBlocked A)
    (hAt : (A.image (· + t)) ⊆ Finset.Icc 1 N)
    (ht : 0 ≤ t) :
    holes (A.image (· + t)) N
      = (Finset.Icc 1 t).filter (fun p => p - t ∉ rawBlocked A) := by
  sorry

theorem march_neg (A : Finset ℤ) (N t : ℤ)
    (hN : 1 ≤ N)
    (hA : A ⊆ Finset.Icc 1 N)
    (hsat : Finset.Icc 1 N ⊆ rawBlocked A)
    (hAt : (A.image (· + t)) ⊆ Finset.Icc 1 N)
    (ht : t ≤ 0) :
    holes (A.image (· + t)) N
      = (Finset.Icc (N + t + 1) N).filter (fun p => p - t ∉ rawBlocked A) := by
  sorry

end TranslationMarch
