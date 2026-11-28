import N63TenPrice
import N63ArithmeticCode
import Mathlib.Tactic.IntervalCases

namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def rightCandidate5 (H : Array Nat) (y z : Nat) : Bool := (y != z) && !adj H y z

def rightGood5 (H : Array Nat) (y t : Nat) : Bool :=
  if t≥4 then (List.range 4).any (rightCandidate5 H y) else
  if t=3 then (pairs 4).any (fun (a,b) => rightCandidate5 H y a &&
    rightCandidate5 H y b && !adj H a b) else false

def fiveTotals (h : Nat) (T : Fin 4 → Fin 4) : Prop :=
  let H := graphOfCode 4 h
  let D := (List.finRange 4).map fun i => (T i).val+2
  tfRight 4 H = true →
  30 + ((List.range 4).map (deg H 4)).sum ≤ 10+2*D.sum →
  (∀ y : Fin 4, rightGood5 H y.val ((T y).val+2) = false) →
  (h=12 ∨ h=18 ∨ h=33) ∧ ∀ y : Fin 4, (T y).val=1

instance (h : Nat) (T : Fin 4 → Fin 4) : Decidable (fiveTotals h T) := by
  unfold fiveTotals
  infer_instance

-- Finite right-block degree patterns, not full charts: at most 64×4^4 states.
-- Proof-producing blocks avoid a large simultaneous kernel calculation.
theorem fiveR0 : ∀ h ∈ List.range 8, ∀ T ∈ tuples 4 4, fiveTotals h T := by decide +kernel
theorem fiveR1 : ∀ h ∈ List.range 8, ∀ T ∈ tuples 4 4, fiveTotals (8+h) T := by decide +kernel
theorem fiveR2 : ∀ h ∈ List.range 8, ∀ T ∈ tuples 4 4, fiveTotals (16+h) T := by decide +kernel
theorem fiveR3 : ∀ h ∈ List.range 8, ∀ T ∈ tuples 4 4, fiveTotals (24+h) T := by decide +kernel
theorem fiveR4 : ∀ h ∈ List.range 8, ∀ T ∈ tuples 4 4, fiveTotals (32+h) T := by decide +kernel
theorem fiveR5 : ∀ h ∈ List.range 8, ∀ T ∈ tuples 4 4, fiveTotals (40+h) T := by decide +kernel
theorem fiveR6 : ∀ h ∈ List.range 8, ∀ T ∈ tuples 4 4, fiveTotals (48+h) T := by decide +kernel
theorem fiveR7 : ∀ h ∈ List.range 8, ∀ T ∈ tuples 4 4, fiveTotals (56+h) T := by decide +kernel

theorem fiveTotals_all (h : Nat) (hh : h<64) (T : Fin 4→Fin 4) : fiveTotals h T := by
  have mem (h' : Nat) (hh' : h'<8) : h' ∈ List.range 8 := List.mem_range.mpr hh'
  have mt := mem_tuples 4 4 T
  by_cases h0 : h<8
  · exact fiveR0 h (mem h h0) T mt
  by_cases h1 : h<16
  · simpa [show 8+(h-8)=h by omega] using fiveR1 (h-8) (mem _ (by omega)) T mt
  by_cases h2 : h<24
  · simpa [show 16+(h-16)=h by omega] using fiveR2 (h-16) (mem _ (by omega)) T mt
  by_cases h3 : h<32
  · simpa [show 24+(h-24)=h by omega] using fiveR3 (h-24) (mem _ (by omega)) T mt
  by_cases h4 : h<40
  · simpa [show 32+(h-32)=h by omega] using fiveR4 (h-32) (mem _ (by omega)) T mt
  by_cases h5 : h<48
  · simpa [show 40+(h-40)=h by omega] using fiveR5 (h-40) (mem _ (by omega)) T mt
  by_cases h6 : h<56
  · simpa [show 48+(h-48)=h by omega] using fiveR6 (h-48) (mem _ (by omega)) T mt
  · simpa [show 56+(h-56)=h by omega] using fiveR7 (h-56) (mem _ (by omega)) T mt

#print axioms fiveTotals_all
end Erdos151N63
