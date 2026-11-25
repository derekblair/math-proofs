import NonconvLocal
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators
open Filter Topology
namespace Nonconv
set_option maxRecDepth 16384
abbrev State := Fin 44
def q : State := 0
def edge (u v : State) : Bool := decide ((row u).suffixKey = (row v).prefixKey)
def adj (rev : Bool) (u v : State) : Bool := if rev then edge v u else edge u v

def ways (rev : Bool) : Nat → State → Nat
  | 0, _ => 1
  | m+1, u => ∑ v : State, if adj rev u v then ways rev m v else 0

set_option maxHeartbeats 12000000 in
theorem base3 : ∀ (rev : Bool) (u : State), ways rev 3 u = 2 := by decide

theorem ways3 (rev : Bool) (m : Nat) (u : State) :
    ways rev (m+3) u = 2 * ways rev m u := by
  induction m generalizing u with
  | zero => simpa [ways] using base3 rev u
  | succ m ih =>
    rw [show m+1+3=(m+3)+1 by omega]
    change (∑ v : State, if adj rev u v then ways rev (m+3) v else 0) =
      2*(∑ v : State, if adj rev u v then ways rev m v else 0)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [ih v]
    split_ifs <;> rfl

theorem scaleWays (rev : Bool) (k r : Nat) (u : State) :
    ways rev (3*k+r) u = 2^k * ways rev r u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 3*(k+1)+r=3*k+r+3 by omega,ways3,ih,pow_succ]
    ring

def totalRoutes (m : Nat) : Nat := ∑ u : State, ways false m u

theorem route_scale (k r : Nat) : totalRoutes (3*k+r) = 2^k * totalRoutes r := by
  simp only [totalRoutes,scaleWays,Finset.mul_sum]

set_option maxHeartbeats 12000000 in
theorem route_bases : totalRoutes 0=44 ∧ totalRoutes 1=56 ∧ totalRoutes 2=72 := by decide

set_option maxHeartbeats 12000000 in
theorem q_bases (rev : Bool) : ways rev 0 q=1 ∧ ways rev 1 q=1 ∧ ways rev 2 q=2 := by decide +revert

def marks (m : Nat) : Nat :=
  ∑ i ∈ Finset.range (m+1), ways true i q * ways false (m-i) q

theorem marksStep (m : Nat) :
    marks (m+3) = 2*marks m +
      (ways false (m+3) q + ways false (m+2) q + 2*ways false (m+1) q) := by
  unfold marks
  rw [show m+3+1=3+(m+1) by omega,Finset.sum_range_add]
  have he : (∑ i ∈ Finset.range (m+1), ways true (3+i) q * ways false (m+3-(3+i)) q) =
      2*(∑ i ∈ Finset.range (m+1), ways true i q * ways false (m-i) q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show 3+i=i+3 by omega,ways3,show m+3-(i+3)=m-i by omega]
    ring
  rw [he]
  have h0 := (q_bases true).1
  have h1 := (q_bases true).2.1
  have h2 := (q_bases true).2.2
  simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add,h0,h1,h2, one_mul, Nat.sub_zero]
  rw [show m+3-1=m+2 by omega,show m+3-2=m+1 by omega]
  omega

theorem marks0 (k : Nat) : marks (3*k) = (3*k+1)*2^k := by
  induction k with
  | zero =>
    change marks 0 = 1
    decide
  | succ k ih =>
    rw [show 3*(k+1)=3*k+3 by omega,marksStep,ih]
    rw [scaleWays,scaleWays,scaleWays]
    obtain ⟨h0,h1,h2⟩ := q_bases false
    rw [h1,h2]
    rw [base3,pow_succ]
    ring

theorem marks1 (k : Nat) : marks (3*k+1) = (4*k+2)*2^k := by
  induction k with
  | zero =>
    change marks 1 = 2
    decide
  | succ k ih =>
    rw [show 3*(k+1)+1=(3*k+1)+3 by omega,marksStep,ih]
    rw [show 3*k+1+3=3*(k+1)+1 by omega,show 3*k+1+2=3*(k+1)+0 by omega]
    rw [scaleWays,scaleWays,show 3*k+1+1=3*k+2 by omega,scaleWays]
    obtain ⟨h0,h1,h2⟩ := q_bases false
    rw [h0,h1,h2,pow_succ]
    ring

theorem marks2 (k : Nat) : marks (3*k+2) = (5*k+5)*2^k := by
  induction k with
  | zero =>
    change marks 2 = 5
    decide
  | succ k ih =>
    rw [show 3*(k+1)+2=(3*k+2)+3 by omega,marksStep,ih]
    rw [show 3*k+2+3=3*(k+1)+2 by omega,show 3*k+2+2=3*(k+1)+1 by omega,
      show 3*k+2+1=3*(k+1)+0 by omega,scaleWays,scaleWays,scaleWays]
    obtain ⟨h0,h1,h2⟩ := q_bases false
    rw [h0,h1,h2,pow_succ]
    ring
end Nonconv
