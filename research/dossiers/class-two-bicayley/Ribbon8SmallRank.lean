import Ribbon8Chart
import Mathlib.GroupTheory.OrderOfElement

namespace Ribbon8Small
open HaarUniversal36 HaarClass4Ports HaarClass4Generate
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- Subtract two parallel equations differing by one copy of v, then
two differing by a power of u coprime to the p-torsion. -/
theorem rank (c u v : G) (p m k : Nat) (coprime : p.Coprime m)
    (U : u^p=1)
    (A : c*u^(m+1)*v^k=1)
    (B : c*u*v^(k+1)=1)
    (D : c*u*v^k=1) : u=1 ∧ v=1 := by
  have e : (c*u*v^k)*v = (c*u*v^k)*1 := by
    rw [mul_one,D,one_mul]
    have h := B
    rw [pow_succ,←mul_assoc] at h
    rw [D,one_mul] at h
    exact h
  have ev : v=1 := mul_left_cancel e
  have h : u^m=1 := by
    have E : c*u^(m+1)=c*u := by
      simpa [ev] using A.trans D.symm
    have F := mul_left_cancel E
    rw [pow_succ] at F
    exact mul_right_cancel (F.trans (one_mul u).symm)
  refine ⟨?_,ev⟩
  have d := Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr U)
    (orderOf_dvd_iff_pow_eq_one.mpr h)
  rw [coprime.gcd_eq_one] at d
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp d)

theorem rank5 (c u v : G) (U : u^5=1)
    (A : c*u^4*v^2=1) (B : c*u*v^3=1) (D : c*u*v^2=1) :
    u=1 ∧ v=1 := rank c u v 5 3 2 (by decide) U A B D

theorem rank7 (c u v : G) (U : u^7=1)
    (A : c*u^6*v^3=1) (B : c*u*v^4=1) (D : c*u*v^3=1) :
    u=1 ∧ v=1 := rank c u v 7 5 3 (by decide) U A B D

/-- In a class-three group, centrality of C^p forces the two port
triple commutators to have p-th power one. -/
theorem torsion (c x u : G) (p : Nat)
    (cu : Commute u c) (e : c*x=x*c*u) (C : Commute (c^p) x) : u^p=1 := by
  have Q := HaarCycle.shift c x u cu e (p:ℤ)
  simp only [zpow_natCast] at Q
  rw [C.eq] at Q
  exact mul_left_cancel (Q.symm.trans (mul_one _).symm)

end Ribbon8Small
#print axioms Ribbon8Small.rank5
#print axioms Ribbon8Small.rank7
#print axioms Ribbon8Small.torsion
