import RibbonAffineBase
import RibbonAffineModCases
import RibbonAffineUniversal
import RibbonAffineWrapper

namespace RibbonAffine
open Ribbon5Bridge
universe u
variable {K : Type*} [Field K]
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def separated (a b : Kˣ) (k : Fin 8) : Prop :=
  ∀ i j : Fin 32, i.val < j.val →
    eRow a b (position k i.val) ≠ eRow a b (position k j.val)

private theorem records_agree (q : Fin 14) :
    (Universal.branch q).u=(obstruction q).1 ∧
    (Universal.branch q).v=(obstruction q).2.1 ∧
    (Universal.branch q).f=(obstruction q).2.2 := by decide +kernel +revert

private theorem from_branch (q : Fin 14) (t : Kˣ) (n : Nat)
    (odd : Odd n) (tn : t^n=1) (two : (2:K)≠0)
    (root : pl t 1 (obstruction q).2.2=0) :
    ∃ k : Fin 8, separated (t^(obstruction q).2.1) (t^(-(obstruction q).1)) k := by
  have m := records_agree q
  by_cases nn : ((Universal.branch q).constant:K)≠0
  · refine ⟨(Universal.branch q).word,?_⟩
    rw [←m.1,←m.2.1]
    have O := Odd.of_dvd_nat odd (orderOf_dvd_iff_pow_eq_one.mpr tn)
    exact Universal.separates q t O (by rwa [m.2.2]) nn
  push_neg at nn
  fin_cases q
  · have e : (2:K)=0 := by
      have Q : (Universal.branch (0:Fin 14)).constant=2 := by decide +kernel
      simpa [Q] using nn
    exact False.elim (two e)
  · have e : (2:K)=0 := by
      have Q : (Universal.branch (1:Fin 14)).constant=2 := by decide +kernel
      simpa [Q] using nn
    exact False.elim (two e)
  · have e : (10:K)=0 := by
      have Q : (Universal.branch (2:Fin 14)).constant=10 := by decide +kernel
      simpa [Q] using nn
    have five : (5:K)=0 := by
      rw [show (10:K)=2*5 by norm_num] at e
      exact (mul_eq_zero.mp e).resolve_left two
    exact False.elim (modcase_2_5 t n odd tn two five root)
  · have e : (10:K)=0 := by
      have Q : (Universal.branch (3:Fin 14)).constant=10 := by decide +kernel
      simpa [Q] using nn
    have five : (5:K)=0 := by
      rw [show (10:K)=2*5 by norm_num] at e
      exact (mul_eq_zero.mp e).resolve_left two
    exact False.elim (modcase_3_5 t n odd tn two five root)
  · have e : (5:K)=0 := by
      have Q : (Universal.branch (4:Fin 14)).constant=5 := by decide +kernel
      simpa [Q] using nn
    have five : (5:K)=0 := e
    exact False.elim (modcase_4_5 t n odd tn two five root)
  · have e : (5:K)=0 := by
      have Q : (Universal.branch (5:Fin 14)).constant=5 := by decide +kernel
      simpa [Q] using nn
    have five : (5:K)=0 := e
    exact False.elim (modcase_5_5 t n odd tn two five root)
  · have e : (42:K)=0 := by
      have Q : (Universal.branch (6:Fin 14)).constant=42 := by decide +kernel
      simpa [Q] using nn
    have charges : (3:K)=0 ∨ (7:K)=0 := by
      rw [show (42:K)=2*(3*7) by norm_num] at e
      exact mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left two)
    rcases charges with three|seven
    · exact False.elim (modcase_6_3 t n odd tn two three root)
    · refine ⟨6,?_⟩
      change separated (t^((1:ℤ))) (t^((0:ℤ))) 6
      rw [zpow_one,zpow_zero]
      exact seven_separates t seven (modcase_6_7 t n odd tn two seven root)
  · have e : (42:K)=0 := by
      have Q : (Universal.branch (7:Fin 14)).constant=42 := by decide +kernel
      simpa [Q] using nn
    have charges : (3:K)=0 ∨ (7:K)=0 := by
      rw [show (42:K)=2*(3*7) by norm_num] at e
      exact mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left two)
    rcases charges with three|seven
    · exact False.elim (modcase_7_3 t n odd tn two three root)
    · refine ⟨6,?_⟩
      change separated (t^((1:ℤ))) (t^((0:ℤ))) 6
      rw [zpow_one,zpow_zero]
      exact seven_separates t seven (modcase_7_7 t n odd tn two seven root)
  · have e : (10:K)=0 := by
      have Q : (Universal.branch (8:Fin 14)).constant=10 := by decide +kernel
      simpa [Q] using nn
    have five : (5:K)=0 := by
      rw [show (10:K)=2*5 by norm_num] at e
      exact (mul_eq_zero.mp e).resolve_left two
    exact False.elim (modcase_8_5 t n odd tn two five root)
  · have e : (10:K)=0 := by
      have Q : (Universal.branch (9:Fin 14)).constant=10 := by decide +kernel
      simpa [Q] using nn
    have five : (5:K)=0 := by
      rw [show (10:K)=2*5 by norm_num] at e
      exact (mul_eq_zero.mp e).resolve_left two
    exact False.elim (modcase_9_5 t n odd tn two five root)
  · have e : (5:K)=0 := by
      have Q : (Universal.branch (10:Fin 14)).constant=5 := by decide +kernel
      simpa [Q] using nn
    have five : (5:K)=0 := e
    exact False.elim (modcase_10_5 t n odd tn two five root)
  · have e : (5:K)=0 := by
      have Q : (Universal.branch (11:Fin 14)).constant=5 := by decide +kernel
      simpa [Q] using nn
    have five : (5:K)=0 := e
    exact False.elim (modcase_11_5 t n odd tn two five root)
  · have e : (2:K)=0 := by
      have Q : (Universal.branch (12:Fin 14)).constant=2 := by decide +kernel
      simpa [Q] using nn
    exact False.elim (two e)
  · have e : (2:K)=0 := by
      have Q : (Universal.branch (13:Fin 14)).constant=2 := by decide +kernel
      simpa [Q] using nn
    exact False.elim (two e)

theorem picks (a b : Kˣ) (n : Nat)
    (two : (2:K)≠0) (odd : Odd n) (ha : a^n=1) (hb : b^n=1) (nt : a≠1) :
    ∃ k : Fin 8, separated a b k := by
  classical
  by_cases good : separated a b 0
  · exact ⟨0,good⟩
  · unfold separated at good
    push_neg at good
    obtain ⟨i,j,lt,e⟩ := good
    obtain ⟨q,t,ha',hb',tn,nt',p⟩ := base_failure a b n ha hb nt odd two i j lt e
    rw [ha',hb']
    exact from_branch q t n odd tn two p

theorem certified_affine : AffineWitness.{u} := by
  intro G group m x y K field finite μ τ n two co odd ha hb nt tx ty
  obtain ⟨k,s⟩ := picks (μ x) (μ y) n two odd ha hb nt
  apply cycle_from_at x y (word k) (size_word k) (close_word m x y k)
  intro i j lt E
  let f : Bool×G → Bool×Kˣ×K := fun d => (d.1,μ d.2,τ d.2)
  have U := position_sound μ τ co.2 co.1 x y tx ty k i.val
  have V := position_sound μ τ co.2 co.1 x y tx ty k j.val
  exact s i j lt (U.symm.trans ((congrArg f E).trans V))

/-- Every finite odd-order metabelian group yields a simple dyadic cycle
of length at most 32 in a one-matching bi-Cayley graph. Nilpotence
is not required. -/
theorem finite_odd_metabelian_ribbon {G : Type u} [Group G] [Finite G]
    (h : IsMulCommutative (commutator G)) (x y : G) (odd : Odd (Nat.card G))
    (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨ Ribbon.Cycle x y 32 :=
  all_metabelian certified_affine h x y odd hx hy

end RibbonAffine
#print axioms RibbonAffine.certified_affine
#print axioms RibbonAffine.finite_odd_metabelian_ribbon
