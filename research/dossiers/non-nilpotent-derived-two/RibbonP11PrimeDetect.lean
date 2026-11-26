import RibbonP11ModP
import RibbonP11Cyclic
import Mathlib.Data.Nat.Factors
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace RibbonP11
open RibbonAffine HaarClass4Structure
variable {A : Type*} [CommGroup A] [Finite A]

/-- Cauchy plus finiteness: reducing modulo p-th powers detects every
prime divisor of an abelian group's order. -/
theorem prime_not_pow_surj (p : ℕ) [Fact p.Prime] (hp : p ∣ Nat.card A) :
    ¬Function.Surjective (fun a : A => a^p) := by
  intro h
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p hp
  have inj := Finite.injective_iff_surjective.mpr h
  have E : a^p=(1:A)^p := by simp only [one_pow,←ha,pow_orderOf_eq_one]
  have A1 := inj E
  rw [A1,orderOf_one] at ha
  exact (Fact.out : p.Prime).ne_one ha.symm

theorem prime_mod_nontrivial (p : ℕ) [Fact p.Prime] (hp : p ∣ Nat.card A) :
    Nontrivial (A ⧸ powSub A p) := by
  by_contra! H
  haveI := H
  apply prime_not_pow_surj p hp
  intro a
  have zz : QuotientGroup.mk' (powSub A p) a=1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff _).mp zz

theorem cyclic_of_prime_power_mod_cyclic (p : ℕ) [Fact p.Prime]
    {k : ℕ} (hcard : Nat.card A=p^k) [IsCyclic (A ⧸ powSub A p)] : IsCyclic A := by
  let f := QuotientGroup.mk' (powSub A p)
  obtain ⟨fa,hfa⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (A ⧸ powSub A p))
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (powSub A p) fa
  let H := Subgroup.zpowers a
  let q := QuotientGroup.mk' H
  have powSurj : Function.Surjective (fun a : A ⧸ H => a^p) := by
    intro z
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective H z
    have hb : f b ∈ Subgroup.zpowers fa := hfa ▸ Subgroup.mem_top _
    obtain ⟨i,hi⟩ := Subgroup.mem_zpowers_iff.mp hb
    have E : f (a^i)=f b := by rw [map_zpow]; exact (ha ▸ hi)
    obtain ⟨w,hw,eq⟩ := (QuotientGroup.mk'_eq_mk' (powSub A p)).mp E
    obtain ⟨d,rfl⟩ := hw
    refine ⟨q d,?_⟩
    have hq : q (a^i)=1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers_iff.mpr ⟨i,rfl⟩)
    have HH := congrArg q eq
    change q (a^i * d^p)=q b at HH
    rw [map_mul,map_pow,hq,one_mul] at HH
    exact HH
  have hdiv : Nat.card (A ⧸ H) ∣ p^k := hcard ▸ H.card_quotient_dvd_card
  obtain ⟨j,_,eqj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdiv
  have j0 : j=0 := by
    by_contra! h
    have div : p ∣ Nat.card (A ⧸ H) := by
      rw [eqj]
      exact dvd_pow_self _ h
    exact prime_not_pow_surj p div powSurj
  have hh : Nat.card (A ⧸ H)=1 := by rw [eqj,j0,pow_zero]
  haveI : Subsingleton (A ⧸ H) := Nat.card_eq_one_iff_unique.mp hh |>.1
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨a,top_unique ?_⟩
  intro g _
  exact (QuotientGroup.eq_one_iff _).mp (Subsingleton.elim (q g) 1)

theorem cyclic_of_single_prime (p : ℕ) [Fact p.Prime]
    (only : ∀ q, q.Prime → q ∣ Nat.card A → q=p)
    [IsCyclic (A ⧸ powSub A p)] : IsCyclic A :=
  cyclic_of_prime_power_mod_cyclic p (Nat.eq_prime_pow_of_unique_prime_dvd
    (Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩) (fun h d => only _ h d))

end RibbonP11
#print axioms RibbonP11.prime_mod_nontrivial
#print axioms RibbonP11.cyclic_of_single_prime
