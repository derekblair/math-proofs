import RibbonClass4Graph
import HaarClass4Ports
import Mathlib.GroupTheory.OrderOfElement

namespace RibbonClass4

open HaarClass4Table HaarClass4Normal HaarClass4Projection HaarClass4CollectCore
open HaarClass4Ports HaarClass4Structure RibbonClass4Data
open scoped commutatorElement
variable {G : Type*} [Group G]

def proj (G : Type*) [Group G] := QuotientGroup.mk' (LS G 2)

theorem kills (nil : LS G 4=⊥) (x y : G) :
    KillsMid (make nil x y) (proj G) := by
  have D := tail_layers nil x y
  have z : LS G 3 ≤ LS G 2 :=
    Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (by decide)
  exact ⟨⟨(QuotientGroup.eq_one_iff _).mpr (z D.1),
    (QuotientGroup.eq_one_iff _).mpr (z D.2.1),
    (QuotientGroup.eq_one_iff _).mpr (z D.2.2)⟩,
    (QuotientGroup.eq_one_iff _).mpr (layer_u x y),
    (QuotientGroup.eq_one_iff _).mpr (layer_v x y)⟩

private theorem power_u_central (nil : LS G 4=⊥) (c u a x : G) (n : Nat)
    (hc : c^n ∈ LS G 2) (cu : Commute c u) (ca : Central a)
    (r : c*x=x*c*(u*a)) : Central (u^n) := by
  let q := ⁅c^n,x⁆
  have c_q : Central q := center_in_layer4 nil (next_layer hc x)
  have e : c^n*x = x*c^n*q := by
    calc
      _ = q*(x*c^n) := by simp only [q,commutatorElement_def]; group
      _ = _ := (c_q (x*c^n)).eq
  have h := HaarCycle.shift c x (u*a) (cu.symm.mul_left (ca c)) r (n:ℤ)
  simp only [zpow_natCast] at h
  have H : (u*a)^n=q := mul_left_cancel (h.symm.trans e)
  have D : u^n = q*(a^n)⁻¹ := by
    rw [(ca u).symm.mul_pow] at H
    calc
      _ = (u^n*a^n)*(a^n)⁻¹ := by group
      _ = _ := by rw [H]
  intro g
  rw [D]
  exact (c_q g).mul_left ((ca g).pow_left n).inv_left

private theorem power_corr_eq_one (u x a : G) (n : Nat) (ca : Central a)
    (rel : u*x=x*u*a) (U : Central (u^n)) : a^n=1 := by
  have h := HaarCycle.shift u x a (ca u) rel (n:ℤ)
  simp only [zpow_natCast] at h
  exact mul_left_cancel (h.symm.trans (by rw [(U x).eq,mul_one]))

theorem target_power_from_proj (nil : LS G 4=⊥) (x y : G) (sel : Fin 3) (n : ℕ)
    (h : (proj G (portC x y))^n=1) : (target (make nil x y) sel)^n=1 := by
  let M := make nil x y
  have hc : M.c^n∈LS G 2 := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (proj G) ((portC x y)^n)=1
    rw [map_pow]
    exact h
  have U := power_u_central nil M.c M.u M.a M.x n hc M.hcu M.ca M.cx
  have V := power_u_central nil M.c M.v M.d M.y n hc M.hcv M.cd M.cy
  fin_cases sel
  · exact power_corr_eq_one M.u M.x M.a n M.ca M.ux U
  · exact power_corr_eq_one M.u M.y M.b n M.cb M.uy U
  · exact power_corr_eq_one M.v M.y M.d n M.cd M.vy V

theorem cycle64_of_fourth (nil : LS G 4=⊥) (x y : G) (sel : Fin 3)
    (fourth : rootGood (target (make nil x y) sel)) : Ribbon.Cycle x y 64 := by
  have hC : rootGood (proj G (portC x y)) := by
    refine ⟨?_,?_,?_⟩
    · intro E
      exact fourth.1 (by simpa using target_power_from_proj nil x y sel 1 (by simpa only [pow_one] using E))
    · exact fun E => fourth.2.1 (target_power_from_proj nil x y sel 2 E)
    · exact fun E => fourth.2.2 (target_power_from_proj nil x y sel 3 E)
  exact cycle64 (make nil x y) (proj G) (kills nil x y) hC sel fourth.1

theorem root_good_card (odd : Odd (Nat.card G)) (no3 : ¬ 3∣Nat.card G)
    {g : G} (hg : g≠1) : rootGood g := by
  have p3 : g^3≠1 := by
    intro H
    have div : orderOf g∣3 := orderOf_dvd_iff_pow_eq_one.mpr H
    have L : orderOf g ≤ 3 := Nat.le_of_dvd (by decide) div
    have X : orderOf g ≠ 1 := fun eq => hg (orderOf_eq_one_iff.mp eq)
    have E : orderOf g=3 := by
      interval_cases K : orderOf g <;> simp_all
    have R := orderOf_dvd_natCard g
    exact no3 (by simpa [E] using R)
  exact ⟨hg,HaarClass3Odd.odd_no_involution odd hg,p3⟩

theorem cycle64_of_fourth_no3 (nil : LS G 4=⊥) (odd : Odd (Nat.card G))
    (no3 : ¬ 3∣Nat.card G) (x y : G) (sel : Fin 3) (fourth : target (make nil x y) sel≠1) :
    Ribbon.Cycle x y 64 :=
  cycle64_of_fourth nil x y sel (root_good_card odd no3 fourth)

end RibbonClass4
#print axioms RibbonClass4.cycle64_of_fourth
#print axioms RibbonClass4.cycle64_of_fourth_no3
