import Ribbon8Algebra
import Ribbon8Graph
import Ribbon8SmallFamily

namespace RibbonDerived3
open HaarUniversal36 HaarClass4Structure HaarClass4Ports Ribbon5Bridge
open scoped commutatorElement
variable {G : Type*} [Group G]

abbrev Derived (G : Type*) [Group G] : Subgroup G := L G 1
abbrev DLS (G : Type*) [Group G] (i : Nat) := (Derived G).lowerCentralSeries i

theorem residue_in_D2 (x y : G) : Ribbon6.residue x y ∈ DLS G 1 := by
  have d (a b : G) : ⁅a,b⁆ ∈ Derived G := Subgroup.commutator_mem_commutator
    (Subgroup.mem_top a) (Subgroup.mem_top b)
  have H : x⁻¹ * ⁅y,x^2⁆ * x ∈ Derived G := by
    simpa only [inv_inv] using (inferInstance : (Derived G).Normal).conj_mem _ (d y _) x⁻¹
  have J : ⁅⁅x,y⁻¹⁆,x⁻¹ * ⁅y,x^2⁆ * x⁆ ∈ DLS G 1 := by
    change _ ∈ ⁅Derived G,Derived G⁆
    exact Subgroup.commutator_mem_commutator (d x y⁻¹) H
  rw [Ribbon6.explicit]
  exact (inferInstance : (DLS G 1).Normal).conj_mem _ J _

theorem comm_of_residue (dnil : DLS G 3=⊥) {u r z : G}
    (U : u ∈ Derived G) (R : r ∈ DLS G 1) (Z : z = u⁻¹ * ⁅u,r⁆ * u) :
    Commute z u := by
  have comm : ⁅u,r⁆ ∈ DLS G 2 := by
    rw [←commutatorElement_inv]
    exact (DLS G 2).inv_mem (Subgroup.commutator_mem_commutator R U)
  have hz : z ∈ DLS G 2 := by
    rw [Z]
    simpa only [inv_inv] using (inferInstance : (DLS G 2).Normal).conj_mem _ comm u⁻¹
  apply commutatorElement_eq_one_iff_commute.mp
  exact Subgroup.mem_bot.mp (dnil ▸ Subgroup.commutator_mem_commutator hz U :
    ⁅z,u⁆ ∈ (⊥ : Subgroup G))

theorem commute (dnil : DLS G 3=⊥) (x y : G) : Commute (Ribbon8.Z x y) (Ribbon8.U x y) := by
  refine comm_of_residue dnil (Ribbon8.u_layer x y) ?_ (Ribbon8.z_conjugate x y)
  rw [Ribbon8.r_conjugate]
  exact (inferInstance : (DLS G 1).Normal).conj_mem _ (residue_in_D2 x y⁻¹) _

theorem variant_commute (dnil : DLS G 3=⊥) (k : Fin 3) (x y : G) :
    Commute (Ribbon8Small.Z k x y) (Ribbon8Small.U k x y) := by
  fin_cases k
  · refine comm_of_residue dnil (Ribbon8AltA.u_layer x y) ?_ (Ribbon8AltA.z_conjugate x y)
    rw [Ribbon8AltA.r_conjugate]
    exact (inferInstance : (DLS G 1).Normal).conj_mem _ (residue_in_D2 y x⁻¹) _
  · refine comm_of_residue dnil (Ribbon8AltB.u_layer x y) ?_ (Ribbon8AltB.z_conjugate x y)
    rw [Ribbon8AltB.r_conjugate]
    exact (inferInstance : (DLS G 1).Normal).conj_mem _ (residue_in_D2 y⁻¹ x) _
  · refine comm_of_residue dnil (Ribbon8AltC.u_layer x y) ?_ (Ribbon8AltC.z_conjugate x y)
    rw [Ribbon8AltC.r_conjugate]
    exact (inferInstance : (DLS G 1).Normal).conj_mem _ ((DLS G 1).inv_mem (residue_in_D2 y x)) _

theorem variant_close (dnil : DLS G 3=⊥) (k : Fin 3) (x y : G) :
    pathAt x y (Ribbon8Small.word k) 128=pathAt x y (Ribbon8Small.word k) 0 := by
  have C := variant_commute dnil k x y
  rw [Ribbon8Small.actual_word]
  fin_cases k
  · change Commute (Ribbon8AltA.Z x y) (Ribbon8AltA.U x y) at C
    change pathAt x y Ribbon8AltA.wt 128 = pathAt x y Ribbon8AltA.wt 0
    rw [Ribbon8AltA.t_end,C.inv_right.eq,mul_inv_cancel_right,inv_mul_cancel]
    rfl
  · change Commute (Ribbon8AltB.Z x y) (Ribbon8AltB.U x y) at C
    change pathAt x y Ribbon8AltB.wt 128 = pathAt x y Ribbon8AltB.wt 0
    rw [Ribbon8AltB.t_end,C.inv_right.eq,mul_inv_cancel_right,inv_mul_cancel]
    rfl
  · change Commute (Ribbon8AltC.Z x y) (Ribbon8AltC.U x y) at C
    change pathAt x y Ribbon8AltC.wt 128 = pathAt x y Ribbon8AltC.wt 0
    rw [Ribbon8AltC.t_end,C.inv_right.eq,mul_inv_cancel_right,inv_mul_cancel]
    rfl

theorem local_bound (dnil : DLS G 3=⊥) (x y : G)
    (good : ∀ k : Nat, 1≤k → k≤7 → (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  have C := commute dnil x y
  apply Ribbon8.cases_of_good x y good C
  intro nz eq
  have H : Commute (Ribbon8.U x y) (Ribbon8.R x y) := eq.symm ▸ C.symm
  apply nz
  rw [Ribbon8.z_conjugate,H.commutator_eq,mul_one,inv_mul_cancel]

end RibbonDerived3
#print axioms RibbonDerived3.local_bound
#print axioms RibbonDerived3.variant_close
