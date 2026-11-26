import HaarClass4Prime
import Mathlib.GroupTheory.Nilpotent

namespace HaarClass4Structure

open scoped commutatorElement

variable {G : Type*} [Group G]

abbrev LS (G : Type*) [Group G] (n : ℕ) := (⊤ : Subgroup G).lowerCentralSeries n

theorem layer4_center (h : LS G 4=⊥) : LS G 3 ≤ Subgroup.center G := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  exact h

theorem layer2_layer3 (h : LS G 4=⊥) : ⁅LS G 1,LS G 2⁆=⊥ := by
  change ⁅⁅(⊤ : Subgroup G),⊤⁆,LS G 2⁆ = ⊥
  apply Subgroup.commutator_commutator_eq_bot_of_rotate
  · rw [Subgroup.commutator_comm (⊤ : Subgroup G) (LS G 2)]
    exact h
  · exact h

theorem comm_of_layers (h : LS G 4=⊥) {a b : G} (ha : a∈LS G 1) (hb : b∈LS G 2) :
    Commute a b := by
  have e : ⁅a,b⁆ ∈ ⁅LS G 1,LS G 2⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [layer2_layer3 h,Subgroup.mem_bot] at e
  exact commutatorElement_eq_one_iff_commute.mp e

theorem layer3_comm (h : LS G 4=⊥) {a b : G} (ha : a∈LS G 2) (hb : b∈LS G 2) :
    Commute a b :=
  comm_of_layers h ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 1 ≤ 2) ha) hb

theorem center_in_layer4 (h : LS G 4=⊥) {a : G} (ha : a∈LS G 3) :
    HaarClass4CollectCore.Central a :=
  fun g => (Subgroup.mem_center_iff.mp (layer4_center h ha) g).symm

end HaarClass4Structure

#print axioms HaarClass4Structure.comm_of_layers
