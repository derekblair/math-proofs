import HaarClass4Generate
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import RibbonP3Collect

namespace RibbonP3
open HaarClass4Generate HaarClass4Structure HaarClass4Ports
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem center_of_L2 (nil : LS G 3=⊥) {z : G} (hz : z∈LS G 2) :
    ∀ w, Commute z w := by
  intro w
  apply commutatorElement_eq_one_iff_commute.mp
  have h := next_layer hz w
  rwa [nil,Subgroup.mem_bot] at h

theorem class3_ports (nil : LS G 3=⊥) (x y : G) :
    Class3 x y (portC x y) (portU x y) (portV x y) := by
  have u := center_of_L2 nil (layer_u x y)
  have v := center_of_L2 nil (layer_v x y)
  refine ⟨u,v,ports_xy x y,?_,?_⟩
  · rw [(u (x*portC x y)).symm.eq]
    simp only [portU,commutatorElement_def]
    group
  · rw [(v (y*portC x y)).symm.eq]
    simp only [portV,commutatorElement_def]
    group

theorem L2_eq_two (nil : LS G 3=⊥) (x y : G) (gen : Generates x y) :
    LS G 2 = Subgroup.closure ({portU x y,portV x y} : Set G) := by
  let S := Subgroup.closure ({portU x y,portV x y} : Set G)
  have leS : S ≤ LS G 2 := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact layer_u x y
    · exact layer_v x y
  have Scenter : S ≤ Subgroup.center G := fun z hz =>
    Subgroup.mem_center_iff.mpr (fun w => (center_of_L2 nil (leS hz) w).symm.eq)
  letI : S.Normal := S.normal_of_le_center Scenter
  let f := QuotientGroup.mk' S
  have hu : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure (by simp))
  have hv : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure (by simp))
  have cu : Commute (f (portC x y)) (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [portU,map_commutatorElement] using hu
  have cv : Commute (f (portC x y)) (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [portV,map_commutatorElement] using hv
  have gg := map_gen f (QuotientGroup.mk'_surjective S) gen
  have xy : f x*f y=f y*f x*f (portC x y) := by simpa only [map_mul] using congrArg f (ports_xy x y)
  have z := c_center_class_two _ _ _ gg xy (gen_center _ _ _ gg cu cv)
  have m := map_ls f (QuotientGroup.mk'_surjective S) 2
  rw [z,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at m
  exact le_antisymm m leS

theorem cube_L2 (nil : LS G 3=⊥) (x y : G) (gen : Generates x y)
    (c3 : (portC x y)^3∈LS G 2) (s : LS G 2) : s^3=1 := by
  let c := portC x y
  have ct (w : G) : Commute (c^3) w := center_of_L2 nil c3 w
  have cu (w : G) : ⁅c,w⁆∈LS G 2 := next_layer (layer_c x y) w
  have call (w : G) : ⁅c,w⁆^3=1 := by
    have cW := center_of_L2 nil (cu w) c
    rw [cW.symm.commutatorElement_pow_left 3]
    exact (ct w).commutator_eq
  apply Subtype.ext
  have z : s.val∈Subgroup.closure ({portU x y,portV x y} : Set G) := L2_eq_two nil x y gen ▸ s.property
  have this : ∀ a ∈ Subgroup.closure ({portU x y,portV x y} : Set G), a^3=1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem z hz =>
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact call x
      · exact call y
    | one => simp
    | mul a b ha _ ih jb =>
      have h : Commute a b := center_of_L2 nil ((L2_eq_two nil x y gen).symm ▸ ha) b
      rw [h.mul_pow,ih,jb,mul_one]
    | inv a _ ih => rw [inv_pow,ih,inv_one]
  exact this s.val z

theorem char_exists (nil : LS G 3=⊥) (x y : G) (gen : Generates x y)
    (c3 : (portC x y)^3∈LS G 2) (nz : portU x y≠1) :
    ∃ χ : LS G 2 →* Multiplicative (ZMod 3),
      χ ⟨portU x y,layer_u x y⟩ = Multiplicative.ofAdd (1:ZMod 3) := by
  let S := LS G 2
  letI : CommGroup S := { (inferInstance : Group S) with
    mul_comm := fun a b => Subtype.ext ((center_of_L2 nil a.property b.val).eq) }
  letI : Module (ZMod 3) (Additive S) := AddCommGroup.zmodModule
    (fun s => cube_L2 nil x y gen c3 s)
  let u : Additive S := Additive.ofMul ⟨portU x y,layer_u x y⟩
  have nu : u ≠ 0 := fun e => nz (congrArg Subtype.val e)
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 3) nu
  let χ : S →* Multiplicative (ZMod 3) :=
    { toFun := fun s => Multiplicative.ofAdd (f (Additive.ofMul s))
      map_one' := f.map_zero
      map_mul' := f.map_add }
  exact ⟨χ,hf⟩

end RibbonP3
#print axioms RibbonP3.char_exists
