import RibbonNonNilLift
import RibbonNonNilAffine
import RibbonAffineFinal
import RibbonMetaSharp

namespace RibbonNonNilSharp
open HaarClass4Structure HaarClass4Generate RibbonClass4Fallback RibbonClass3SharpGraph
open scoped commutatorElement
abbrev J := RibbonNonNilAffine.G
abbrev PGroup := H × J
def x : PGroup := (a,RibbonNonNilAffine.a)
def y : PGroup := (b,RibbonNonNilAffine.b)
abbrev Component := Pair x y
local instance : Finite H := Finite.of_equiv _ coord.symm

private theorem nonid_x : x≠1 := by
  intro h
  have hn : a≠1 := by decide +kernel
  exact hn (congrArg Prod.fst h)

private theorem nonid_y : y≠1 := by
  intro h
  have hn : b≠1 := by decide +kernel
  exact hn (congrArg Prod.fst h)

private theorem prod_odd : Odd (Nat.card PGroup) := by
  rw [Nat.card_prod,h_card,RibbonNonNilAffine.cardinality]
  decide

private theorem prod_meta : RibbonMeta.Meta PGroup := by
  intro g hg h hh
  let fl : PGroup →* H := MonoidHom.fst _ _
  let fr : PGroup →* J := MonoidHom.snd _ _
  have el := map_ls fl (fun l => ⟨(l,1),rfl⟩) 1
  have er := map_ls fr (fun r => ⟨(1,r),rfl⟩) 1
  have gl := Subgroup.mem_map_of_mem fl hg
  have hl := Subgroup.mem_map_of_mem fl hh
  have gr := Subgroup.mem_map_of_mem fr hg
  have hr := Subgroup.mem_map_of_mem fr hh
  rw [el] at gl hl
  rw [er] at gr hr
  have R := RibbonNonNilAffine.metabelian ⟨fr g,by rwa [←Subgroup.top_lowerCentralSeries_one]⟩
    ⟨fr h,by rwa [←Subgroup.top_lowerCentralSeries_one]⟩
  exact Prod.ext ((RibbonMeta.meta_of_class_three class_three _ gl _ hl).eq)
    (congrArg Subtype.val R)

def component_right : Component →* J :=
  (MonoidHom.snd H J).comp (Pair x y).subtype

theorem component_surj : Function.Surjective component_right := by
  rintro ⟨u,v⟩
  refine ⟨(rightPort x y)^u.val*(leftPort x y)^v.val,?_⟩
  rw [map_mul,map_pow,map_pow]
  exact RibbonNonNilAffine.normal_form u v

theorem component_not_nil (n : Nat) : LS Component n≠⊥ := by
  intro e
  have a := map_ls component_right component_surj n
  rw [e,Subgroup.map_bot] at a
  exact RibbonNonNilAffine.not_nil n a.symm

theorem component_meta : RibbonMeta.Meta Component := RibbonMeta.subgroup_meta prod_meta (Pair x y)

private theorem commutative_derived : IsMulCommutative (commutator Component) := by
  rw [← Subgroup.top_lowerCentralSeries_one]
  apply isMulCommutative_iff.mpr
  intro a b
  exact Subtype.ext ((component_meta a a.property b b.property).eq)

private def component_left : Component →* H :=
  (MonoidHom.fst H J).comp (Pair x y).subtype

theorem no_small :
  ¬ Ribbon.Cycle (leftPort x y) (rightPort x y) 4 ∧
  ¬ Ribbon.Cycle (leftPort x y) (rightPort x y) 8 ∧
  ¬ Ribbon.Cycle (leftPort x y) (rightPort x y) 16 :=
  ⟨excluded_lift component_left _ _ rfl rfl 2 (by decide) checked2,
   excluded_lift component_left _ _ rfl rfl 4 (by decide) checked4,
   excluded_lift component_left _ _ rfl rfl 8 (by decide) checked8⟩

theorem component_odd : Odd (Nat.card Component) :=
  Odd.of_dvd_nat prod_odd ((Pair x y).card_subgroup_dvd_card)

theorem sharp :
    ¬ Ribbon.Cycle (leftPort x y) (rightPort x y) 4 ∧
    ¬ Ribbon.Cycle (leftPort x y) (rightPort x y) 8 ∧
    ¬ Ribbon.Cycle (leftPort x y) (rightPort x y) 16 ∧
    Ribbon.Cycle (leftPort x y) (rightPort x y) 32 := by
  refine ⟨no_small.1,no_small.2.1,no_small.2.2,?_⟩
  have hx : leftPort x y ≠ 1 := fun e => nonid_x (congrArg (fun a : Component => (a : PGroup)) e)
  have hy : rightPort x y ≠ 1 := fun e => nonid_y (congrArg (fun a : Component => (a : PGroup)) e)
  rcases RibbonAffine.finite_odd_metabelian_ribbon (G:=Component) commutative_derived
      (leftPort x y) (rightPort x y) component_odd hx hy with h|h|h|h
  · exact (no_small.1 h).elim
  · exact (no_small.2.1 h).elim
  · exact (no_small.2.2 h).elim
  · exact h

end RibbonNonNilSharp
#print axioms RibbonNonNilSharp.component_not_nil
#print axioms RibbonNonNilSharp.sharp
