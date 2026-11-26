import HaarClass4Generate
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace RibbonAffine
open HaarClass4Structure HaarClass4Generate HaarClass4Ports
open scoped commutatorElement
variable {G K : Type*} [Group G] [Field K]

abbrev D (G : Type*) [Group G] := LS G 1

theorem normalClosure_c (x y : G) (gen : Generates x y) :
    Subgroup.normalClosure ({portC x y} : Set G) = D G := by
  let N := Subgroup.normalClosure ({portC x y} : Set G)
  have hc : portC x y∈N := Subgroup.subset_normalClosure (by simp)
  have le : N ≤ D G :=
    Subgroup.normalClosure_le_normal (by simpa using layer_c x y)
  let f := QuotientGroup.mk' N
  have fc : f (portC x y)=1 := (QuotientGroup.eq_one_iff _).mpr hc
  have xy : Commute (f x) (f y) := by
    change f x*f y=f y*f x
    simpa only [map_mul,fc,mul_one] using congrArg f (ports_xy x y)
  let : IsMulCommutative (G ⧸ N) := gen_comm _ _ (map_gen f (QuotientGroup.mk'_surjective _) gen) xy
  have zz : LS (G ⧸ N) 1=⊥ :=
    Subgroup.top_lowerCentralSeries_one.trans (commutator_eq_bot _)
  have m := map_ls f (QuotientGroup.mk'_surjective _) 1
  rw [zz,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at m
  exact le_antisymm le m

theorem survives_in_normal_quotient (x y : G) (gen : Generates x y)
    (N : Subgroup G) [N.Normal] (hN : N < D G) :
    portC x y ∉ N := by
  intro h
  have H : Subgroup.normalClosure ({portC x y} : Set G) ≤ N :=
    Subgroup.normalClosure_le_normal (by simpa using h)
  rw [normalClosure_c x y gen] at H
  exact (not_le_of_gt hN) H

def cAt (g s : G) : D G :=
  ⟨⁅g,s⁆,next_layer (Subgroup.mem_top g) s⟩

def displacement (ell : D G →* Multiplicative K) (s g : G) : K :=
  Multiplicative.toAdd (ell (cAt g s))

def Equivariant (μ : G →* Kˣ) (ell : D G →* Multiplicative K) : Prop :=
  ∀ (g : G) (d : D G),
    Multiplicative.toAdd (ell (MulAut.conjNormal g d)) =
      (μ g : K) * Multiplicative.toAdd (ell d)

theorem displacement_mul (μ : G →* Kˣ) (ell : D G →* Multiplicative K)
    (e : Equivariant μ ell) (s g h : G) :
    displacement ell s (g*h) = displacement ell s g + (μ g : K) * displacement ell s h := by
  have E : cAt (g*h) s = MulAut.conjNormal g (cAt h s) * cAt g s := by
    apply Subtype.ext
    simpa only [cAt,MulAut.conjNormal_apply,Subgroup.coe_mul] using
      commutatorElement_mul_left_eq_conj_mul g h s
  unfold displacement
  rw [E,map_mul]
  change Multiplicative.toAdd (ell (MulAut.conjNormal g (cAt h s))) +
    Multiplicative.toAdd (ell (cAt g s)) = _
  rw [e,add_comm]

theorem displacement_derived (μ : G →* Kˣ) (ell : D G →* Multiplicative K)
    (e : Equivariant μ ell) (s : G) (d : D G) :
    displacement ell s d.val = (1 - (μ s : K))*Multiplicative.toAdd (ell d) := by
  have E : cAt d.val s = d * (MulAut.conjNormal s d)⁻¹ := by
    apply Subtype.ext
    simpa only [cAt,MulAut.conjNormal_apply,Subgroup.coe_mul,Subgroup.coe_inv] using
      (show ⁅d.val,s⁆ = d.val*(s*d.val*s⁻¹)⁻¹ by rw [commutatorElement_def]; group)
  unfold displacement
  rw [E,map_mul,map_inv]
  change Multiplicative.toAdd (ell d) + -(Multiplicative.toAdd (ell (MulAut.conjNormal s d))) = _
  rw [e]
  ring

theorem displacement_detects (μ : G →* Kˣ) (ell : D G →* Multiplicative K)
    (e : Equivariant μ ell) (s : G) (h : μ s≠1) (d : D G) (hd : ell d≠1) :
    displacement ell s d.val≠0 := by
  rw [displacement_derived μ ell e]
  apply mul_ne_zero
  · intro H
    apply h
    apply Units.ext
    exact (sub_eq_zero.mp H).symm
  · exact hd

theorem order_odd [Finite G] (odd : Odd (Nat.card G)) (μ : G →* Kˣ) (g : G) :
    Odd (orderOf (μ g)) :=
  Odd.of_dvd_nat odd (dvd_trans (orderOf_map_dvd μ g) (orderOf_dvd_natCard g))

end RibbonAffine
#print axioms RibbonAffine.normalClosure_c
#print axioms RibbonAffine.displacement_detects
