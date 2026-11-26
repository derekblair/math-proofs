import RibbonStationaryWords

namespace RibbonStationaryThird
open scoped commutatorElement
open RibbonDerived3 HaarClass4Structure
variable {G : Type*} [Group G]

/-- In a group with class-two derived group, if the third lower-central group
is contained in the second derived group, conjugation is trivial on the second derived group. -/
theorem second_derived_central
    (d : RibbonDerivedTwo.D2 G) (h : LS G 2 ≤ DLS G 1) :
    DLS G 1 ≤ Subgroup.center G := by
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  apply Subgroup.mem_center_iff.mpr
  intro g
  have zz (v : G) (hv : v ∈ LS G 1) : ⁅g,v⁆∈DLS G 1 := by
    have hc : ⁅v,g⁆∈LS G 2 :=
      Subgroup.commutator_mem_commutator hv (Subgroup.mem_top g)
    rw [←commutatorElement_inv]
    exact (DLS G 1).inv_mem (h hc)
  let z := ⁅g,a⁆
  let w := ⁅g,b⁆
  have cz (v : G) (hv : v∈LS G 1) : Commute z v :=
    RibbonStationaryWords.central d (zz a ha) hv
  have cw (v : G) (hv : v∈LS G 1) : Commute w v :=
    RibbonStationaryWords.central d (zz b hb) hv
  have wa : w∈LS G 1 := Subgroup.commutator_le_self (LS G 1) (zz b hb)
  have wb : z∈LS G 1 := Subgroup.commutator_le_self (LS G 1) (zz a ha)
  have ga : g*a*g⁻¹=z*a := by simp only [z,commutatorElement_def]; group
  have gb : g*b*g⁻¹=w*b := by simp only [w,commutatorElement_def]; group
  have commutes {v A B : G} (hA : Commute v A) (hB : Commute v B) : Commute v ⁅A,B⁆ := by
    rw [commutatorElement_def]
    exact ((hA.mul_right hB).mul_right hA.inv_right).mul_right hB.inv_right
  have right : ⁅a,w*b⁆=⁅a,b⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,(cw _ ha).symm.commutator_eq,
      one_mul,(commutes (cw _ ha) (cw _ hb)).eq,
      mul_assoc,mul_inv_cancel,mul_one]
  have lc : Commute z (w*b) := (cz _ wa).mul_right (cz _ hb)
  have lz : Commute z ⁅a,w*b⁆ := commutes (cz _ ha) lc
  have C : g*⁅a,b⁆*g⁻¹=⁅a,b⁆ := by
    rw [conjugate_commutatorElement,ga,gb,commutatorElement_mul_left_eq_conj_mul,
      lc.commutator_eq,mul_one,lz.eq,mul_assoc,mul_inv_cancel,mul_one,right]
  calc
    _ = (g*⁅a,b⁆*g⁻¹)*g := by group
    _ = _ := by rw [C]

/-- A stable, nontrivial third lower-central group must already be visible
in the abelianization of the class-two derived subgroup. -/
theorem stable_third_not_in_second_derived
    (d : RibbonDerivedTwo.D2 G) (stable : LS G 2 = LS G 3) (nz : LS G 2≠⊥) :
    ¬LS G 2≤DLS G 1 := by
  intro h
  have H := h.trans (second_derived_central d h)
  have eq : LS G 3=⊥ := by
    apply le_bot_iff.mp
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    exact Subgroup.mem_bot.mpr (Subgroup.mem_center_iff.mp (H ha) b |>.symm |> commutatorElement_eq_one_iff_commute.mpr)
  exact nz (stable.trans eq)

end RibbonStationaryThird
#print axioms RibbonStationaryThird.stable_third_not_in_second_derived
