import RibbonDumbbellLift
import RibbonIA
import RibbonDerived3Algebra

namespace RibbonDumbbell
open Ribbon5Bridge
variable {G Q : Type*} [Group G] [Group Q]

@[simp] theorem rho10 (r s : G) : rho r s ((1,0):Z) = r := by
  change r^(1:Int)*s^(0:Int)=r
  rw [zpow_one,zpow_zero,mul_one]
@[simp] theorem rho01 (r s : G) : rho r s ((0,1):Z) = s := by
  change r^(0:Int)*s^(1:Int)=s
  rw [zpow_zero,zpow_one,one_mul]
@[simp] theorem rho11 (r s : G) : rho r s ((1,1):Z) = r*s := by
  change r^(1:Int)*s^(1:Int)=r*s
  rw [zpow_one,zpow_one]

private theorem full_levels (r s : G) (R : r ≠ 1) (S : s ≠ 1)
    (sep : s ≠ r) (inv : s ≠ r⁻¹) :
    ∀ a ∈ allowed 0, ∀ b ∈ allowed 0, rho r s a = rho r s b → a=b := by
  have P : r*s ≠ 1 := fun e => inv (eq_inv_of_mul_eq_one_right e)
  have RS : r ≠ s := Ne.symm sep
  have RP : r*s ≠ r := by
    intro E
    apply S
    apply mul_left_cancel (a:=r)
    simpa only [mul_one] using E
  have SP : r*s ≠ s := by
    intro E
    apply R
    apply mul_right_cancel (b:=s)
    simpa only [one_mul] using E
  intro a aH b bH e
  change a ∈ [0,(1,0),(0,1),(1,1)] at aH
  change b ∈ [0,(1,0),(0,1),(1,1)] at bH
  simp only [List.mem_cons,List.not_mem_nil,or_false] at aH bH
  rcases aH with rfl|rfl|rfl|rfl <;> rcases bH with rfl|rfl|rfl|rfl
  all_goals try rfl
  all_goals simp only [rho_zero,rho10,rho01,rho11] at e
  all_goals first
    | exact (R e).elim
    | exact (R e.symm).elim
    | exact (S e).elim
    | exact (S e.symm).elim
    | exact (P e).elim
    | exact (P e.symm).elim
    | exact (RS e).elim
    | exact (RS e.symm).elim
    | exact (RP e).elim
    | exact (RP e.symm).elim
    | exact (SP e).elim
    | exact (SP e.symm).elim

private theorem line_levels (r s : G) (R : r ≠ 1) :
    ∀ a ∈ ([0,(1,0)] : List Z), ∀ b ∈ ([0,(1,0)] : List Z),
      rho r s a = rho r s b → a=b := by
  intro a aH b bH e
  simp only [List.mem_cons,List.not_mem_nil,or_false] at aH bH
  rcases aH with rfl|rfl <;> rcases bH with rfl|rfl
  all_goals try rfl
  all_goals simp only [rho_zero,rho10] at e
  all_goals first | exact (R e).elim | exact (R e.symm).elim

private theorem loop_A {X : Type*} (x y s : G) (v : Tag → Bool × G) (π : Bool × G → X)
    (vm : Function.Injective (π ∘ v)) (D : Forward x y 1 s v) :
    Ribbon.Cycle x y 32 := by
  refine ⟨fun i => v (aTag i),?_,?_⟩
  · intro i j E
    have h := vm (congrArg π E)
    exact Fin.ext (congrArg (Fin.val : Tag → Nat) h)
  · intro i
    have k := D.a i
    change Ribbon.Adj x y (v (aTag i)) (shift (if i.val == 31 then 1 else 1)
      (v (aTag (dot (i.val+1))))) at k
    change Ribbon.Adj x y (v (aTag i)) (v (aTag (dot (i.val+1))))
    simpa [shift] using k

private theorem loop_B {X : Type*} (x y r : G) (v : Tag → Bool × G) (π : Bool × G → X)
    (vm : Function.Injective (π ∘ v)) (D : Forward x y r 1 v) :
    Ribbon.Cycle x y 32 := by
  refine ⟨fun i => v (bTag i),?_,?_⟩
  · intro i j E
    have h := vm (congrArg π E)
    apply Fin.ext
    have H := congrArg Fin.val h
    change 32+i.val=32+j.val at H
    omega
  · intro i
    have k := D.b i
    change Ribbon.Adj x y (v (bTag i)) (shift (if i.val == 31 then 1 else 1)
      (v (bTag (dot (i.val+1))))) at k
    change Ribbon.Adj x y (v (bTag i)) (v (bTag (dot (i.val+1))))
    simpa [shift] using k

/-- A pair of projected 32-cycles and a disjoint projected connecting 32-path.
Only the projections of the 95 base positions must be distinct. Gains are
left displacements at the two loops, and are assumed to commute. -/
theorem commuting_gains_project {X : Type*} (x y r s : G) (comm : Commute r s)
    (π : Bool × G → X)
    (inv : ∀ (a : Z) (q : Bool × G), π (shift (rho r s a) q) = π q)
    (v : Tag → Bool × G) (vm : Function.Injective (π ∘ v)) (D : Forward x y r s v) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 128 ∨ Ribbon.Cycle x y 256 := by
  by_cases R : r=1
  · left; exact loop_A x y s v π vm (by simpa [R] using D)
  by_cases S : s=1
  · left; exact loop_B x y r v π vm (by simpa [S] using D)
  by_cases I : s=r⁻¹
  · right; left
    have a : rho r s (shiftA 1) = r := by simp [rho,shiftA]
    have b : rho r s (shiftB 1) = s := by simp [rho,shiftB,I]
    exact lift_mode_project x y r s comm π inv v vm 1 (line_levels r s R)
      (all_arcs x y r s comm v D _ _ a b)
  by_cases E : s=r
  · right; left
    have a : rho r s (shiftA 2) = r := by simp [rho,shiftA]
    have b : rho r s (shiftB 2) = s := by simp [rho,shiftB,E]
    exact lift_mode_project x y r s comm π inv v vm 2 (line_levels r s R)
      (all_arcs x y r s comm v D _ _ a b)
  · right; right
    have a : rho r s (shiftA 0) = r := by simp [rho,shiftA]
    have b : rho r s (shiftB 0) = s := by simp [rho,shiftB]
    exact lift_mode_project x y r s comm π inv v vm 0 (full_levels r s R S E I)
      (all_arcs x y r s comm v D _ _ a b)

theorem commuting_gains (x y r s : G) (comm : Commute r s) (f : G →* Q)
    (fr : f r=1) (fs : f s=1) (v : Tag → Bool × G)
    (vm : Function.Injective (project f ∘ v)) (D : Forward x y r s v) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 128 ∨ Ribbon.Cycle x y 256 :=
  commuting_gains_project x y r s comm (project f) (project_shift f fr fs) v vm D

open scoped commutatorElement in
theorem d3_gains_commute (h : RibbonDerived3.DLS G 3 = ⊥)
    {r s : G} (hr : r ∈ RibbonDerived3.DLS G 1) (hs : s ∈ RibbonDerived3.DLS G 1) :
    Commute r s := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h0 := RibbonIA.weight_pair (RibbonDerived3.Derived G) 1 1
    (Subgroup.commutator_mem_commutator hr hs)
  change ⁅r,s⁆ ∈ RibbonDerived3.DLS G 3 at h0
  rw [h] at h0
  exact Subgroup.mem_bot.mp h0

theorem derived_three (x y r s : G) (h : RibbonDerived3.DLS G 3 = ⊥)
    (hr : r ∈ RibbonDerived3.DLS G 1) (hs : s ∈ RibbonDerived3.DLS G 1)
    (f : G →* Q) (fr : f r=1) (fs : f s=1) (v : Tag → Bool × G)
    (vm : Function.Injective (project f ∘ v)) (D : Forward x y r s v) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 128 ∨ Ribbon.Cycle x y 256 :=
  commuting_gains x y r s (d3_gains_commute h hr hs) f fr fs v vm D

theorem derived_three_project {X : Type*} (x y r s : G) (h : RibbonDerived3.DLS G 3 = ⊥)
    (hr : r ∈ RibbonDerived3.DLS G 1) (hs : s ∈ RibbonDerived3.DLS G 1)
    (π : Bool × G → X)
    (inv : ∀ (a : Z) (q : Bool × G), π (shift (rho r s a) q) = π q)
    (v : Tag → Bool × G) (vm : Function.Injective (π ∘ v)) (D : Forward x y r s v) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 128 ∨ Ribbon.Cycle x y 256 :=
  commuting_gains_project x y r s (d3_gains_commute h hr hs) π inv v vm D

#print axioms derived_three_project
#print axioms derived_three
end RibbonDumbbell
