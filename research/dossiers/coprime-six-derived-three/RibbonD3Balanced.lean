import RibbonD3ClosureMembership

namespace RibbonD3ClosureMembership
open RibbonD3MateData RibbonD3MateUse RibbonD3Grid RibbonD3SignedEval
open RibbonD3PortEval RibbonDerived3 HaarClass4Structure Ribbon5Bridge
variable {G : Type*} [Group G]

theorem eval_exponents {H : Type*} [CommGroup H] (x y : H) (w : List Int)
    (hw : ∀ a ∈ w, legal a) :
    eval (letter x y) w = x^(axisExponent 1 w) * y^(axisExponent 2 w) := by
  induction w with
  | nil => simp [axisExponent,eval]
  | cons a w ih =>
    have ha := hw a (by simp)
    have ht : ∀ v ∈ w, legal v := fun v hv => hw v (List.mem_cons_of_mem _ hv)
    rw [eval,ih ht]
    rcases ha with e|e|e|e <;> subst a <;>
      simp [letter,axisExponent,List.count_cons,zpow_add,zpow_sub,
        add_sub_assoc,show ∀ a b : Int, a - (b+1) = a-b-1 by omega] <;> group <;> simp [sub_eq_add_neg,zpow_add,mul_left_comm,mul_assoc,mul_comm]

theorem map_letter {H : Type*} [Group H] (f : G →* H) (x y : G) (a : Int) :
    f (letter x y a) = letter (f x) (f y) a := by
  unfold letter
  split_ifs <;> simp [map_zpow,map_inv]

theorem map_eval {H : Type*} [Group H] (f : G →* H) (x y : G) (w : List Int) :
    f (eval (letter x y) w) = eval (letter (f x) (f y)) w := by
  induction w with
  | nil => simp [eval]
  | cons a w ih => simp [eval,map_letter,ih]

theorem of_balanced (x y : G) (w : List Int) (hw : ∀ a ∈ w, legal a)
    (e1 : axisExponent 1 w = 0) (e2 : axisExponent 2 w = 0) :
    eval (letter x y) w ∈ Derived G := by
  change _ ∈ (⊤ : Subgroup G).lowerCentralSeries 1
  rw [Subgroup.top_lowerCentralSeries_one]
  apply (QuotientGroup.eq_one_iff (N:=commutator G) _).mp
  let f : G →* Abelianization G := Abelianization.of
  change f (eval (letter x y) w) = 1
  rw [map_eval,eval_exponents _ _ _ hw,e1,e2,zpow_zero,zpow_zero,mul_one]

private def checkU (C : Chart) : Bool :=
  axisExponent 1 (letters C C.rotation) == 0 &&
  axisExponent 2 (letters C C.rotation) == 0
private theorem checkU_all : charts.all checkU = true := by decide +kernel

theorem U_mem_derived (x y : G) (i : Fin charts.size) :
    eval (letter x y) (letters charts[i] (charts[i]).rotation) ∈ Derived G := by
  have c := Array.all_eq_true.mp checkU_all i.val i.isLt
  simp only [checkU,Bool.and_eq_true_iff,beq_iff_eq] at c
  exact of_balanced x y _ (legal_erase _ _) c.1 c.2

#print axioms U_mem_derived
end RibbonD3ClosureMembership
