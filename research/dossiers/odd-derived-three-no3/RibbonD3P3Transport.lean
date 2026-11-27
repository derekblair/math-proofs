import RibbonD3P3Numeric

namespace RibbonD3P3
open RibbonDumbbell Ribbon5Bridge
variable {G H : Type*} [Group G] [Group H]

def evalPair (x y c u v : H) (r : Row) : Bool × H :=
  (r.rim,RibbonP3.eval x y c u v r)

theorem eval_zero (x y c u v : H) : evalPair x y c u v RibbonP3.zeroRow = (false,1) := by
  simp only [evalPair,RibbonP3.zeroRow,RibbonP3.eval,HaarClass3Collect.norm,
    RibbonP3.coord,zpow_zero,one_mul]

theorem row_action (x y c u v : H) (d : RibbonP3.Class3 x y c u v) (r : Row)
    (S : RibbonP3.Range r.i) (p : P) :
    evalPair x y c u v (RibbonP3.march r p) = action x y (evalPair x y c u v r) p := by
  have h := RibbonP3.eval_march d r p (RibbonP3.x_word_to_y d r.i S)
  apply Prod.ext
  · cases e : r.rim <;> fin_cases p <;> simp [evalPair,action,RibbonP3.march,e]
  · cases e : r.rim <;> fin_cases p <;> simpa [evalPair,action,RibbonP3.trace,e] using h

theorem atWord_next (x y : H) (z : Bool × H) (w : Array P) (i : Nat) (h : i<w.size) :
    atWord x y z w (i+1) = action x y (atWord x y z w i) w[i]! := by
  have hh : i < w.toList.length := by simpa using h
  unfold atWord
  rw [List.take_succ_eq_append_getElem hh,run_append]
  simp [run,getElem!_pos w i h,Array.getElem_toList]

theorem table_follow (x y c u v : H) (d : RibbonP3.Class3 x y c u v)
    (T : Array Row) (w : Array P) (B : TableOK T w) (nW : w.size=32) (i : Nat) (h : i≤32) :
    atWord x y (evalPair x y c u v (atRow T 0)) w i = evalPair x y c u v (atRow T i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have small : i<32 := by omega
    rw [atWord_next _ _ _ _ i (by simpa [nW] using small),ih (by omega)]
    rw [←B.1 ⟨i,small⟩]
    exact (row_action x y c u v d _ (B.2 ⟨i,by omega⟩) _).symm

theorem point_collect (x y c u v : H) (d : RibbonP3.Class3 x y c u v) (q t : Fin 3)
    (i : Tag) : wordPoint x y (false,1) (spec q t).W i = evalPair x y c u v (rowPoint q t i) := by
  let D := spec q t
  have F := shape_checked q t
  change atRow D.ta 0 = RibbonP3.zeroRow ∧ atRow D.tp 0 = RibbonP3.zeroRow ∧
    atRow D.tb 0 = atRow D.tp 32 ∧ (atRow D.tp 32).rim = D.bside ∧
    TableOK D.ta D.W.a ∧ TableOK D.tp D.W.p ∧ TableOK D.tb D.W.b at F
  obtain ⟨I,J,L,_,U,V,W⟩ := F
  have p : terminus x y (false,1) D.W = evalPair x y c u v (atRow D.tp 32) := by
    unfold terminus
    have h := table_follow x y c u v d D.tp D.W.p V D.W.pSize 32 (le_refl _)
    rwa [J,eval_zero] at h
  have iLt := i.isLt
  unfold wordPoint rowPoint
  split_ifs with h h'
  · have r := table_follow x y c u v d D.ta D.W.a U D.W.aSize i.val h.le
    rwa [I,eval_zero] at r
  · have r := table_follow x y c u v d D.tb D.W.b W D.W.bSize (i.val-32) (by omega)
    rwa [L,←p] at r
  · have r := table_follow x y c u v d D.tp D.W.p V D.W.pSize (i.val-63) (by omega)
    rwa [J,eval_zero] at r

theorem map_at (p : G→*H) (x y : G) (z : Bool×G) (w : Array P) (i : Nat) :
    project p (atWord x y z w i) = atWord (p x) (p y) (project p z) w i := by
  exact mapped_run p x y z (w.toList.take i)

theorem map_point (p : G→*H) (x y : G) (w : Words) (i : Tag) :
    project p (wordPoint x y (false,1) w i) = wordPoint (p x) (p y) (false,1) w i := by
  unfold wordPoint terminus
  split_ifs <;> simp only [map_at] <;> simp [project]

theorem bridge_side (p : G→*H) (x y : G) (c u v : H)
    (d : RibbonP3.Class3 (p x) (p y) c u v) (q t : Fin 3) :
    (terminus x y (false,1) (spec q t).W).1 = (spec q t).bside := by
  have U := shape_checked q t
  have J : atRow (spec q t).tp 0 = RibbonP3.zeroRow := U.2.1
  have Q := table_follow (p x) (p y) c u v d (spec q t).tp (spec q t).W.p
    U.2.2.2.2.2.1 (spec q t).W.pSize 32 (le_refl _)
  rw [J,eval_zero] at Q
  have M := map_at p x y (false,1) (spec q t).W.p 32
  rw [show project p ((false,1):Bool×G) = (false,1) by simp [project],Q] at M
  have B : (atRow (spec q t).tp 32).rim = (spec q t).bside := U.2.2.2.1
  exact (congrArg Prod.fst M).trans B

#print axioms point_collect
#print axioms bridge_side
end RibbonD3P3
