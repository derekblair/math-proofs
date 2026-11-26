import RibbonD3TagData7
import RibbonD3LowValuesCheck
import RibbonD3ChartCycles

namespace RibbonD3Low
open RibbonD3WordSelection RibbonD3VertexMates RibbonD3MateData Ribbon5Bridge
open RibbonD3Field (label raw)
open RibbonDerived3 HaarClass4Structure HaarClass4Ports
open RibbonClass4Fallback
variable {G : Type*} [Group G]

def kSeven : Count := 9
def kFive : Count := 7

def within (k : Count) (i : Fin 128) : Prop :=
  -1 ≤ (low k i.val).2.1 ∧ (low k i.val).2.1 ≤ 2 ∧
  -1 ≤ (low k i.val).2.2.1 ∧ (low k i.val).2.2.1 ≤ 2
instance (k : Count) (i : Fin 128) : Decidable (within k i) := by unfold within; infer_instance

def tableWithin (b : Bool) (n : Nat) : Prop :=
  -1 ≤ (tabLow b)[n]!.2.1 ∧ (tabLow b)[n]!.2.1 ≤ 2 ∧
  -1 ≤ (tabLow b)[n]!.2.2.1 ∧ (tabLow b)[n]!.2.2.1 ≤ 2
instance (b : Bool) (n : Nat) : Decidable (tableWithin b n) := by unfold tableWithin; infer_instance

theorem split128 (l : Fin 128) :
    ∃ a : Fin 8, ∃ b : Fin 16, a.val*16+b.val = l.val := by
  refine ⟨⟨l.val/16,by have := l.isLt; omega⟩,⟨l.val%16,by omega⟩,?_⟩
  change l.val / 16 * 16 + l.val % 16 = l.val
  omega

set_option maxHeartbeats 2000000 in
private theorem withinSlice (b : Bool) (g : Fin 8) :
    ∀ i : Fin 16, tableWithin b (g.val*16+i.val) := by
  cases b <;> fin_cases g <;> decide +kernel

private theorem within_by_table (b : Bool) (i : Fin 128) : within (pChart b) i := by
  obtain ⟨g,h,e⟩ := split128 i
  have Q := withinSlice b g h
  rw [e] at Q
  unfold within
  rw [low_from_table b i.val i.isLt.le]
  exact Q

theorem within_checked : (∀ i, within kSeven i) ∧ (∀ i, within kFive i) :=
  ⟨within_by_table true,within_by_table false⟩

theorem within_gap (k : Count) (i j : Fin 128) (hi : within k i) (hj : within k j)
    {p : Nat} (h : 4 ≤ p) : smallGaps p k i.val j.val := by
  unfold within at hi hj
  unfold smallGaps
  omega

def tagFun (p : Nat) (B : List ((Bool × ℤ × ℤ × ℤ) × List Nat)) (q : Q) : List Nat :=
  ((B.find? fun r => r.1 == lowKey p q).map Prod.snd).getD []

set_option maxHeartbeats 3000000 in
private theorem tagSevenSlice (g : Fin 8) : ∀ i : Fin 16,
    tagFun 7 tagBank7 (tabLow true)[g.val*16+i.val]! =
      [(RibbonD3Field.chart kSeven).map[g.val*16+i.val]!] := by
  fin_cases g <;> decide +kernel

theorem tagSeven_checked (i : Fin 128) :
    tagFun 7 tagBank7 (low kSeven i.val) = [(RibbonD3Field.chart kSeven).map[i.val]!] := by
  obtain ⟨g,h,e⟩ := split128 i
  have Q := tagSevenSlice g h
  rw [e] at Q
  change tagFun 7 tagBank7 (low (pChart true) i.val) = _
  rw [low_from_table true _ i.isLt.le]
  exact Q

theorem projected_seven (d3 : DLS G 3 = ⊥) (x y : G)
    (h : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=7) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  apply RibbonD3ChartCycles.from_chart d3 x y kSeven
  intro i j e
  have U := lowKey_eq x y kSeven h
    (within_gap kSeven i j (within_checked.1 i) (within_checked.1 j) (by decide)) e
  have H := congrArg (fun q => ((tagBank7.find? fun r => r.1 == q).map Prod.snd).getD []) U
  change tagFun 7 tagBank7 (low kSeven i.val) = tagFun 7 tagBank7 (low kSeven j.val) at H
  rw [tagSeven_checked,tagSeven_checked] at H
  have M := List.singleton_inj.mp H
  exact ((RibbonD3Field.charts_shape _).2.2 i).2.symm.trans
    ((congrArg (fun n : Nat => (RibbonD3Field.chart kSeven).reps[n]!) M).trans
      ((RibbonD3Field.charts_shape _).2.2 j).2)

#print axioms projected_seven
end RibbonD3Low
