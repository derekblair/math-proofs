import RibbonD3OrderSeven
import RibbonD3TagData5
import RibbonD3FactorData5
import RibbonD3FieldPoint

namespace RibbonD3Low
set_option maxRecDepth 5000
open RibbonD3WordSelection RibbonD3VertexMates RibbonD3MateData
open RibbonD3Field (label raw)
open RibbonAffine (Mono eRow pl mon nf negative poly_eq pl_append negative_sound)
open RibbonDerived3 HaarClass4Structure HaarClass4Ports RibbonClass4Fallback
variable {G K : Type*} [Group G] [Field K]

def facList : List Mono := [(0,0,1),(0,1,1),(1,0,-2),(1,1,-2),(2,0,1),(2,1,1)]
def tagFive := tagFun 5 tagBank5
def mapFive := (RibbonD3Field.chart kFive).map
def repFive := (RibbonD3Field.chart kFive).reps

set_option maxHeartbeats 3000000 in
private theorem tagFiveSlice (g : Fin 8) : ∀ i : Fin 16,
    mapFive[g.val*16+i.val]! ∈ tagFive (tabLow false)[g.val*16+i.val]! := by
  fin_cases g <;> decide +kernel

theorem tagFive_checked (i : Fin 128) : mapFive[i.val]! ∈ tagFive (low kFive i.val) := by
  obtain ⟨g,h,e⟩ := split128 i
  have Q := tagFiveSlice g h
  rw [e] at Q
  change mapFive[i.val]! ∈ tagFive (low (pChart false) i.val)
  rw [low_from_table false _ i.isLt.le]
  exact Q

def coversFactor (i j : Nat) : Bool := factors5.any fun f => f.i == i && f.j == j
def tagsCovered : Bool :=
  tagBank5.all fun d => d.2.all fun i => d.2.all fun j => !(i<j) || coversFactor i j

theorem tagsCovered_true : tagsCovered = true := by decide +kernel

def checkFactor (f : Factor5) : Bool :=
  decide (nf (repFive[f.i]!.tr ++ negative repFive[f.j]!.tr) = nf facList)
theorem factors5_checked : factors5.all checkFactor = true := by decide +kernel

theorem factor_poly (a b : Kˣ) :
    pl a b facList = ((a:K)-1)^2*((b:K)+1) := by
  norm_num [facList,pl,mon,Units.val_mul,zpow_ofNat,Units.val_pow_eq_pow_val]
  ring

theorem factor_binding (a b : Kˣ) (i j : Nat) (h : coversFactor i j = true) :
    pl a b repFive[i]!.tr - pl a b repFive[j]!.tr = ((a:K)-1)^2*((b:K)+1) := by
  unfold coversFactor at h
  obtain ⟨m,hm,P⟩ := Array.any_eq_true.mp h
  simp only [Bool.and_eq_true_iff,beq_iff_eq] at P
  have T := Array.all_eq_true.mp factors5_checked m hm
  change decide (nf (repFive[factors5[m].i]!.tr ++ negative repFive[factors5[m].j]!.tr) = nf facList) = true at T
  rw [P.1,P.2] at T
  have E := poly_eq a b _ _ (of_decide_eq_true T)
  rwa [pl_append,negative_sound,←sub_eq_add_neg,factor_poly] at E

theorem withinTag (q : Ribbon5Bridge.Q) (a b : Nat)
    (ha : a ∈ tagFive q) (hb : b ∈ tagFive q) (lt : a < b) :
    coversFactor a b = true := by
  unfold tagFive tagFun at ha hb
  cases E : tagBank5.find? (fun r => r.1 == lowKey 5 q) with
  | none => simp [E] at ha
  | some j =>
    have J : j ∈ tagBank5 := List.mem_of_find?_eq_some E
    have U := List.all_eq_true.mp tagsCovered_true j J
    have aM : a ∈ j.2 := by simpa [E] using ha
    have bM : b ∈ j.2 := by simpa [E] using hb
    have C := List.all_eq_true.mp (List.all_eq_true.mp U a aM) b bM
    simpa [lt] using C

theorem projected_five_normalized (d3 : DLS G 3 = ⊥) (x y : G)
    (p : orderOf (QuotientGroup.mk' (LS G 2) (portC x y)) = 5)
    (μ : G →* Kˣ) (τ : G → K) (co : RibbonStationaryChart.Aff μ τ)
    (pivot : (μ x:K) ≠ 1) (minus : (μ y:K)+1 ≠ 0)
    (tx : τ x=0) (ty : τ y=1) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  apply RibbonD3ChartCycles.from_chart d3 x y kFive
  intro i j e
  have U := lowKey_eq x y kFive p
    (within_gap kFive i j (within_checked.2 i) (within_checked.2 j) (by decide)) e
  have H := congrArg (fun q => ((tagBank5.find? fun r => r.1 == q).map Prod.snd).getD []) U
  change tagFive (low kFive i.val) = tagFive (low kFive j.val) at H
  have pi := tagFive_checked i
  have pj := tagFive_checked j
  rw [←H] at pj
  have si := ((RibbonD3Field.charts_shape kFive).2.2 i).2
  have sj := ((RibbonD3Field.charts_shape kFive).2.2 j).2
  change repFive[mapFive[i.val]!]! = _ at si
  change repFive[mapFive[j.val]!]! = _ at sj
  by_cases N : mapFive[i.val]! = mapFive[j.val]!
  · rw [←si,←sj,N]
  · have vv := RibbonD3FieldPoint.affine_collision μ τ co x y tx ty kFive i.val j.val e
    rw [←RibbonD3Field.label_eval _ _ (raw (RibbonD3Field.chart kFive) i.val),
      ←RibbonD3Field.label_eval _ _ (raw (RibbonD3Field.chart kFive) j.val),←si,←sj] at vv
    have eqv := congrArg (fun x : Bool × Kˣ × K => x.2.2) vv
    simp only [eRow,RibbonD3Field.Label.toRow] at eqv
    change pl (μ x) (μ y) repFive[mapFive[i.val]!]!.tr =
        pl (μ x) (μ y) repFive[mapFive[j.val]!]!.tr at eqv
    have ne : ((μ x:K)-1)^2*((μ y:K)+1) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr pivot)) minus
    exfalso
    rcases lt_or_gt_of_ne N with I|J
    · have w := factor_binding (μ x) (μ y) _ _ (withinTag (low kFive i.val) _ _ pi pj I)
      rw [eqv,sub_self] at w
      exact ne w.symm
    · have w := factor_binding (μ x) (μ y) _ _ (withinTag (low kFive i.val) _ _ pj pi J)
      rw [eqv,sub_self] at w
      exact ne w.symm

#print axioms projected_five_normalized
end RibbonD3Low
