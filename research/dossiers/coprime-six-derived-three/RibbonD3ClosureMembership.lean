import RibbonD3RBinding
import RibbonD3ClosureCheck

namespace RibbonD3ClosureMembership
open RibbonD3MateData RibbonD3MateUse RibbonD3Grid RibbonD3SignedEval
open RibbonD3PortEval RibbonDerived3 HaarClass4Structure RibbonSchreierCollect
open scoped commutatorElement
variable {G : Type*} [Group G]

def signedDecode (w : List Int) : List Letter :=
  w.map fun z => (z.natAbs-1, decide (0<z))

private theorem central_commGroup (H : Type*) [CommGroup H] : Central₂ H :=
  fun a b c => mul_comm _ _

private theorem evalC_one {H : Type*} [CommGroup H] (g : Nat → H) (w : List Com) :
    evalC g w = 1 := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    change cs g d * evalC g w = 1
    rw [ih,mul_one]
    simp [cs,sgn,commutatorElement_def,mul_comm,mul_left_comm,mul_assoc]

theorem empty_base_word {H : Type*} [CommGroup H] (g : Nat → H)
    (w : List Letter) (h : (normal w).1 = []) : evalL g w = 1 := by
  rw [normal_sound (central_commGroup H) g w,h,evalC_one]
  simp only [evalL,List.map_nil,List.prod_nil,mul_one]

def checkA (C : Chart) : Bool :=
  match schreier C.keys (letters C 32) with
  | none => false
  | some L => (normal (signedDecode L)).1.isEmpty

private theorem checkA_all : charts.all checkA = true := by decide +kernel

theorem A_mem_second (x y : G) (i : Fin charts.size) :
    eval (letter x y) (letters charts[i] 32) ∈ DLS G 1 := by
  let C := charts[i]
  have hc := Array.all_eq_true.mp checkA_all i.val i.isLt
  change checkA C = true at hc
  let L := schreier C.keys (letters C 32)
  cases E : L with
  | none => simp [checkA, L, E] at hc
  | some w =>
    have E' : schreier C.keys (letters C 32) = some w := E
    have H : (normal (signedDecode w)).1 = [] := by
      simpa [checkA,E'] using hc
    have op := schreier_sound x y C.keys (letters C 32) w (legal_erase _ _) E'
    change eval (letter x y) (letters C 32) ∈ DLS G 1
    rw [op]
    let f : Derived G →* Abelianization (Derived G) := Abelianization.of
    let g := ggen x y C.keys
    let d : Derived G := evalL g (signedDecode w)
    have one : f d = 1 := by
      change f (evalL (ggen x y C.keys) (w.map fun z => (z.natAbs-1, decide (0<z)))) = 1
      rw [←eval_decode_map x y C.keys f w]
      exact empty_base_word _ _ H
    have hm : d ∈ commutator (Derived G) :=
      (QuotientGroup.eq_one_iff (N:=commutator (Derived G)) d).mp one
    have hp := Subgroup.mem_map_of_mem (Derived G).subtype hm
    have s : (commutator (Derived G)).map (Derived G).subtype = DLS G 1 := by
      rw [←Subgroup.top_lowerCentralSeries_one,Subgroup.map_lowerCentralSeries,
        Subgroup.map_top,Subgroup.range_subtype]
    rw [s] at hp
    simpa only [d,g,signedDecode,Subgroup.subtype_apply,eval_decode_value] using hp

#print axioms A_mem_second
end RibbonD3ClosureMembership
