import RibbonD3PortEval
import RibbonD3MateCheckAPI
import RibbonSchreierMateNormals

namespace RibbonD3MateUse
open RibbonD3MateData RibbonD3SignedEval RibbonD3Grid RibbonD3Closure RibbonDerived3
open HaarClass4Structure
variable {G : Type*} [Group G]

def ggen (x y : G) (keys : Array Coord) (n : Nat) : Derived G :=
  let q := keys[n]!
  ⟨edge x y q.1 q.2,edge_derived x y q.1 q.2⟩

theorem eval_decode_map {H : Type*} [Group H] (x y : G) (keys : Array Coord)
    (f : Derived G →* H) (w : List Int) :
    RibbonSchreierCollect.evalL (fun n => f (ggen x y keys n))
        (w.map fun z => (z.natAbs-1, decide (0<z))) =
    f (RibbonSchreierCollect.evalL (ggen x y keys)
        (w.map fun z => (z.natAbs-1, decide (0<z)))) := by
  induction w with
  | nil => simp only [List.map_nil,RibbonSchreierCollect.evalL,List.prod_nil,map_one]
  | cons z w ih =>
    simp only [List.map_cons,RibbonSchreierCollect.evalL,List.prod_cons,map_mul] at ih ⊢
    rw [ih]
    by_cases z0 : 0 < z <;> simp [RibbonSchreierCollect.ls,RibbonSchreierCollect.sgn,z0] <;> exact (map_inv f _).symm

theorem eval_decode_value (x y : G) (keys : Array Coord) (w : List Int) :
    ((RibbonSchreierCollect.evalL (ggen x y keys)
      (w.map fun z => (z.natAbs-1, decide (0<z)))) : Derived G).val =
    eval (indexed x y keys) w := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    simp only [List.map_cons,RibbonSchreierCollect.evalL,List.prod_cons,Subgroup.coe_mul,eval] at ih ⊢
    rw [ih]
    by_cases z0 : 0 < z <;>
      simp [RibbonSchreierCollect.ls,RibbonSchreierCollect.sgn,z0,ggen,indexed] <;> rfl

theorem map_third :
    (LS (Derived G) 2).map (Derived G).subtype = DLS G 2 := by
  rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top, Subgroup.range_subtype]

theorem dictionary_diff (x y : G) (C : Chart) (hc : C ∈ charts) (r : RRow) (hr : r ∈ C.rows) :
    eval (indexed x y C.keys) C.words[r.leftWord]!.toList *
    (eval (indexed x y C.keys) C.words[r.rightWord]!.toList)⁻¹ ∈ DLS G 2 := by
  let N := LS (Derived G) 2
  let f := QuotientGroup.mk' N
  let L := RibbonSchreierCollect.evalL (ggen x y C.keys)
      (RibbonSchreierCollect.decode C.words[r.leftWord]!)
  let R := RibbonSchreierCollect.evalL (ggen x y C.keys)
      (RibbonSchreierCollect.decode C.words[r.rightWord]!)
  have h := RibbonSchreierCollect.dictionary_equal
    (RibbonSchreierCollect.quotient_class_two (G:=Derived G))
      (fun n => f (ggen x y C.keys n)) C hc r hr
  have hLR : f L = f R := by
    simpa only [L,R,RibbonSchreierCollect.decode,eval_decode_map] using h
  have hm : L*R⁻¹ ∈ N := (QuotientGroup.eq_one_iff (N:=N) _).mp (by
    change f (L*R⁻¹)=1
    rw [map_mul,map_inv,hLR,mul_inv_cancel])
  rw [←map_third]
  have t := Subgroup.mem_map_of_mem (Derived G).subtype hm
  simpa only [L,R,RibbonSchreierCollect.decode,Subgroup.coe_mul,Subgroup.coe_inv,
    Subgroup.subtype_apply,eval_decode_value] using t

#print axioms dictionary_diff
end RibbonD3MateUse
