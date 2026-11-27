import RibbonDumbbellWords
import RibbonD3ClosureMembership

namespace RibbonDumbbell
open Ribbon5Bridge RibbonDerived3 RibbonD3PortEval
open RibbonD3Grid RibbonD3SignedEval RibbonD3MateUse RibbonD3MateData
open RibbonSchreierCollect RibbonD3ClosureMembership
variable {G : Type*} [Group G]

/-- A proof-producing closed-side and metabelian-neutral port word. -/
structure NeutralWord (b : Bool) (W : Array P) where
  keys : Array Coord
  trace : List Int
  trace_ok : schreier keys (erasePorts b (enc W.toList)) = some trace
  zero_ab : (normal (signedDecode trace)).1 = []
  side_preserved : (run (1:PUnit.{1}) 1 (b,1) W.toList).1 = b

theorem eval_neutral (x y : G) (b : Bool) (W : Array P) (n : NeutralWord b W) :
    eval (letter x y) (erasePorts b (enc W.toList)) ∈ DLS G 1 := by
  have op := schreier_sound x y n.keys (erasePorts b (enc W.toList)) n.trace
    (legal_erase _ _) n.trace_ok
  rw [op]
  let f : Derived G →* Abelianization (Derived G) := Abelianization.of
  let g := ggen x y n.keys
  let d : Derived G := evalL g (signedDecode n.trace)
  have one : f d = 1 := by
    change f (evalL (ggen x y n.keys) (n.trace.map fun z => (z.natAbs-1, decide (0<z)))) = 1
    rw [←eval_decode_map x y n.keys f n.trace]
    exact empty_base_word _ _ n.zero_ab
  have hm : d ∈ commutator (Derived G) :=
    (QuotientGroup.eq_one_iff (N:=commutator (Derived G)) d).mp one
  have hp := Subgroup.mem_map_of_mem (Derived G).subtype hm
  have s : (commutator (Derived G)).map (Derived G).subtype = DLS G 1 := by
    rw [←Subgroup.top_lowerCentralSeries_one,Subgroup.map_lowerCentralSeries,
      Subgroup.map_top,Subgroup.range_subtype]
  rw [s] at hp
  simpa only [d,g,signedDecode,Subgroup.subtype_apply,eval_decode_value] using hp

theorem neutral_gain (x y : G) (u : Bool × G) (W : Array P) (wSize : W.size=32)
    (n : NeutralWord u.1 W) :
    displacement x y u W ∈ DLS G 1 := by
  have take : W.toList.take 32 = W.toList := List.take_of_length_le (by simp [wSize])
  unfold displacement atWord
  rw [take,run_trace,←eval_encode x y u.1 W.toList]
  exact (inferInstance : (DLS G 1).Normal).conj_mem _ (eval_neutral x y u.1 W n) u.2

theorem neutral_side (x y : G) (u : Bool × G) (W : Array P) (wSize : W.size=32)
    (n : NeutralWord u.1 W) : (atWord x y u W 32).1 = u.1 := by
  let f : G →* PUnit.{1} := 1
  have take : W.toList.take 32 = W.toList := List.take_of_length_le (by simp [wSize])
  have S := congrArg (Prod.fst : Bool × PUnit.{1} → Bool) (mapped_run f x y u W.toList)
  unfold atWord
  rw [take]
  simpa [f] using S.trans n.side_preserved

#print axioms neutral_gain
#print axioms neutral_side
end RibbonDumbbell
