import RibbonSchreierNormal
import RibbonD3MateData

namespace RibbonSchreierCollect
open RibbonD3MateData
open scoped commutatorElement
open HaarClass4Structure
set_option maxRecDepth 22000
set_option maxHeartbeats 0

def decode (w : Array Int) : List Letter :=
  w.toList.map fun z => (z.natAbs-1, decide (0<z))

def dictionary (c : Chart) := c.words.map (fun w => normal (decode w))

def rowCheck (c : Chart) : Bool :=
  let Q := dictionary c
  c.rows.all fun r => decide (Q[r.leftWord]! = Q[r.rightWord]!)

theorem normal_rows : charts.all rowCheck = true := by decide +kernel

theorem dictionary_pos (c : Chart) (i : Nat) :
    (dictionary c)[i]! = normal (decode c.words[i]!) := by
  by_cases h : i<c.words.size
  · have e : i<(dictionary c).size := by simpa only [dictionary,Array.size_map] using h
    rw [getElem!_pos (dictionary c) i e,getElem!_pos c.words i h]
    simp [dictionary]
  · have e : ¬i<(dictionary c).size := by simpa only [dictionary,Array.size_map] using h
    rw [getElem!_neg (dictionary c) i e,getElem!_neg c.words i h]
    rfl

theorem dictionary_equal {G : Type*} [Group G] (h : Central₂ G)
    (g : Nat→G) (c : Chart) (hc : c∈charts) (r : RRow) (hr : r∈c.rows) :
    evalL g (decode c.words[r.leftWord]!) =
    evalL g (decode c.words[r.rightWord]!) := by
  have e := Array.all_eq_true'.mp normal_rows c hc
  have f := Array.all_eq_true'.mp e r hr
  have H := of_decide_eq_true f
  rw [dictionary_pos,dictionary_pos] at H
  exact same_normal h g _ _ H

theorem quotient_class_two {G : Type*} [Group G] :
    Central₂ (G ⧸ LS G 2) := by
  let f := QuotientGroup.mk' (LS G 2)
  have surj := QuotientGroup.mk'_surjective (LS G 2)
  intro a b c
  obtain ⟨a,rfl⟩ := surj a
  obtain ⟨b,rfl⟩ := surj b
  obtain ⟨c,rfl⟩ := surj c
  apply commutatorElement_eq_one_iff_commute.mp
  simp only [←map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)) (Subgroup.mem_top c))

end RibbonSchreierCollect
#print axioms RibbonSchreierCollect.normal_rows
#print axioms RibbonSchreierCollect.dictionary_equal
#print axioms RibbonSchreierCollect.quotient_class_two
