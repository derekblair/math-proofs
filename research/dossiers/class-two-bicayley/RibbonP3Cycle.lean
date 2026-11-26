import RibbonP3Glue
import RibbonP3KeySound

namespace RibbonP3
open Ribbon5Bridge HaarUniversal36
variable {G : Type*} [Group G]

private theorem conj_detect (s T : G) (h : 1=s*T*s⁻¹) : T=1 := by
  calc
    T = s⁻¹*(s*T*s⁻¹)*s := by group
    _ = 1 := by rw [←h]; simp

private theorem cross (x y : G) (t : Fin 3) (i j : Fin 64)
    (sum : i.val+j.val=64)
    (range : i.val=1 ∨ (if t=2 then 2 ≤ i.val ∧ i.val≤6 else 27 ≤ i.val ∧ i.val≤31))
    (E : vertAt x y t i=vertAt x y t j) :
    trace x y false a=1 := by
  have data := congrArg Prod.snd E
  simp only [vertAt,start,run_eq_trace,one_mul] at data
  by_cases ht : t=2
  · rw [if_pos ht] at range
    have iLo : 1 ≤ i.val := by omega
    have iHi : i.val≤6 := by omega
    have jl : ¬j.val≤32 := by omega
    have il : i.val≤32 := by omega
    simp only [wordAt,if_pos il,if_neg jl,wa,wb,if_pos ht] at data
    have ej : j.val-32=32-i.val := by omega
    rw [ej] at data
    interval_cases m : i.val
    · have f := pair_ax_1_31 x y
      unfold pref at f
      rw [data,inv_mul_cancel] at f
      exact conj_detect _ _ f
    · have f := pair_ax_2_30 x y
      unfold pref at f
      rw [data,inv_mul_cancel] at f
      simpa using conj_detect _ _ f
    · have f := pair_ax_3_29 x y
      unfold pref at f
      rw [data,inv_mul_cancel] at f
      simpa using conj_detect _ _ f
    · have f := pair_ax_4_28 x y
      unfold pref at f
      rw [data,inv_mul_cancel] at f
      simpa using conj_detect _ _ f
    · have f := pair_ax_5_27 x y
      unfold pref at f
      rw [data,inv_mul_cancel] at f
      simpa using conj_detect _ _ f
    · have f := pair_ax_6_26 x y
      unfold pref at f
      rw [data,inv_mul_cancel] at f
      simpa using conj_detect _ _ f
  · rw [if_neg ht] at range
    have iLo : 1 ≤ i.val := by omega
    have iHi : i.val≤31 := by omega
    have jl : ¬j.val≤32 := by omega
    have il : i.val≤32 := by omega
    simp only [wordAt,if_pos il,if_neg jl,wa,wb,if_neg ht] at data
    have ej : j.val-32=32-i.val := by omega
    rw [ej] at data
    rcases range with h | h
    · rw [h] at data
      have f := pair_a_1_31 x y
      unfold pref at f
      rw [data,inv_mul_cancel] at f
      exact conj_detect _ _ f
    · interval_cases m : i.val <;> try omega
      · have f := pair_a_27_5 x y
        unfold pref at f
        rw [data,inv_mul_cancel] at f
        simpa using conj_detect _ _ f
      · have f := pair_a_28_4 x y
        unfold pref at f
        rw [data,inv_mul_cancel] at f
        simpa using conj_detect _ _ f
      · have f := pair_a_29_3 x y
        unfold pref at f
        rw [data,inv_mul_cancel] at f
        simpa using conj_detect _ _ f
      · have f := pair_a_30_2 x y
        unfold pref at f
        rw [data,inv_mul_cancel] at f
        simpa using conj_detect _ _ f
      · have f := pair_a_31_1 x y
        unfold pref at f
        rw [data,inv_mul_cancel] at f
        simpa using conj_detect _ _ f

private theorem zero32 (x y : G) (t : Fin 3) (nil : L G 5=⊥)
    (E : vertAt x y t 0=vertAt x y t 32) : trace x y false a=1 := by
  have h : wordAt t 0=[] ∧ wordAt t 32=wa t := by fin_cases t <;> decide
  unfold vertAt at E
  rw [h.1,h.2,(stop_word t x y nil).1] at E
  exact (congrArg Prod.snd E).symm

theorem ribbon_cycle (x y : G) (t : Fin 3) (nil : L G 5=⊥)
    (detect : ∀ i j : Fin 64, vertAt x y t i=vertAt x y t j → rep t i=rep t j) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  by_cases Z : trace x y false a=1
  · left
    refine cycle_from_at x y _ (word32_size t) (word32_back x y t nil Z) ?_
    intro i j lt e
    rw [at32,at32] at e
    have r := detect _ _ e
    have ij : (⟨i.val,by have := i.isLt; omega⟩ : Fin 64) <
        ⟨j.val,by have := j.isLt; omega⟩ := lt
    have alternatives := residual_indices t _ _ ij r
    change (i.val=0 ∧ j.val=32) ∨
      (i.val+j.val=64 ∧ (i.val=1 ∨ (if t=2 then 2 ≤ i.val ∧ i.val≤6 else 27 ≤ i.val ∧ i.val≤31))) at alternatives
    have hi := i.isLt
    have hj := j.isLt
    omega
  · right
    have inj : Function.Injective (vertAt x y t) := by
      suffices H : ∀ i j : Fin 64, i<j → vertAt x y t i≠vertAt x y t j by
        intro i j e
        by_contra ne
        rcases lt_or_gt_of_ne ne with h | h
        · exact H i j h e
        · exact H j i h e.symm
      intro i j lt E
      rcases residual_indices t i j lt (detect _ _ E) with ⟨i0,j32⟩ | ⟨sum,range⟩
      · have ie : i=0 := Fin.ext i0
        have je : j=32 := Fin.ext j32
        rw [ie,je] at E
        exact Z (zero32 x y t nil E)
      · exact Z (cross x y t i j sum range E)
    refine cycle_from_at x y _ (word64_size t) (word64_back x y t nil) ?_
    intro i j h e
    rw [at64 x y t i nil,at64 x y t j nil] at e
    exact (Nat.ne_of_lt h) (congrArg Fin.val (refl_inj (inj e)))

end RibbonP3
#print axioms RibbonP3.ribbon_cycle
