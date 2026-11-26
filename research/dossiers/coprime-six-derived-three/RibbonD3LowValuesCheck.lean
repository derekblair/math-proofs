import RibbonD3LowValuesNumeric

namespace RibbonD3Low
open RibbonD3WordSelection Ribbon5Bridge RibbonD3PortEval

theorem low_from_table (b : Bool) (n : Nat) (hn : n ≤ 128) :
    low (pChart b) n = (tabLow b)[n]! := by
  induction n with
  | zero => exact (initial b).symm
  | succ n ih =>
    have n0 : n < 128 := by omega
    have E : n < (block (pChart b) 128).length := by
      rwa [RibbonD3ChartCycles.length_block _ _ (le_refl 128)]
    have pref (i : Nat) (hi : i ≤ 128) :
        block (pChart b) i = (block (pChart b) 128).take i := by
      simp [block,decode,List.map_take,List.take_take,Nat.min_eq_left hi]
    have H : low (pChart b) (n+1) =
        push (low (pChart b) n) (block (pChart b) 128)[n]! := by
      unfold low
      rw [pref (n+1) hn,pref n (by omega),List.take_succ_eq_append_getElem E]
      rw [List.foldl_append,getElem!_pos (block (pChart b) 128) n E]
      rfl
    rw [H,ih (by omega)]
    exact numericStep b ⟨n,n0⟩

#print axioms low_from_table
end RibbonD3Low
