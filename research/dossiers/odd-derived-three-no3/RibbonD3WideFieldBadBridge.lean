import RibbonD3WideOutcome
import RibbonD3WideOrbit

namespace RibbonD3Wide
open RibbonD3WideFinite
open RibbonD3Finite (Label.triple)
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem bad_table_eq : exactBad = bads.toList.map Label.triple := by decide +kernel

theorem bad_table_size : bads.size=96 := by decide +kernel

theorem bad_iff (t : Triple) : t∈exactBad ↔ Bad t := by
  rw [bad_table_eq]
  constructor
  · intro h
    obtain ⟨l, H, E⟩ := List.mem_map.mp h
    obtain ⟨i, hi, Ei⟩ := List.mem_iff_getElem.mp H
    have h' : i<bads.size := by simpa using hi
    let j : B := ⟨i,by simpa only [bad_table_size] using h'⟩
    refine ⟨j,?_⟩
    have V : bads[i] = l := by simpa only [Array.getElem_toList] using Ei
    simpa only [getBad,j,getElem!_pos bads i h',V] using E
  · rintro ⟨i,Eq⟩
    apply List.mem_map.mpr
    refine ⟨getBad i,?_ ,Eq⟩
    have h : i.val<bads.size := by simpa only [bad_table_size] using i.isLt
    apply List.mem_iff_getElem.mpr
    exact ⟨i.val, by simpa using h, by simp [Array.getElem_toList,getBad,getElem!_pos bads i.val h]⟩

end RibbonD3Wide
#print axioms RibbonD3Wide.bad_iff
