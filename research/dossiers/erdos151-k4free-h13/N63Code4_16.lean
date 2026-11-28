import N63BindingHelpers
import N63Bank21
import N63Bank22
import N63Bank23
import N63Bank24
import N63Bank25
import N63Bank26
import N63Bank27
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet4_16 : List Entry := ((bank21.drop 1).take 63) ++ (((bank22.drop 0).take 64) ++ (((bank23.drop 0).take 13)))
theorem enumerate4_16 : enumFast 9 14 4 16 = packet4_16.map Entry.rows := by decide +kernel
theorem bind4_16 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 16) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_16] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_16 at he
  simp only [List.mem_append] at he
  rcases he with he | he | he
  · exact bank21_checked e (mem_of_mem_slice he)
  · exact bank22_checked e (mem_of_mem_slice he)
  · exact bank23_checked e (mem_of_mem_slice he)
def packet4_17 : List Entry := ((bank23.drop 13).take 51) ++ (((bank24.drop 0).take 38))
theorem enumerate4_17 : enumFast 9 14 4 17 = packet4_17.map Entry.rows := by decide +kernel
theorem bind4_17 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 17) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_17] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_17 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank23_checked e (mem_of_mem_slice he)
  · exact bank24_checked e (mem_of_mem_slice he)
def packet4_18 : List Entry := ((bank24.drop 38).take 19)
theorem enumerate4_18 : enumFast 9 14 4 18 = packet4_18.map Entry.rows := by decide +kernel
theorem bind4_18 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 18) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_18] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_18 at he
  exact bank24_checked e (mem_of_mem_slice he)
def packet4_19 : List Entry := ((bank24.drop 57).take 7) ++ (((bank25.drop 0).take 19))
theorem enumerate4_19 : enumFast 9 14 4 19 = packet4_19.map Entry.rows := by decide +kernel
theorem bind4_19 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 19) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_19] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_19 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank24_checked e (mem_of_mem_slice he)
  · exact bank25_checked e (mem_of_mem_slice he)
def packet4_20 : List Entry := ((bank25.drop 19).take 45) ++ (((bank26.drop 0).take 44))
theorem enumerate4_20 : enumFast 9 14 4 20 = packet4_20.map Entry.rows := by decide +kernel
theorem bind4_20 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 20) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_20] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_20 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank25_checked e (mem_of_mem_slice he)
  · exact bank26_checked e (mem_of_mem_slice he)
def packet4_21 : List Entry := []
theorem enumerate4_21 : enumFast 9 14 4 21 = packet4_21.map Entry.rows := by decide +kernel
theorem bind4_21 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 21) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_21] at hr
  exact (List.not_mem_nil hr).elim
def packet4_22 : List Entry := ((bank26.drop 44).take 20) ++ (((bank27.drop 0).take 6))
theorem enumerate4_22 : enumFast 9 14 4 22 = packet4_22.map Entry.rows := by decide +kernel
theorem bind4_22 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 22) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_22] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_22 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank26_checked e (mem_of_mem_slice he)
  · exact bank27_checked e (mem_of_mem_slice he)
def packet4_23 : List Entry := []
theorem enumerate4_23 : enumFast 9 14 4 23 = packet4_23.map Entry.rows := by decide +kernel
theorem bind4_23 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 23) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_23] at hr
  exact (List.not_mem_nil hr).elim
end Erdos151N63
