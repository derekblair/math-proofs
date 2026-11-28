import N63BindingHelpers
import N63Bank36
import N63Bank37
import N63Bank38
import N63Bank39
import N63Bank40
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet4_40 : List Entry := ((bank36.drop 55).take 9) ++ (((bank37.drop 0).take 64) ++ (((bank38.drop 0).take 16)))
theorem enumerate4_40 : enumFast 9 14 4 40 = packet4_40.map Entry.rows := by decide +kernel
theorem bind4_40 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 40) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_40] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_40 at he
  simp only [List.mem_append] at he
  rcases he with he | he | he
  · exact bank36_checked e (mem_of_mem_slice he)
  · exact bank37_checked e (mem_of_mem_slice he)
  · exact bank38_checked e (mem_of_mem_slice he)
def packet4_41 : List Entry := ((bank38.drop 16).take 26)
theorem enumerate4_41 : enumFast 9 14 4 41 = packet4_41.map Entry.rows := by decide +kernel
theorem bind4_41 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 41) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_41] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_41 at he
  exact bank38_checked e (mem_of_mem_slice he)
def packet4_42 : List Entry := ((bank38.drop 42).take 22) ++ (((bank39.drop 0).take 56))
theorem enumerate4_42 : enumFast 9 14 4 42 = packet4_42.map Entry.rows := by decide +kernel
theorem bind4_42 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 42) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_42] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_42 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank38_checked e (mem_of_mem_slice he)
  · exact bank39_checked e (mem_of_mem_slice he)
def packet4_43 : List Entry := []
theorem enumerate4_43 : enumFast 9 14 4 43 = packet4_43.map Entry.rows := by decide +kernel
theorem bind4_43 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 43) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_43] at hr
  exact (List.not_mem_nil hr).elim
def packet4_44 : List Entry := ((bank39.drop 56).take 8) ++ (((bank40.drop 0).take 18))
theorem enumerate4_44 : enumFast 9 14 4 44 = packet4_44.map Entry.rows := by decide +kernel
theorem bind4_44 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 44) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_44] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_44 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank39_checked e (mem_of_mem_slice he)
  · exact bank40_checked e (mem_of_mem_slice he)
def packet4_45 : List Entry := ((bank40.drop 18).take 17)
theorem enumerate4_45 : enumFast 9 14 4 45 = packet4_45.map Entry.rows := by decide +kernel
theorem bind4_45 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 45) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_45] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_45 at he
  exact bank40_checked e (mem_of_mem_slice he)
def packet4_46 : List Entry := []
theorem enumerate4_46 : enumFast 9 14 4 46 = packet4_46.map Entry.rows := by decide +kernel
theorem bind4_46 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 46) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_46] at hr
  exact (List.not_mem_nil hr).elim
def packet4_47 : List Entry := []
theorem enumerate4_47 : enumFast 9 14 4 47 = packet4_47.map Entry.rows := by decide +kernel
theorem bind4_47 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 47) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_47] at hr
  exact (List.not_mem_nil hr).elim
end Erdos151N63
