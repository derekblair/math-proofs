import N63BindingHelpers
import N63Bank30
import N63Bank31
import N63Bank32
import N63Bank33
import N63Bank34
import N63Bank35
import N63Bank36
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet4_32 : List Entry := ((bank30.drop 50).take 14) ++ (((bank31.drop 0).take 64) ++ (((bank32.drop 0).take 62)))
theorem enumerate4_32 : enumFast 9 14 4 32 = packet4_32.map Entry.rows := by decide +kernel
theorem bind4_32 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 32) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_32] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_32 at he
  simp only [List.mem_append] at he
  rcases he with he | he | he
  · exact bank30_checked e (mem_of_mem_slice he)
  · exact bank31_checked e (mem_of_mem_slice he)
  · exact bank32_checked e (mem_of_mem_slice he)
def packet4_33 : List Entry := ((bank32.drop 62).take 2) ++ (((bank33.drop 0).take 17))
theorem enumerate4_33 : enumFast 9 14 4 33 = packet4_33.map Entry.rows := by decide +kernel
theorem bind4_33 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 33) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_33] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_33 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank32_checked e (mem_of_mem_slice he)
  · exact bank33_checked e (mem_of_mem_slice he)
def packet4_34 : List Entry := ((bank33.drop 17).take 47) ++ (((bank34.drop 0).take 42))
theorem enumerate4_34 : enumFast 9 14 4 34 = packet4_34.map Entry.rows := by decide +kernel
theorem bind4_34 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 34) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_34] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_34 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank33_checked e (mem_of_mem_slice he)
  · exact bank34_checked e (mem_of_mem_slice he)
def packet4_35 : List Entry := ((bank34.drop 42).take 22) ++ (((bank35.drop 0).take 4))
theorem enumerate4_35 : enumFast 9 14 4 35 = packet4_35.map Entry.rows := by decide +kernel
theorem bind4_35 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 35) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_35] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_35 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank34_checked e (mem_of_mem_slice he)
  · exact bank35_checked e (mem_of_mem_slice he)
def packet4_36 : List Entry := ((bank35.drop 4).take 60) ++ (((bank36.drop 0).take 29))
theorem enumerate4_36 : enumFast 9 14 4 36 = packet4_36.map Entry.rows := by decide +kernel
theorem bind4_36 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 36) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_36] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_36 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank35_checked e (mem_of_mem_slice he)
  · exact bank36_checked e (mem_of_mem_slice he)
def packet4_37 : List Entry := ((bank36.drop 29).take 26)
theorem enumerate4_37 : enumFast 9 14 4 37 = packet4_37.map Entry.rows := by decide +kernel
theorem bind4_37 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 37) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_37] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_37 at he
  exact bank36_checked e (mem_of_mem_slice he)
def packet4_38 : List Entry := []
theorem enumerate4_38 : enumFast 9 14 4 38 = packet4_38.map Entry.rows := by decide +kernel
theorem bind4_38 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 38) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_38] at hr
  exact (List.not_mem_nil hr).elim
def packet4_39 : List Entry := []
theorem enumerate4_39 : enumFast 9 14 4 39 = packet4_39.map Entry.rows := by decide +kernel
theorem bind4_39 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 39) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_39] at hr
  exact (List.not_mem_nil hr).elim
end Erdos151N63
