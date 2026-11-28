import N63BindingHelpers
import N63Bank14
import N63Bank15
import N63Bank16
import N63Bank17
import N63Bank18
import N63Bank19
import N63Bank20
import N63Bank21
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet4_8 : List Entry := ((bank14.drop 60).take 4) ++ (((bank15.drop 0).take 64) ++ (((bank16.drop 0).take 64) ++ (((bank17.drop 0).take 8))))
theorem enumerate4_8 : enumFast 9 14 4 8 = packet4_8.map Entry.rows := by decide +kernel
theorem bind4_8 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 8) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_8] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_8 at he
  simp only [List.mem_append] at he
  rcases he with he | he | he | he
  · exact bank14_checked e (mem_of_mem_slice he)
  · exact bank15_checked e (mem_of_mem_slice he)
  · exact bank16_checked e (mem_of_mem_slice he)
  · exact bank17_checked e (mem_of_mem_slice he)
def packet4_9 : List Entry := ((bank17.drop 8).take 56) ++ (((bank18.drop 0).take 33))
theorem enumerate4_9 : enumFast 9 14 4 9 = packet4_9.map Entry.rows := by decide +kernel
theorem bind4_9 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 9) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_9] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_9 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank17_checked e (mem_of_mem_slice he)
  · exact bank18_checked e (mem_of_mem_slice he)
def packet4_10 : List Entry := ((bank18.drop 33).take 31) ++ (((bank19.drop 0).take 58))
theorem enumerate4_10 : enumFast 9 14 4 10 = packet4_10.map Entry.rows := by decide +kernel
theorem bind4_10 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 10) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_10] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_10 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank18_checked e (mem_of_mem_slice he)
  · exact bank19_checked e (mem_of_mem_slice he)
def packet4_11 : List Entry := []
theorem enumerate4_11 : enumFast 9 14 4 11 = packet4_11.map Entry.rows := by decide +kernel
theorem bind4_11 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 11) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_11] at hr
  exact (List.not_mem_nil hr).elim
def packet4_12 : List Entry := ((bank19.drop 58).take 6) ++ (((bank20.drop 0).take 13))
theorem enumerate4_12 : enumFast 9 14 4 12 = packet4_12.map Entry.rows := by decide +kernel
theorem bind4_12 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 12) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_12] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_12 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank19_checked e (mem_of_mem_slice he)
  · exact bank20_checked e (mem_of_mem_slice he)
def packet4_13 : List Entry := ((bank20.drop 13).take 26)
theorem enumerate4_13 : enumFast 9 14 4 13 = packet4_13.map Entry.rows := by decide +kernel
theorem bind4_13 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 13) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_13] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_13 at he
  exact bank20_checked e (mem_of_mem_slice he)
def packet4_14 : List Entry := ((bank20.drop 39).take 25) ++ (((bank21.drop 0).take 1))
theorem enumerate4_14 : enumFast 9 14 4 14 = packet4_14.map Entry.rows := by decide +kernel
theorem bind4_14 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 14) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_14] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_14 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank20_checked e (mem_of_mem_slice he)
  · exact bank21_checked e (mem_of_mem_slice he)
def packet4_15 : List Entry := []
theorem enumerate4_15 : enumFast 9 14 4 15 = packet4_15.map Entry.rows := by decide +kernel
theorem bind4_15 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 15) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_15] at hr
  exact (List.not_mem_nil hr).elim
end Erdos151N63
