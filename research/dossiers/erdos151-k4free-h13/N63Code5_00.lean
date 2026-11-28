import N63BindingHelpers
import N63Bank44
import N63Bank45
import N63Bank46
import N63Bank47
import N63Bank48
import N63Bank49
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet5_0 : List Entry := ((bank44.drop 15).take 49) ++ (((bank45.drop 0).take 64) ++ (((bank46.drop 0).take 64) ++ (((bank47.drop 0).take 6))))
theorem enumerate5_0 : enumFast 9 14 5 0 = packet5_0.map Entry.rows := by decide +kernel
theorem bind5_0 (r : Array Nat) (hr : r ∈ enumFast 9 14 5 0) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate5_0] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet5_0 at he
  simp only [List.mem_append] at he
  rcases he with he | he | he | he
  · exact bank44_checked e (mem_of_mem_slice he)
  · exact bank45_checked e (mem_of_mem_slice he)
  · exact bank46_checked e (mem_of_mem_slice he)
  · exact bank47_checked e (mem_of_mem_slice he)
def packet5_1 : List Entry := ((bank47.drop 6).take 33)
theorem enumerate5_1 : enumFast 9 14 5 1 = packet5_1.map Entry.rows := by decide +kernel
theorem bind5_1 (r : Array Nat) (hr : r ∈ enumFast 9 14 5 1) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate5_1] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet5_1 at he
  exact bank47_checked e (mem_of_mem_slice he)
def packet5_2 : List Entry := ((bank47.drop 39).take 25) ++ (((bank48.drop 0).take 8))
theorem enumerate5_2 : enumFast 9 14 5 2 = packet5_2.map Entry.rows := by decide +kernel
theorem bind5_2 (r : Array Nat) (hr : r ∈ enumFast 9 14 5 2) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate5_2] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet5_2 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank47_checked e (mem_of_mem_slice he)
  · exact bank48_checked e (mem_of_mem_slice he)
def packet5_3 : List Entry := ((bank48.drop 8).take 13)
theorem enumerate5_3 : enumFast 9 14 5 3 = packet5_3.map Entry.rows := by decide +kernel
theorem bind5_3 (r : Array Nat) (hr : r ∈ enumFast 9 14 5 3) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate5_3] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet5_3 at he
  exact bank48_checked e (mem_of_mem_slice he)
def packet5_4 : List Entry := ((bank48.drop 21).take 33)
theorem enumerate5_4 : enumFast 9 14 5 4 = packet5_4.map Entry.rows := by decide +kernel
theorem bind5_4 (r : Array Nat) (hr : r ∈ enumFast 9 14 5 4) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate5_4] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet5_4 at he
  exact bank48_checked e (mem_of_mem_slice he)
def packet5_5 : List Entry := ((bank48.drop 54).take 10) ++ (((bank49.drop 0).take 3))
theorem enumerate5_5 : enumFast 9 14 5 5 = packet5_5.map Entry.rows := by decide +kernel
theorem bind5_5 (r : Array Nat) (hr : r ∈ enumFast 9 14 5 5) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate5_5] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet5_5 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank48_checked e (mem_of_mem_slice he)
  · exact bank49_checked e (mem_of_mem_slice he)
def packet5_6 : List Entry := ((bank49.drop 3).take 13)
theorem enumerate5_6 : enumFast 9 14 5 6 = packet5_6.map Entry.rows := by decide +kernel
theorem bind5_6 (r : Array Nat) (hr : r ∈ enumFast 9 14 5 6) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate5_6] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet5_6 at he
  exact bank49_checked e (mem_of_mem_slice he)
def packet5_7 : List Entry := []
theorem enumerate5_7 : enumFast 9 14 5 7 = packet5_7.map Entry.rows := by decide +kernel
theorem bind5_7 (r : Array Nat) (hr : r ∈ enumFast 9 14 5 7) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate5_7] at hr
  exact (List.not_mem_nil hr).elim
end Erdos151N63
