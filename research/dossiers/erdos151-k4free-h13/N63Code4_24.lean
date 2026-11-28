import N63BindingHelpers
import N63Bank27
import N63Bank28
import N63Bank29
import N63Bank30
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet4_24 : List Entry := ((bank27.drop 6).take 58) ++ (((bank28.drop 0).take 31))
theorem enumerate4_24 : enumFast 9 14 4 24 = packet4_24.map Entry.rows := by decide +kernel
theorem bind4_24 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 24) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_24] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_24 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank27_checked e (mem_of_mem_slice he)
  · exact bank28_checked e (mem_of_mem_slice he)
def packet4_25 : List Entry := ((bank28.drop 31).take 33) ++ (((bank29.drop 0).take 45))
theorem enumerate4_25 : enumFast 9 14 4 25 = packet4_25.map Entry.rows := by decide +kernel
theorem bind4_25 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 25) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_25] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_25 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank28_checked e (mem_of_mem_slice he)
  · exact bank29_checked e (mem_of_mem_slice he)
def packet4_26 : List Entry := ((bank29.drop 45).take 19) ++ (((bank30.drop 0).take 7))
theorem enumerate4_26 : enumFast 9 14 4 26 = packet4_26.map Entry.rows := by decide +kernel
theorem bind4_26 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 26) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_26] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_26 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank29_checked e (mem_of_mem_slice he)
  · exact bank30_checked e (mem_of_mem_slice he)
def packet4_27 : List Entry := []
theorem enumerate4_27 : enumFast 9 14 4 27 = packet4_27.map Entry.rows := by decide +kernel
theorem bind4_27 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 27) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_27] at hr
  exact (List.not_mem_nil hr).elim
def packet4_28 : List Entry := ((bank30.drop 7).take 26)
theorem enumerate4_28 : enumFast 9 14 4 28 = packet4_28.map Entry.rows := by decide +kernel
theorem bind4_28 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 28) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_28] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_28 at he
  exact bank30_checked e (mem_of_mem_slice he)
def packet4_29 : List Entry := []
theorem enumerate4_29 : enumFast 9 14 4 29 = packet4_29.map Entry.rows := by decide +kernel
theorem bind4_29 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 29) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_29] at hr
  exact (List.not_mem_nil hr).elim
def packet4_30 : List Entry := ((bank30.drop 33).take 17)
theorem enumerate4_30 : enumFast 9 14 4 30 = packet4_30.map Entry.rows := by decide +kernel
theorem bind4_30 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 30) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_30] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_30 at he
  exact bank30_checked e (mem_of_mem_slice he)
def packet4_31 : List Entry := []
theorem enumerate4_31 : enumFast 9 14 4 31 = packet4_31.map Entry.rows := by decide +kernel
theorem bind4_31 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 31) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_31] at hr
  exact (List.not_mem_nil hr).elim
end Erdos151N63
