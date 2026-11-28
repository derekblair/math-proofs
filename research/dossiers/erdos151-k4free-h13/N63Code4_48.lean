import N63BindingHelpers
import N63Bank40
import N63Bank41
import N63Bank42
import N63Bank43
import N63Bank44
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet4_48 : List Entry := ((bank40.drop 35).take 29) ++ (((bank41.drop 0).take 60))
theorem enumerate4_48 : enumFast 9 14 4 48 = packet4_48.map Entry.rows := by decide +kernel
theorem bind4_48 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 48) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_48] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_48 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank40_checked e (mem_of_mem_slice he)
  · exact bank41_checked e (mem_of_mem_slice he)
def packet4_49 : List Entry := ((bank41.drop 60).take 4) ++ (((bank42.drop 0).take 22))
theorem enumerate4_49 : enumFast 9 14 4 49 = packet4_49.map Entry.rows := by decide +kernel
theorem bind4_49 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 49) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_49] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_49 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank41_checked e (mem_of_mem_slice he)
  · exact bank42_checked e (mem_of_mem_slice he)
def packet4_50 : List Entry := ((bank42.drop 22).take 26)
theorem enumerate4_50 : enumFast 9 14 4 50 = packet4_50.map Entry.rows := by decide +kernel
theorem bind4_50 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 50) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_50] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_50 at he
  exact bank42_checked e (mem_of_mem_slice he)
def packet4_51 : List Entry := ((bank42.drop 48).take 16) ++ (((bank43.drop 0).take 1))
theorem enumerate4_51 : enumFast 9 14 4 51 = packet4_51.map Entry.rows := by decide +kernel
theorem bind4_51 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 51) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_51] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_51 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank42_checked e (mem_of_mem_slice he)
  · exact bank43_checked e (mem_of_mem_slice he)
def packet4_52 : List Entry := ((bank43.drop 1).take 63) ++ (((bank44.drop 0).take 15))
theorem enumerate4_52 : enumFast 9 14 4 52 = packet4_52.map Entry.rows := by decide +kernel
theorem bind4_52 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 52) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_52] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_52 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank43_checked e (mem_of_mem_slice he)
  · exact bank44_checked e (mem_of_mem_slice he)
def packet4_53 : List Entry := []
theorem enumerate4_53 : enumFast 9 14 4 53 = packet4_53.map Entry.rows := by decide +kernel
theorem bind4_53 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 53) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_53] at hr
  exact (List.not_mem_nil hr).elim
def packet4_54 : List Entry := []
theorem enumerate4_54 : enumFast 9 14 4 54 = packet4_54.map Entry.rows := by decide +kernel
theorem bind4_54 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 54) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_54] at hr
  exact (List.not_mem_nil hr).elim
def packet4_55 : List Entry := []
theorem enumerate4_55 : enumFast 9 14 4 55 = packet4_55.map Entry.rows := by decide +kernel
theorem bind4_55 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 55) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_55] at hr
  exact (List.not_mem_nil hr).elim
end Erdos151N63
