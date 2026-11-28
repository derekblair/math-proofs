import N63BindingHelpers
import N63Bank00
import N63Bank01
import N63Bank02
import N63Bank03
import N63Bank04
import N63Bank05
import N63Bank06
import N63Bank07
import N63Bank08
import N63Bank09
import N63Bank10
import N63Bank11
import N63Bank12
import N63Bank13
import N63Bank14
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet4_0 : List Entry := ((bank0.drop 0).take 64) ++ (((bank1.drop 0).take 64) ++ (((bank2.drop 0).take 63)))
theorem enumerate4_0 : enumFast 9 14 4 0 = packet4_0.map Entry.rows := by decide +kernel
theorem bind4_0 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 0) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_0] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_0 at he
  simp only [List.mem_append] at he
  rcases he with he | he | he
  · exact bank0_checked e (mem_of_mem_slice he)
  · exact bank1_checked e (mem_of_mem_slice he)
  · exact bank2_checked e (mem_of_mem_slice he)
def packet4_1 : List Entry := ((bank2.drop 63).take 1) ++ (((bank3.drop 0).take 64) ++ (((bank4.drop 0).take 64) ++ (((bank5.drop 0).take 11))))
theorem enumerate4_1 : enumFast 9 14 4 1 = packet4_1.map Entry.rows := by decide +kernel
theorem bind4_1 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 1) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_1] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_1 at he
  simp only [List.mem_append] at he
  rcases he with he | he | he | he
  · exact bank2_checked e (mem_of_mem_slice he)
  · exact bank3_checked e (mem_of_mem_slice he)
  · exact bank4_checked e (mem_of_mem_slice he)
  · exact bank5_checked e (mem_of_mem_slice he)
def packet4_2 : List Entry := ((bank5.drop 11).take 53) ++ (((bank6.drop 0).take 64) ++ (((bank7.drop 0).take 23)))
theorem enumerate4_2 : enumFast 9 14 4 2 = packet4_2.map Entry.rows := by decide +kernel
theorem bind4_2 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 2) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_2] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_2 at he
  simp only [List.mem_append] at he
  rcases he with he | he | he
  · exact bank5_checked e (mem_of_mem_slice he)
  · exact bank6_checked e (mem_of_mem_slice he)
  · exact bank7_checked e (mem_of_mem_slice he)
def packet4_3 : List Entry := ((bank7.drop 23).take 41) ++ (((bank8.drop 0).take 48))
theorem enumerate4_3 : enumFast 9 14 4 3 = packet4_3.map Entry.rows := by decide +kernel
theorem bind4_3 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 3) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_3] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_3 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank7_checked e (mem_of_mem_slice he)
  · exact bank8_checked e (mem_of_mem_slice he)
def packet4_4 : List Entry := ((bank8.drop 48).take 16) ++ (((bank9.drop 0).take 64) ++ (((bank10.drop 0).take 60)))
theorem enumerate4_4 : enumFast 9 14 4 4 = packet4_4.map Entry.rows := by decide +kernel
theorem bind4_4 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 4) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_4] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_4 at he
  simp only [List.mem_append] at he
  rcases he with he | he | he
  · exact bank8_checked e (mem_of_mem_slice he)
  · exact bank9_checked e (mem_of_mem_slice he)
  · exact bank10_checked e (mem_of_mem_slice he)
def packet4_5 : List Entry := ((bank10.drop 60).take 4) ++ (((bank11.drop 0).take 64) ++ (((bank12.drop 0).take 21)))
theorem enumerate4_5 : enumFast 9 14 4 5 = packet4_5.map Entry.rows := by decide +kernel
theorem bind4_5 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 5) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_5] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_5 at he
  simp only [List.mem_append] at he
  rcases he with he | he | he
  · exact bank10_checked e (mem_of_mem_slice he)
  · exact bank11_checked e (mem_of_mem_slice he)
  · exact bank12_checked e (mem_of_mem_slice he)
def packet4_6 : List Entry := ((bank12.drop 21).take 43) ++ (((bank13.drop 0).take 46))
theorem enumerate4_6 : enumFast 9 14 4 6 = packet4_6.map Entry.rows := by decide +kernel
theorem bind4_6 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 6) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_6] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_6 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank12_checked e (mem_of_mem_slice he)
  · exact bank13_checked e (mem_of_mem_slice he)
def packet4_7 : List Entry := ((bank13.drop 46).take 18) ++ (((bank14.drop 0).take 60))
theorem enumerate4_7 : enumFast 9 14 4 7 = packet4_7.map Entry.rows := by decide +kernel
theorem bind4_7 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 7) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_7] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet4_7 at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact bank13_checked e (mem_of_mem_slice he)
  · exact bank14_checked e (mem_of_mem_slice he)
end Erdos151N63
