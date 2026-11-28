import N63BindingHelpers
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet4_56 : List Entry := []
theorem enumerate4_56 : enumFast 9 14 4 56 = packet4_56.map Entry.rows := by decide +kernel
theorem bind4_56 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 56) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_56] at hr
  exact (List.not_mem_nil hr).elim
def packet4_57 : List Entry := []
theorem enumerate4_57 : enumFast 9 14 4 57 = packet4_57.map Entry.rows := by decide +kernel
theorem bind4_57 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 57) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_57] at hr
  exact (List.not_mem_nil hr).elim
def packet4_58 : List Entry := []
theorem enumerate4_58 : enumFast 9 14 4 58 = packet4_58.map Entry.rows := by decide +kernel
theorem bind4_58 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 58) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_58] at hr
  exact (List.not_mem_nil hr).elim
def packet4_59 : List Entry := []
theorem enumerate4_59 : enumFast 9 14 4 59 = packet4_59.map Entry.rows := by decide +kernel
theorem bind4_59 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 59) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_59] at hr
  exact (List.not_mem_nil hr).elim
def packet4_60 : List Entry := []
theorem enumerate4_60 : enumFast 9 14 4 60 = packet4_60.map Entry.rows := by decide +kernel
theorem bind4_60 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 60) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_60] at hr
  exact (List.not_mem_nil hr).elim
def packet4_61 : List Entry := []
theorem enumerate4_61 : enumFast 9 14 4 61 = packet4_61.map Entry.rows := by decide +kernel
theorem bind4_61 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 61) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_61] at hr
  exact (List.not_mem_nil hr).elim
def packet4_62 : List Entry := []
theorem enumerate4_62 : enumFast 9 14 4 62 = packet4_62.map Entry.rows := by decide +kernel
theorem bind4_62 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 62) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_62] at hr
  exact (List.not_mem_nil hr).elim
def packet4_63 : List Entry := []
theorem enumerate4_63 : enumFast 9 14 4 63 = packet4_63.map Entry.rows := by decide +kernel
theorem bind4_63 (r : Array Nat) (hr : r ∈ enumFast 9 14 4 63) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate4_63] at hr
  exact (List.not_mem_nil hr).elim
end Erdos151N63
