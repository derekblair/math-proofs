import N63BindingHelpers
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet8_0 : List Entry := []
theorem enumerate8_0 : enumFast 9 14 8 0 = packet8_0.map Entry.rows := by decide +kernel
theorem bind8_0 (r : Array Nat) (hr : r ∈ enumFast 9 14 8 0) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate8_0] at hr
  exact (List.not_mem_nil hr).elim
end Erdos151N63
