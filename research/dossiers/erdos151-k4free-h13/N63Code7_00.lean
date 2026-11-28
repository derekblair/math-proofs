import N63BindingHelpers
import N63Bank49
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet7_0 : List Entry := ((bank49.drop 31).take 1)
theorem enumerate7_0 : enumFast 9 14 7 0 = packet7_0.map Entry.rows := by decide +kernel
theorem bind7_0 (r : Array Nat) (hr : r ∈ enumFast 9 14 7 0) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate7_0] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet7_0 at he
  exact bank49_checked e (mem_of_mem_slice he)
end Erdos151N63
