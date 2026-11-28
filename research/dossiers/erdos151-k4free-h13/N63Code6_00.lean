import N63BindingHelpers
import N63Bank49
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def packet6_0 : List Entry := ((bank49.drop 16).take 15)
theorem enumerate6_0 : enumFast 9 14 6 0 = packet6_0.map Entry.rows := by decide +kernel
theorem bind6_0 (r : Array Nat) (hr : r ∈ enumFast 9 14 6 0) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate6_0] at hr
  obtain ⟨e,he,eq⟩ := List.mem_map.mp hr
  refine ⟨e,eq.symm,?_⟩
  unfold packet6_0 at he
  exact bank49_checked e (mem_of_mem_slice he)
def packet6_1 : List Entry := []
theorem enumerate6_1 : enumFast 9 14 6 1 = packet6_1.map Entry.rows := by decide +kernel
theorem bind6_1 (r : Array Nat) (hr : r ∈ enumFast 9 14 6 1) : ∃ e : Entry, r=e.rows ∧ e.Check 9 := by
  rw [enumerate6_1] at hr
  exact (List.not_mem_nil hr).elim
end Erdos151N63
