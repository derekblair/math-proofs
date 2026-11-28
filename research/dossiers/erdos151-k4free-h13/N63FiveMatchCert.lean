import N63FiveMatchCore
namespace Erdos151N63
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def match12 : List TenPivotEntry := [
  ⟨#[62, 65, 129, 193, 769, 769, 522, 268, 176, 112], 3, 4, [1, 2, 5]⟩,
  ⟨#[62, 65, 129, 321, 641, 769, 522, 276, 168, 112], 3, 4, [1, 2, 5]⟩,
  ⟨#[62, 65, 193, 257, 641, 769, 518, 276, 168, 112], 2, 4, [1, 3, 5]⟩,
  ⟨#[62, 65, 257, 321, 641, 641, 522, 304, 140, 112], 3, 4, [1, 2, 5]⟩,
  ⟨#[62, 129, 193, 321, 513, 769, 524, 262, 168, 112], 2, 3, [1, 4, 5]⟩,
  ⟨#[62, 129, 321, 321, 513, 641, 524, 290, 140, 112], 2, 3, [1, 4, 5]⟩,
  ⟨#[62, 193, 193, 257, 513, 769, 518, 262, 168, 112], 1, 2, [3, 4, 5]⟩,
  ⟨#[62, 193, 257, 321, 513, 641, 522, 290, 140, 112], 1, 3, [2, 4, 5]⟩]
theorem binding_12 : matchRows 12= match12.map TenPivotEntry.rows := by decide +kernel
theorem cert_12 : ∀ e ∈ match12, e.cert := by decide +kernel
def match18 : List TenPivotEntry := [
  ⟨#[62, 65, 129, 193, 769, 769, 266, 524, 112, 176], 3, 4, [1, 2, 5]⟩,
  ⟨#[62, 65, 129, 385, 577, 769, 274, 524, 104, 176], 3, 4, [1, 2, 5]⟩,
  ⟨#[62, 65, 193, 385, 513, 769, 262, 524, 104, 176], 2, 3, [1, 4, 5]⟩,
  ⟨#[62, 65, 385, 385, 513, 577, 290, 524, 76, 176], 2, 3, [1, 4, 5]⟩,
  ⟨#[62, 129, 193, 257, 577, 769, 276, 518, 104, 176], 2, 4, [1, 3, 5]⟩,
  ⟨#[62, 129, 257, 385, 577, 577, 304, 522, 76, 176], 3, 4, [1, 2, 5]⟩,
  ⟨#[62, 193, 193, 257, 513, 769, 262, 518, 104, 176], 1, 2, [3, 4, 5]⟩,
  ⟨#[62, 193, 257, 385, 513, 577, 290, 522, 76, 176], 1, 3, [2, 4, 5]⟩]
theorem binding_18 : matchRows 18= match18.map TenPivotEntry.rows := by decide +kernel
theorem cert_18 : ∀ e ∈ match18, e.cert := by decide +kernel
def match33 : List TenPivotEntry := [
  ⟨#[62, 65, 257, 321, 641, 641, 138, 112, 524, 304], 3, 4, [1, 2, 5]⟩,
  ⟨#[62, 65, 257, 385, 577, 641, 146, 104, 524, 304], 3, 4, [1, 2, 5]⟩,
  ⟨#[62, 65, 321, 385, 513, 641, 134, 104, 524, 304], 2, 3, [1, 4, 5]⟩,
  ⟨#[62, 65, 385, 385, 513, 577, 162, 76, 524, 304], 2, 3, [1, 4, 5]⟩,
  ⟨#[62, 129, 257, 321, 577, 641, 152, 98, 524, 304], 3, 4, [1, 2, 5]⟩,
  ⟨#[62, 129, 257, 385, 577, 577, 176, 74, 524, 304], 3, 4, [1, 2, 5]⟩,
  ⟨#[62, 129, 321, 321, 513, 641, 140, 98, 524, 304], 2, 3, [1, 4, 5]⟩,
  ⟨#[62, 129, 321, 385, 513, 577, 164, 74, 524, 304], 2, 3, [1, 4, 5]⟩]
theorem binding_33 : matchRows 33= match33.map TenPivotEntry.rows := by decide +kernel
theorem cert_33 : ∀ e ∈ match33, e.cert := by decide +kernel
theorem matching_pivots (h : Nat) (hh : h=12 ∨ h=18 ∨ h=33)
    (r : Array Nat) (hr : r ∈ matchRows h) :
    ∃ e : TenPivotEntry, r=e.rows ∧ e.cert := by
  rcases hh with rfl | rfl | rfl
  · rw [binding_12] at hr
    obtain ⟨e,he,hrow⟩ := List.mem_map.mp hr
    exact ⟨e,hrow.symm,cert_12 e he⟩
  · rw [binding_18] at hr
    obtain ⟨e,he,hrow⟩ := List.mem_map.mp hr
    exact ⟨e,hrow.symm,cert_18 e he⟩
  · rw [binding_33] at hr
    obtain ⟨e,he,hrow⟩ := List.mem_map.mp hr
    exact ⟨e,hrow.symm,cert_33 e he⟩
#print axioms matching_pivots
end Erdos151N63
