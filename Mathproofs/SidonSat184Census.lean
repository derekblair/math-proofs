import Mathproofs.SidonSat184

/-!
# The nine displayed one-hole Sidon sets

`census i` is manuscript row 13+i. The unique holes and saturated ten-element
extensions are kernel-checked. The two gate counterexamples are included.
No claim is made about the twelve unavailable earlier rows, search shells,
minimality, or historical priority.
-/

namespace SidonSat184

def census : Fin 9 → Finset ℕ := ![
  {52,65,75,79,91,121,123,129,170},
  {63,65,66,79,88,112,116,127,170},
  {9,62,63,74,98,106,121,123,126},
  {62,63,66,84,96,115,121,123,165},
  {20,64,65,81,90,113,121,123,127},
  {34,62,66,81,103,114,120,121,123},
  {10,62,63,65,90,101,111,119,123},
  {32,46,62,86,91,104,112,123,143},
  {9,70,73,79,81,112,117,124,141}]

def censusHole : Fin 9 → ℕ := ![86,182,23,49,13,13,182,179,24]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem census_facts : ∀ i : Fin 9,
    (census i).card = 9 ∧ census i ⊆ Finset.Icc 1 184 ∧
    censusHole i ∈ Finset.Icc 1 184 ∧ censusHole i ∉ census i ∧
    IsSidon (insert (censusHole i) (census i)) ∧
    (∀ y ∈ Finset.Icc 1 184, y ∉ census i →
      IsSidon (insert y (census i)) → y = censusHole i) := by
  unfold census censusHole IsSidon
  decide

theorem census_extensions_saturated (i : Fin 9) :
    (insert (censusHole i) (census i)).card = 10 ∧
      IsSaturated (insert (censusHole i) (census i)) 184 := by
  obtain ⟨hcard, hA, hx, hn, hsid, huni⟩ := census_facts i
  constructor
  · simp [Finset.card_insert_of_notMem hn, hcard]
  · exact unique_extension_saturated hA hx hsid huni

theorem census_unique_hole (i : Fin 9) :
    IsSidon (census i) ∧
      (∀ y ∈ Finset.Icc 1 184,
        y ∉ census i ∧ IsSidon (insert y (census i)) ↔ y = censusHole i) := by
  obtain ⟨_, _, _, hn, hsid, huni⟩ := census_facts i
  refine ⟨sidon_subset (Finset.subset_insert _ _) hsid, ?_⟩
  intro y hy
  constructor
  · rintro ⟨hyn, hys⟩
    exact huni y hy hyn hys
  · rintro rfl
    exact ⟨hn, hsid⟩

/-- Positions already occupied or blocked against a Sidon-preserving insertion. -/
noncomputable def blockedPositions (A : Finset ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun y => y ∈ A ∨ ¬ IsSidon (insert y A))

/-- The operational blocked-position definition has exactly 183 members. -/
theorem census_blocked_card (i : Fin 9) : (blockedPositions (census i) 184).card = 183 := by
  classical
  have he : blockedPositions (census i) 184 =
      (Finset.Icc 1 184).erase (censusHole i) := by
    ext y
    simp only [blockedPositions, Finset.mem_filter, Finset.mem_erase]
    have hh := (census_unique_hole i).2 y
    by_cases hy : y ∈ Finset.Icc 1 184
    · specialize hh hy
      simp only [hy, true_and, and_true]
      tauto
    · simp [hy]
  rw [he, Finset.card_erase_of_mem (census_facts i).2.2.1]
  norm_num [Nat.card_Icc]

/-- Rows 14 and 21 refute the proposed 121/123 gate for one-hole nine-sets. -/
theorem census_gate_counterexamples (i : Fin 9) (hi : i = 1 ∨ i = 8) :
    (census i).card = 9 ∧ census i ⊆ Finset.Icc 1 184 ∧
      IsSidon (census i) ∧ (blockedPositions (census i) 184).card = 183 ∧
      121 ∉ census i ∧ 123 ∉ census i := by
  refine ⟨(census_facts i).1, (census_facts i).2.1,
    (census_unique_hole i).1, census_blocked_card i, ?_⟩
  rcases hi with rfl | rfl <;> decide

end SidonSat184
