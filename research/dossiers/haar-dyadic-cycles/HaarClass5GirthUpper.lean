import HaarUniversal36
import HaarReducedWalkCycle

namespace HaarClass5GirthUpper
open HaarUniversal36 HaarAllNoncommuting

theorem even_cycle_le36 {G : Type*} [Group G] (x y : G)
    (hx : x≠1) (hy : y≠1) (hxy : x≠y) (nil : L G 5=⊥) :
    ∃ k, 4 ≤ k ∧ k ≤ 36 ∧ Even k ∧ HasCycle x y k := by
  have data := HaarReducedWalkCycle.fromWord x y hx hy hxy word
    (by rw [word_len]; decide) (by rw [word_len]; decide) word_good (word_closes nil x y)
  simpa only [word_len] using data

end HaarClass5GirthUpper
#print axioms HaarClass5GirthUpper.even_cycle_le36
