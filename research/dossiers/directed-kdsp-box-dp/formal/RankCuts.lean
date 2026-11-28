import Mathlib.Data.Finset.Max

namespace DirectedBoxDSP

variable {V K : Type*} [LinearOrder K]

/-- The algorithm needs no representation of the existential cut level.
For a nonempty lower child, the cut induces precisely a weak rank
threshold at some actual coordinate of a vertex in the box. -/
theorem cut_has_input_rank (box : Finset V) (coordinate : V → K) (level : K)
    (lower_nonempty : ∃ v ∈ box, coordinate v < level) :
    ∃ x ∈ box, coordinate x < level ∧
      ∀ v ∈ box, coordinate v < level ↔ coordinate v ≤ coordinate x := by
  classical
  let lower := box.filter (fun v => coordinate v < level)
  have hn : lower.Nonempty := by
    obtain ⟨v, hv, hl⟩ := lower_nonempty
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hl⟩⟩
  obtain ⟨x, hx, hmax⟩ := lower.exists_max_image coordinate hn
  obtain ⟨hxb, hxl⟩ := Finset.mem_filter.mp hx
  exact ⟨x, hxb, hxl, fun v hv => ⟨
    fun hvl => hmax v (Finset.mem_filter.mpr ⟨hv, hvl⟩),
    fun hvx => hvx.trans_lt hxl⟩⟩

/-- For cuts avoiding every current coordinate, the weak rank threshold
and its complementary rank set recover both strict geometric children. -/
theorem proper_rank_split (box : Finset V) (coordinate : V → K) (level : K)
    (lower_nonempty : ∃ v ∈ box, coordinate v < level)
    (avoid : ∀ v ∈ box, coordinate v ≠ level) :
    ∃ x ∈ box, (∀ v ∈ box, coordinate v < level ↔ coordinate v ≤ coordinate x) ∧
      (∀ v ∈ box, level < coordinate v ↔ coordinate x < coordinate v) := by
  obtain ⟨x, hx, _, h⟩ := cut_has_input_rank box coordinate level lower_nonempty
  refine ⟨x,hx,h,?_⟩
  intro v hv
  constructor
  · intro hv'
    exact lt_of_not_ge fun hle => (not_lt_of_ge hv'.le) ((h v hv).2 hle)
  · intro hv'
    have nlt : ¬ coordinate v < level := fun hl => not_le_of_gt hv' ((h v hv).1 hl)
    exact lt_of_le_of_ne (le_of_not_gt nlt) (Ne.symm (avoid v hv))

#print axioms cut_has_input_rank
#print axioms proper_rank_split
end DirectedBoxDSP
