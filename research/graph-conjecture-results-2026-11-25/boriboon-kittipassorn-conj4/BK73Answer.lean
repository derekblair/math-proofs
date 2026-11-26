import BK73Statement
import BK73FinalEq
import BK73Final4

/-!
# Boriboon–Kittipassorn, Conjecture 4 (arXiv:2508.17569): answer

`conjecture_4 : ¬ Conjecture4`, `seven_three : minEdges 7 3 = 14` and
`seven_four : minEdges 7 4 = 11`. The statement definitions in `BK73Statement` are shown to
agree with the ones used by the computation (`BK73.mnd`), which is then reused.
-/

open SimpleGraph

namespace Arxiv2508_17569

theorem dreach_iff {V : Type*} (r : V → V → Prop) (k : ℕ) (u v : V) :
    BK73.DReach r k u v ↔ relPow r k u v := by
  constructor
  · intro h
    induction h with
    | refl u => rfl
    | tail _ hr ih => exact ⟨_, ih, hr⟩
  · induction k generalizing v with
    | zero => rintro rfl; exact BK73.DReach.refl _
    | succ k ih => rintro ⟨w, h1, h2⟩; exact BK73.DReach.tail (ih w h1) h2

theorem hasOD_iff {V : Type*} (G : SimpleGraph V) (d : ℕ) :
    BK73.HasOrientDiamLE G d ↔ HasOrientedDiameterLE G d := by
  constructor
  · rintro ⟨O, h⟩
    refine ⟨⟨O.arc⟩, ⟨O.arc_adj, fun u v huv => ⟨O.anti u v, fun hn => ?_⟩⟩, fun u v => ?_⟩
    · exact (O.total u v huv).resolve_right hn
    · obtain ⟨k, hk, hr⟩ := h u v
      exact ⟨k, hk, (dreach_iff _ _ _ _).mp hr⟩
  · rintro ⟨D, ⟨h1, h2⟩, h⟩
    refine ⟨⟨D.Adj, h1, fun u v huv => ?_, fun u v huv => (h2 u v (h1 u v huv)).mp huv⟩,
      fun u v => ?_⟩
    · by_cases hu : D.Adj u v
      · exact Or.inl hu
      · exact Or.inr (not_not.mp (mt (h2 u v huv).mpr hu))
    · obtain ⟨k, hk, hr⟩ := h u v
      exact ⟨k, hk, (dreach_iff _ _ _ _).mpr hr⟩

theorem minEdges_eq (n d : ℕ) : minEdges n d = BK73.mnd n d := by
  unfold BK73.mnd minEdges
  simp only [hasOD_iff]
  rfl

/-- **Conjecture 4 is false.** -/
theorem conjecture_4 : ¬ Conjecture4 := fun h =>
  BK73.conjecture4_false (fun n d h1 h2 => (minEdges_eq n d).symm.trans (h n d h1 h2))

/-- `m(7,3) = 14`; Conjecture 4 predicts `15`. -/
theorem seven_three : minEdges 7 3 = 14 := (minEdges_eq 7 3).trans BK73.mnd_7_3

/-- `m(7,4) = 11`; Conjecture 4 predicts `12`. -/
theorem seven_four : minEdges 7 4 = 11 := (minEdges_eq 7 4).trans BK73.mnd_7_4

end Arxiv2508_17569

#print axioms Arxiv2508_17569.conjecture_4
#print axioms Arxiv2508_17569.seven_three
#print axioms Arxiv2508_17569.seven_four
