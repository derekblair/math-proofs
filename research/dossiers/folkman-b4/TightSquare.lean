import TightShoreLift
import CentralSquare

namespace FolkmanB4.Tight
open Critical
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq V]

/-- A central square wholly off the contraction vertex would switch an
original perfect matching, impossible under its constant parity. -/
theorem no_central_square_off_port (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (covered : Covered I) (tight : Tight I A B) (k : V ≃ L)
    (signs : ∀ s t : V ≃ L, (∀ i, I (s i) i) → (∀ i, I (t i) i) →
      pSign (s.trans k.symm)=pSign (t.trans k.symm))
    (q : Option (In B) ≃ In A) (Q : ∀ i, pointsContraction I A B (q i) i)
    {x y : In B} (ne : x≠y)
    (c : pointsContraction I A B (q (some y)) (some x))
    (d : pointsContraction I A B (q (some x)) (some y)) : False := by
  obtain ⟨u,out,orig⟩ := Q none
  obtain ⟨m,hm,hv,_⟩ := lift_from_port I A B covered tight q Q u out orig
  have xy : x.val≠y.val := fun h => ne (Subtype.ext h)
  apply no_switch_square I k signs m hm xy
  · rw [hv y]
    exact c
  · rw [hv x]
    exact d

#print axioms no_central_square_off_port
end FolkmanB4.Tight
