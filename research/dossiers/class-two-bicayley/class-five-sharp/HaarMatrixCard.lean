import HaarMatrixCycle

namespace HaarMatrixCard
open HaarMatrixFiltration HaarMatrixCycle

abbrev Off := {p : Fin 6 × Fin 6 // p.1.val<p.2.val}

def fill (f : Off → ZMod 17) : Mat := fun i j =>
  if h : i.val<j.val then f ⟨(i,j),h⟩ else (1:Mat) i j

theorem fill_band (f : Off → ZMod 17) : Band 1 (fill f-1) := by
  intro i j h
  have z : ¬ i.val<j.val := by omega
  simp [fill,z]

noncomputable def strict_entries : UT ≃ (Off → ZMod 17) where
  toFun u p := value u p.val.1 p.val.2
  invFun f := ofMatrix (fill f) (fill_band f)
  right_inv f := by
    funext a
    change value (ofMatrix (fill f) (fill_band f)) a.val.1 a.val.2 = f a
    rw [value_ofMatrix]
    exact dite_eq_left a.property
  left_inv u := by
    apply value_inj
    rw [value_ofMatrix]
    ext i j
    by_cases h : i.val<j.val
    · unfold fill
      rw [dite_eq_left h]
    · have hu := (mem_upper.mp u.property) i j (by omega)
      exact (dite_eq_right h).trans ((sub_eq_zero.mp hu).symm)

theorem off_card : Fintype.card Off = 15 := by decide

theorem unitriangular_card : Nat.card UT = 17^15 := by
  rw [Nat.card_congr strict_entries,Nat.card_eq_fintype_card,Fintype.card_fun,off_card,ZMod.card]

theorem unitriangular_pgroup : IsPGroup 17 UT := by
  exact IsPGroup.of_card unitriangular_card

end HaarMatrixCard

#print axioms HaarMatrixCard.unitriangular_card
