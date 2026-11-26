import HaarMatrixRows

namespace HaarMatrixCycle
open HaarMatrixFiltration HaarMatrixRows HaarAllNoncommuting

abbrev UT := upper 1

def value (g : UT) : Mat := (g.val:Mat)

theorem value_inj : Function.Injective value :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem value_mul (a b : UT) : value (a*b)=value a * value b := rfl

noncomputable def ofMatrix (A : Mat) (h : Band 1 (A-1)) : UT := by
  have e : IsUnit A := by simpa only [add_sub_cancel] using unit_add h
  exact ⟨e.unit,by change Band 1 ((e.unit:Mat)-1); rw [e.unit_spec]; exact h⟩

theorem value_ofMatrix (A : Mat) (h : Band 1 (A-1)) : value (ofMatrix A h)=A := by
  unfold ofMatrix value
  exact IsUnit.unit_spec _

noncomputable def x : UT := ofMatrix rawX gen_band.1
noncomputable def y : UT := ofMatrix rawY gen_band.2
noncomputable def V (i : Fin 64) : Bool × UT :=
  (side i,ofMatrix (getRow i) (row_band i))

theorem value_x : value x=rawX := value_ofMatrix _ _
theorem value_y : value y=rawY := value_ofMatrix _ _
theorem value_vert (i : Fin 64) : value (V i).2=getRow i := value_ofMatrix _ (row_band i)

theorem vertices : Function.Injective V := by
  intro i j e
  rcases code_separates i j with z|z|z
  · exact z
  · exact (z (congrArg Prod.fst e)).elim
  · have g := congrArg (fun p : Bool × UT => value p.2) e
    change value (V i).2 = value (V j).2 at g
    rw [value_vert,value_vert] at g
    exact (z ((code_rows i).symm.trans ((congrArg matCode g).trans (code_rows j)))).elim

theorem step_value (i j : Fin 64) (h : rel (getRow i) (getRow j)) :
    (V j).2=(V i).2 ∨ (V j).2=(V i).2*x ∨ (V j).2=(V i).2*y := by
  rcases h with h|h|h
  · exact Or.inl (value_inj (by simpa only [value_vert] using h))
  · exact Or.inr (Or.inl (value_inj (by simpa only [value_mul,value_vert,value_x] using h)))
  · exact Or.inr (Or.inr (value_inj (by simpa only [value_mul,value_vert,value_y] using h)))

theorem cycle64 : HasCycle x y 64 := by
  apply cycle_form V vertices
  intro i
  have hs := exact_step i
  have hf := side_step i
  cases h1 : side i <;> cases h2 : side (i+1) <;> simp only [h1,h2,step,ite_true] at hs hf
  · contradiction
  · simpa [HaarCycle.haarAdj,show (V i).1=side i from rfl,
      show (V (i+1)).1=side (i+1) from rfl,h1,h2] using step_value i (i+1) hs
  · simpa [HaarCycle.haarAdj,show (V i).1=side i from rfl,
      show (V (i+1)).1=side (i+1) from rfl,h1,h2] using step_value (i+1) i hs
  · contradiction

end HaarMatrixCycle

#print axioms HaarMatrixCycle.cycle64
