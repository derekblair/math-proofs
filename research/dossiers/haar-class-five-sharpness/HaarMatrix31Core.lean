import HaarMatrix31Filtration

namespace HaarMatrix31Core
open HaarMatrix31Filtration

abbrev UT := upper 1
def value (g : UT) : Mat := (g.val:Mat)
theorem value_inj : Function.Injective value := fun _ _ h => Subtype.ext (Units.ext h)
theorem value_mul (a b : UT) : value (a*b)=value a * value b := rfl

def unflatten (a : Array ℕ) : Mat := fun i j => (a[i.val*6+j.val]! : ZMod 31)
def rawX : Mat := unflatten #[1,14,0,0,0,0,0,1,22,0,0,0,0,0,1,19,0,0,0,0,0,1,2,0,0,0,0,0,1,14,0,0,0,0,0,1]
def rawY : Mat := unflatten #[1,28,0,0,0,0,0,1,11,0,0,0,0,0,1,15,0,0,0,0,0,1,24,0,0,0,0,0,1,13,0,0,0,0,0,1]
theorem gen_band : Band 1 (rawX-1) ∧ Band 1 (rawY-1) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> decide
noncomputable def ofMatrix (A : Mat) (h : Band 1 (A-1)) : UT := by
  have e : IsUnit A := by simpa only [add_sub_cancel] using unit_add h
  exact ⟨e.unit,by change Band 1 ((e.unit:Mat)-1); rw [e.unit_spec]; exact h⟩

theorem value_ofMatrix (A : Mat) (h : Band 1 (A-1)) : value (ofMatrix A h)=A := by
  unfold ofMatrix value
  exact IsUnit.unit_spec _

noncomputable def x : UT := ofMatrix rawX gen_band.1
noncomputable def y : UT := ofMatrix rawY gen_band.2
theorem value_x : value x=rawX := value_ofMatrix _ _
theorem value_y : value y=rawY := value_ofMatrix _ _

theorem distinct : x≠1 ∧ y≠1 ∧ x≠y := by
  constructor
  · intro h
    have e := congrArg (fun g : UT => value g 0 1) h
    change value x 0 1 = (1 : Mat) 0 1 at e
    rw [value_x] at e
    exact (by decide : ¬ rawX 0 1=(1 : Mat) 0 1) e
  constructor
  · intro h
    have e := congrArg (fun g : UT => value g 0 1) h
    change value y 0 1 = (1 : Mat) 0 1 at e
    rw [value_y] at e
    exact (by decide : ¬ rawY 0 1=(1 : Mat) 0 1) e
  · intro h
    have e := congrArg (fun g : UT => value g 0 1) h
    change value x 0 1 = value y 0 1 at e
    rw [value_x,value_y] at e
    exact (by decide : ¬ rawX 0 1=rawY 0 1) e
end HaarMatrix31Core
