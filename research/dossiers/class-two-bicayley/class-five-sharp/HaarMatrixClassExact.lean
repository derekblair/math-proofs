import HaarMatrixCycle

namespace HaarMatrixClassExact
open scoped commutatorElement
open HaarMatrixFiltration HaarMatrixRows HaarMatrixCycle
def rawC2 : Mat := unflatten #[1,0,9,6,9,8,0,1,0,14,13,15,0,0,1,0,14,5,0,0,0,1,0,16,0,0,0,0,1,0,0,0,0,0,0,1]
theorem rawC2_band : Band 1 (rawC2-1) := by intro i j; fin_cases i <;> fin_cases j <;> decide
noncomputable def C2 : UT := ofMatrix rawC2 rawC2_band
theorem val_C2 : value C2 = rawC2 := value_ofMatrix _ _
def rawC3 : Mat := unflatten #[1,0,0,1,13,13,0,1,0,0,0,3,0,0,1,0,0,13,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1]
theorem rawC3_band : Band 1 (rawC3-1) := by intro i j; fin_cases i <;> fin_cases j <;> decide
noncomputable def C3 : UT := ofMatrix rawC3 rawC3_band
theorem val_C3 : value C3 = rawC3 := value_ofMatrix _ _
def rawC4 : Mat := unflatten #[1,0,0,0,1,4,0,1,0,0,0,4,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1]
theorem rawC4_band : Band 1 (rawC4-1) := by intro i j; fin_cases i <;> fin_cases j <;> decide
noncomputable def C4 : UT := ofMatrix rawC4 rawC4_band
theorem val_C4 : value C4 = rawC4 := value_ofMatrix _ _
def rawC5 : Mat := unflatten #[1,0,0,0,0,7,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1]
theorem rawC5_band : Band 1 (rawC5-1) := by intro i j; fin_cases i <;> fin_cases j <;> decide
noncomputable def C5 : UT := ofMatrix rawC5 rawC5_band
theorem val_C5 : value C5 = rawC5 := value_ofMatrix _ _

theorem comm_eq (a b c : UT) (h : value c * value b * value a = value a * value b) :
    ⁅a,b⁆ = c := by
  have eq : c*b*a=a*b := value_inj h
  calc
    ⁅a,b⁆ = (a*b) * (b*a)⁻¹ := by simp [commutatorElement_def,mul_inv_rev,mul_assoc]
    _ = c := (eq_mul_inv_iff_mul_eq.mpr (by simpa only [← mul_assoc] using eq)).symm

theorem comm2 : ⁅x,y⁆ = C2 := by
  apply comm_eq
  rw [val_C2,value_x,value_y]
  decide
theorem comm3 : ⁅C2,x⁆ = C3 := by
  apply comm_eq
  rw [val_C3,val_C2,value_x]
  decide
theorem comm4 : ⁅C3,x⁆ = C4 := by
  apply comm_eq
  rw [val_C4,val_C3,value_x]
  decide
theorem comm5 : ⁅C4,x⁆ = C5 := by
  apply comm_eq
  rw [val_C5,val_C4,value_x]
  decide

theorem C5_nonidentity : C5 ≠ 1 := by
  intro eq
  have impossible := congrArg (fun a : UT => value a 0 5) eq
  change value C5 0 5 = (1 : Mat) 0 5 at impossible
  rw [val_C5] at impossible
  exact (by decide : ¬ (rawC5 0 5 = (1 : Mat) 0 5)) impossible

theorem class_at_least_five : (⊤ : Subgroup UT).lowerCentralSeries 4 ≠ ⊥ := by
  intro h
  let T : Subgroup UT := ⊤
  have xT : x ∈ T := Subgroup.mem_top x
  have yT : y ∈ T := Subgroup.mem_top y
  have h2 : C2 ∈ T.lowerCentralSeries 1 := comm2 ▸ Subgroup.commutator_mem_commutator xT yT
  have h3 : C3 ∈ T.lowerCentralSeries 2 := comm3 ▸ Subgroup.commutator_mem_commutator h2 xT
  have h4 : C4 ∈ T.lowerCentralSeries 3 := comm4 ▸ Subgroup.commutator_mem_commutator h3 xT
  have h5 : C5 ∈ (⊤ : Subgroup UT).lowerCentralSeries 4 := comm5 ▸ Subgroup.commutator_mem_commutator h4 xT
  rw [h] at h5
  exact C5_nonidentity (Subgroup.mem_bot.mp h5)

end HaarMatrixClassExact
#print axioms HaarMatrixClassExact.class_at_least_five
