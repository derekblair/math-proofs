import Ribbon5UT

namespace Ribbon5UT
open HaarMatrixFiltration HaarMatrixRows HaarMatrixCycle
open scoped commutatorElement

private theorem band_local (m : Mat) : Band 1 (upperize m-1) := by
  intro i j h
  by_cases e : i=j
  · subst j
    simp [upperize,Matrix.sub_apply]
  · have l : ¬i<j := by
      change ¬ i.val < j.val
      omega
    simp [upperize,Matrix.sub_apply,e,l]

def rawC2 : Mat := upperize (unflatten #[1,0,0,0,0,0,0,1,0,5,9,9,0,0,1,0,9,4,0,0,0,1,0,4,0,0,0,0,1,0,0,0,0,0,0,1])
noncomputable def C2 : UT := ofMatrix rawC2 (band_local _)
theorem val_C2 : value C2=rawC2 := value_ofMatrix _ _
def rawC3 : Mat := upperize (unflatten #[1,0,0,14,11,1,0,1,0,0,14,0,0,0,1,0,0,13,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1])
noncomputable def C3 : UT := ofMatrix rawC3 (band_local _)
theorem val_C3 : value C3=rawC3 := value_ofMatrix _ _
def rawC4 : Mat := upperize (unflatten #[1,0,0,0,16,16,0,1,0,0,0,12,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1])
noncomputable def C4 : UT := ofMatrix rawC4 (band_local _)
theorem val_C4 : value C4=rawC4 := value_ofMatrix _ _
def rawC5 : Mat := upperize (unflatten #[1,0,0,0,0,13,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1])
noncomputable def C5 : UT := ofMatrix rawC5 (band_local _)
theorem val_C5 : value C5=rawC5 := value_ofMatrix _ _

theorem comm2 : ⁅a,b⁆ = C2 := by
  apply HaarMatrixClassExact.comm_eq
  rw [val_C2,val_a,val_b]
  decide +kernel

theorem comm3 : ⁅C2,a⁆ = C3 := by
  apply HaarMatrixClassExact.comm_eq
  rw [val_C3,val_C2,val_a]
  decide +kernel

theorem comm4 : ⁅C3,a⁆ = C4 := by
  apply HaarMatrixClassExact.comm_eq
  rw [val_C4,val_C3,val_a]
  decide +kernel

theorem comm5 : ⁅C4,a⁆ = C5 := by
  apply HaarMatrixClassExact.comm_eq
  rw [val_C5,val_C4,val_a]
  decide +kernel

theorem pair_fifth_nontrivial : ⁅⁅⁅⁅a,b⁆,a⁆,a⁆,a⁆ ≠ 1 := by
  rw [comm2,comm3,comm4,comm5]
  intro eq
  have h := congrArg (fun v : UT => value v 0 5) eq
  change value C5 0 5 = (1:Mat) 0 5 at h
  rw [val_C5] at h
  exact (by decide : rawC5 0 5 ≠ (1:Mat) 0 5) h

theorem ports_not_involutions : a*a≠1 ∧ b*b≠1 := by
  constructor
  · intro h
    have e := congrArg value h
    change value (a*a)=(1:Mat) at e
    rw [value_mul,val_a] at e
    exact (by decide : rawA*rawA≠(1:Mat)) e
  · intro h
    have e := congrArg value h
    change value (b*b)=(1:Mat) at e
    rw [value_mul,val_b] at e
    exact (by decide : rawB*rawB≠(1:Mat)) e

end Ribbon5UT
#print axioms Ribbon5UT.pair_fifth_nontrivial
