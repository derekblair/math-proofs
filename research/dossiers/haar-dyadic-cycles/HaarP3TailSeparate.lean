import HaarP3FifthCertCycle
import HaarClass5P3MetaCycle

namespace HaarP3TailSeparate
open HaarP3FifthCert HaarP3CollectCore HaarP3CollectActions HaarP3CollectSteps
variable {G G2 G3 G4 : Type*} [Group G] [Group G2] [Group G3] [Group G4]

theorem separates (M : Model G) (φ₂ : G →* G2) (φ₃ : G →* G3) (φ₄ : G →* G4)
    (U₂ : φ₂ M.U=1) (A₂ : φ₂ M.A=1) (Z₂ : φ₂ M.Z=1)
    (CX₂ : Commute (φ₂ M.C) (φ₂ M.x)) (CY₂ : Commute (φ₂ M.C) (φ₂ M.y))
    (O₂ : 3∣orderOf (φ₂ M.C)) (A₃ : φ₃ M.A=1) (Z₃ : φ₃ M.Z=1)
    (O₃ : 3∣orderOf (φ₃ M.U)) (Z₄ : φ₄ M.Z=1)
    (O₄ : 3∣orderOf (φ₄ M.A)) (OZ : 3∣orderOf M.Z) :
    Separates M := by
  intro r s sr ss he
  have p₂ (t : Grid) : φ₂ (ev M t)=
      HaarCycle.norm (φ₂ M.x) (φ₂ M.y) (φ₂ M.C) (t.i,t.j,t.n.k) := by
    simp [ev,ne,HaarCycle.norm,U₂,A₂,Z₂]
  have e₂ := (p₂ r).symm.trans ((congrArg φ₂ he).trans (p₂ s))
  have xy₂ : φ₂ M.x*φ₂ M.y = φ₂ M.y*φ₂ M.x*φ₂ M.C := by
    simpa only [map_mul] using congrArg φ₂ M.xy
  obtain ⟨hi,hj⟩ := HaarBound16.conjugate_eq _ _ _ CX₂ CY₂ xy₂ e₂
  refine ⟨HaarClass5P3Meta.mob _ O₂ hi,HaarClass5P3Meta.mob _ O₂ hj,?_,?_⟩
  · intro i j
    change (φ₂ M.y)^r.j*(φ₂ M.x)^r.i*(φ₂ M.C)^r.n.k =
      (φ₂ M.y)^s.j*(φ₂ M.x)^s.i*(φ₂ M.C)^s.n.k at e₂
    rw [i,j] at e₂
    exact HaarClass5P3Meta.mob _ O₂ (mul_left_cancel e₂)
  · intro i j k
    simp only [ev,ne] at he
    rw [i,j,k] at he
    have T : M.U^r.n.u*M.A^r.n.a*M.Z^r.n.z=M.U^s.n.u*M.A^s.n.a*M.Z^s.n.z := by
      simp only [mul_assoc] at he ⊢
      exact mul_left_cancel (mul_left_cancel (mul_left_cancel he))
    have Ue : (φ₃ M.U)^r.n.u=(φ₃ M.U)^s.n.u := by
      simpa [A₃,Z₃] using congrArg φ₃ T
    have Um := HaarClass5P3Meta.mob _ O₃ Ue
    have Ueq : r.n.u=s.n.u := by have := sr.1; have := ss.1; omega
    rw [Ueq] at T
    have T₁ : M.A^r.n.a*M.Z^r.n.z=M.A^s.n.a*M.Z^s.n.z := by
      simp only [mul_assoc] at T
      exact mul_left_cancel T
    have Ae : (φ₄ M.A)^r.n.a=(φ₄ M.A)^s.n.a := by
      simpa [Z₄] using congrArg φ₄ T₁
    have Am := HaarClass5P3Meta.mob _ O₄ Ae
    have Aeq : r.n.a=s.n.a := by have := sr.2.1; have := ss.2.1; omega
    rw [Aeq] at T₁
    have Ze := mul_left_cancel T₁
    have Zm := HaarClass5P3Meta.mob _ OZ Ze
    have Zeq : r.n.z=s.n.z := by have := sr.2.2; have := ss.2.2; omega
    exact ⟨Ueq,Aeq,Zeq⟩

end HaarP3TailSeparate
#print axioms HaarP3TailSeparate.separates
