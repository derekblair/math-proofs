import GeometricProjectionDerivative

namespace RobustFolkman.GeometricGap
open Set
variable {I : Type*} [Fintype I]

noncomputable def splitRadius (z : Split I) : ℝ :=
  Real.sqrt ((∑ i, splitVec z i ^ 2)+(splitRad z)^2)

noncomputable def splitPolarInv (w : Split I) : Split I :=
  Sum.elim (fun i => splitVec w i / splitRadius w) (fun _ => splitRadius w)

def splitPolarDomain : Set (Split I) := {z | 0 < splitRest z ∧ 0 < splitRad z}
def splitHalfSpace : Set (Split I) := {w | 0 < splitRad w}

@[simp] theorem splitPolar_vec (z : Split I) (i : I) :
    splitVec (splitPolar z) i = splitRad z*splitVec z i := rfl
@[simp] theorem splitPolar_rad (z : Split I) :
    splitRad (splitPolar z) = splitRad z*Real.sqrt (splitRest z) := rfl

theorem splitRadius_polar (z : Split I) (hs : 0 ≤ splitRest z) (hr : 0 ≤ splitRad z) :
    splitRadius (splitPolar z) = splitRad z := by
  unfold splitRadius
  simp only [splitPolar_vec,splitPolar_rad,mul_pow,Real.sq_sqrt hs,←Finset.mul_sum]
  rw [← mul_add]
  have c : (∑ i, splitVec z i ^ 2)+splitRest z=1 := by unfold splitRest; ring
  rw [c,mul_one,Real.sqrt_sq hr]

theorem splitPolar_left_inverse {z : Split I} (h : z ∈ (splitPolarDomain : Set (Split I))) :
    splitPolarInv (splitPolar z) = z := by
  change 0 < splitRest z ∧ 0 < splitRad z at h
  have R := splitRadius_polar z h.1.le h.2.le
  funext i
  cases i with
  | inl i =>
    change splitVec (splitPolar z) i / splitRadius (splitPolar z) = splitVec z i
    simp [R, h.2.ne', mul_comm]
  | inr u =>
    cases u
    exact R

theorem splitPolar_injOn : InjOn (splitPolar (I:=I)) splitPolarDomain :=
  fun _ hx _ hy e => by rw [← splitPolar_left_inverse hx, ← splitPolar_left_inverse hy,e]

theorem splitPolar_mapsTo : MapsTo (splitPolar (I:=I)) splitPolarDomain splitHalfSpace :=
  fun _ h => mul_pos h.2 (Real.sqrt_pos.2 h.1)

theorem splitPolar_inverse_of_positive {w : Split I} (hw : w ∈ splitHalfSpace) :
    splitPolarInv w ∈ splitPolarDomain ∧ splitPolar (splitPolarInv w) = w := by
  change 0 < splitRad w at hw
  have S : 0 ≤ ∑ i, splitVec w i^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have R0 : 0 < splitRadius w := Real.sqrt_pos.2 (by positivity)
  have R2 : splitRadius w^2=(∑ i, splitVec w i^2)+splitRad w^2 :=
    Real.sq_sqrt (by positivity)
  have RV : splitRad (splitPolarInv w)=splitRadius w := rfl
  have XV (i : I) : splitVec (splitPolarInv w) i=splitVec w i/splitRadius w := rfl
  have RT : splitRest (splitPolarInv w) = (splitRad w/splitRadius w)^2 := by
    unfold splitRest
    simp_rw [XV,div_pow,div_eq_mul_inv,← Finset.sum_mul]
    field_simp
    nlinarith only [R2]
  have RP : 0 < splitRad w/splitRadius w := div_pos hw R0
  refine ⟨⟨RT ▸ sq_pos_of_pos RP,RV ▸ R0⟩,?_⟩
  funext i
  cases i with
  | inl i =>
    change splitVec (splitPolar (splitPolarInv w)) i=splitVec w i
    rw [splitPolar_vec,RV,XV]
    field_simp
  | inr a =>
    cases a
    change splitRad (splitPolar (splitPolarInv w))=splitRad w
    rw [splitPolar_rad,RV,RT,Real.sqrt_sq RP.le]
    field_simp

theorem splitPolar_image_domain :
    splitPolar (I:=I) '' splitPolarDomain = splitHalfSpace := by
  apply Set.Subset.antisymm
  · rintro w ⟨z,hz,rfl⟩
    exact splitPolar_mapsTo hz
  · intro w hw
    obtain ⟨h,e⟩ := splitPolar_inverse_of_positive hw
    exact ⟨splitPolarInv w,h,e⟩

#print axioms splitPolar_injOn
end RobustFolkman.GeometricGap
