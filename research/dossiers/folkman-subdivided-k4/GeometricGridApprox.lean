import GeometricSphereGrid

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped InnerProductSpace
variable {d m : ℕ}

noncomputable def cellRepresentative (base : GridSphere d) (b : GridCode d m) : GridSphere d := by
  classical
  exact if h : ∃ x, gridCode d m x=b then h.choose else base

theorem cellRepresentative_measurable (base : GridSphere d) :
    Measurable (cellRepresentative (m:=m) base) := measurable_of_finite _

theorem gridRepresentative_dist (mp : 0<m) (base x : GridSphere d) :
    ‖(cellRepresentative base (gridCode d m x)).val-x.val‖≤Real.sqrt (d:ℝ)/(m:ℝ) := by
  classical
  let g := gridCode d m
  have h : ∃ y, g y=g x := ⟨x,rfl⟩
  unfold cellRepresentative
  rw [dif_pos h]
  exact grid_code_diameter d m mp h.choose x h.choose_spec

theorem grid_inner_error (mp : 0<m) (base x y : GridSphere d) :
    let R := cellRepresentative base ∘ gridCode d m
    |⟪(R x).val,(R y).val⟫_ℝ-⟪x.val,y.val⟫_ℝ| ≤ 2*(Real.sqrt (d:ℝ)/(m:ℝ)) := by
  intro R
  have h1 : ‖(R x).val-x.val‖≤Real.sqrt (d:ℝ)/(m:ℝ) := gridRepresentative_dist mp base x
  have h2 : ‖(R y).val-y.val‖≤Real.sqrt (d:ℝ)/(m:ℝ) := gridRepresentative_dist mp base y
  have v1 : ‖(R y).val‖=1 := by simpa using (R y).property
  have v2 : ‖x.val‖=1 := by simpa using x.property
  have e : ⟪(R x).val,(R y).val⟫_ℝ-⟪x.val,y.val⟫_ℝ =
      ⟪(R x).val-x.val,(R y).val⟫_ℝ+⟪x.val,(R y).val-y.val⟫_ℝ := by
    rw [inner_sub_left,inner_sub_right]
    ring
  rw [e]
  have a := abs_real_inner_le_norm ((R x).val-x.val) (R y).val
  have b := abs_real_inner_le_norm x.val ((R y).val-y.val)
  rw [v1,mul_one] at a
  rw [v2,one_mul] at b
  have p := abs_add_le ⟪(R x).val-x.val,(R y).val⟫_ℝ ⟪x.val,(R y).val-y.val⟫_ℝ
  linarith only [p,a,b,h1,h2]

theorem threshold_disagreement_in_strip (c a b δ : ℝ) (h : |b-a|≤δ)
    (ne : ¬(c≤a ↔ c≤b)) : a∈Icc (c-δ) (c+δ) := by
  have hl := (abs_le.mp h).1
  have hr := (abs_le.mp h).2
  by_cases aa : c≤a
  · have bb : b<c := lt_of_not_ge (fun le => ne (iff_of_true aa le))
    exact ⟨by linarith only [aa,hl,hr],by linarith only [bb,hl]⟩
  · have bb : c≤b := by by_contra! nn; exact ne (iff_of_false aa (not_le_of_gt nn))
    exact ⟨by linarith only [bb,hr],by linarith only [lt_of_not_ge aa,hl,hr]⟩

#print axioms grid_inner_error
#print axioms threshold_disagreement_in_strip
end RobustFolkman.GeometricGap
