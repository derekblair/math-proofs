import GeometricMoment

open Finset
namespace RobustFolkman.Moment
variable {Ω I 𝕜 : Type*} [Fintype Ω] [DecidableEq I]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem mean_sum_of (p : Ω → 𝕜) (s : Finset I) (f : I → Ω → 𝕜) :
    mean p (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, mean p (f i) := by
  simp only [mean, mul_sum]
  exact Finset.sum_comm

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem mean_covariance (p : Ω → 𝕜) (p1 : (∑ ω, p ω)=1)
    (f g : Ω → 𝕜) :
    mean p (fun ω => (f ω-mean p f)*(g ω-mean p g)) =
      mean p (fun ω => f ω*g ω)-mean p f*mean p g := by
  have h : ∀ ω, p ω*((f ω-mean p f)*(g ω-mean p g)) =
      p ω*(f ω*g ω)-(p ω*f ω)*mean p g-mean p f*(p ω*g ω)+p ω*(mean p f*mean p g) := by
    intro ω
    ring
  have equiv :
      mean p (fun ω => (f ω-mean p f)*(g ω-mean p g)) =
      ∑ ω, (p ω*(f ω*g ω)-(p ω*f ω)*mean p g-mean p f*(p ω*g ω)+p ω*(mean p f*mean p g)) := by
    unfold mean at *
    exact sum_congr rfl (fun ω _ => h ω)
  rw [equiv]
  simp only [sum_add_distrib,sum_sub_distrib,←Finset.sum_mul,←Finset.mul_sum,p1,one_mul]
  change mean p (fun ω => f ω*g ω)-mean p f*mean p g-
    mean p f*mean p g+mean p f*mean p g=_
  ring

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem variance_sum_of (p : Ω → 𝕜) (p1 : (∑ ω, p ω)=1)
    (s : Finset I) (f : I → Ω → 𝕜) :
    mean p (fun ω => ((∑ i ∈ s, f i ω)-(∑ i ∈ s, mean p (f i)))^2) =
      ∑ i ∈ s, ∑ j ∈ s, (mean p (fun ω => f i ω*f j ω)-mean p (f i)*mean p (f j)) := by
  have h : ∀ ω, ((∑ i ∈ s, f i ω)-(∑ i ∈ s, mean p (f i)))^2 =
      ∑ i ∈ s, ∑ j ∈ s, ((f i ω-mean p (f i))*(f j ω-mean p (f j))) := by
    intro ω
    rw [←Finset.sum_sub_distrib, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp_rw [h, mean_sum_of, mean_covariance p p1]

/-- A homogeneous family of indicator events has variance bounded by its
size times the individual probability plus the number of exceptional
ordered pairs times the exceptional joint probability. Nonexceptional
off-diagonal pairs may be independent or negatively correlated. -/
theorem variance_indicator_upper (p : Ω → 𝕜) (p1 : (∑ ω, p ω)=1)
    (s : Finset I) (f : I → Ω → 𝕜) (μ q : 𝕜)
    (sq : ∀ i ω, f i ω*f i ω=f i ω)
    (m : ∀ i ∈ s, mean p (f i)=μ)
    (R : I → I → Prop) [DecidableRel R]
    (no : ∀ i j, i ∈ s → j ∈ s → i ≠ j → ¬ R i j →
      mean p (fun ω => f i ω*f j ω) ≤ μ^2)
    (yes : ∀ i j, i ∈ s → j ∈ s → i ≠ j → R i j →
      mean p (fun ω => f i ω*f j ω) ≤ q) :
    mean p (fun ω => ((∑ i ∈ s, f i ω)-(s.card : 𝕜)*μ)^2) ≤
      (s.card : 𝕜)*μ+∑ i ∈ s, (((s.erase i).filter (R i)).card : 𝕜)*q := by
  have center : (∑ i ∈ s, mean p (f i))=(s.card : 𝕜)*μ := by
    calc
      _ = ∑ _i ∈ s, μ := sum_congr rfl m
      _ = _ := by simp
  conv_lhs => rw [←center, variance_sum_of p p1]
  have cen2 : (s.card : 𝕜)*μ = ∑ _i ∈ s, μ := by simp
  rw [cen2, ←Finset.sum_add_distrib]
  apply sum_le_sum
  intro i hi
  have row : (∑ j ∈ s, (mean p (fun ω => f i ω*f j ω)-mean p (f i)*mean p (f j))) ≤
      ∑ j ∈ s, (if i=j then μ else if R i j then q else 0) := by
    apply sum_le_sum
    intro j hj
    rw [m i hi,m j hj]
    by_cases e : i=j
    · subst j
      rw [ite_eq_left rfl]
      simp_rw [sq i]
      rw [m i hi]
      linarith only [mul_self_nonneg μ]
    · rw [ite_eq_right e]
      by_cases r : R i j
      · rw [ite_eq_left r]
        linarith only [yes i j hi hj e r,mul_self_nonneg μ]
      · rw [ite_eq_right r]
        have h := no i j hi hj e r
        rw [pow_two] at h
        linarith only [h]
  apply row.trans
  rw [←Finset.sum_erase_add _ _ hi, ite_eq_left rfl]
  have rest :
      (∑ j ∈ s.erase i, (if i=j then μ else if R i j then q else 0)) =
        (((s.erase i).filter (R i)).card : 𝕜)*q := by
    calc
      _ = ∑ j ∈ s.erase i, (if R i j then q else 0) := by
        apply sum_congr rfl
        intro j hj
        rw [ite_eq_right (Finset.ne_of_mem_erase hj).symm]
      _ = ∑ _j ∈ (s.erase i).filter (R i), q := by rw [Finset.sum_filter]
      _ = _ := by simp
  rw [rest, add_comm]

#print axioms variance_indicator_upper
end RobustFolkman.Moment
