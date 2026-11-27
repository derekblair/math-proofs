import GraphonCaseTwoAverage

open MeasureTheory Set
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]
variable (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

lemma BMeas.mul {f g : X→ℝ} (hf : BMeas f) (hg : BMeas g) : BMeas (f*g) := by
  obtain ⟨hf,A,hA⟩ := hf
  obtain ⟨hg,B,hB⟩ := hg
  refine ⟨hf.mul hg,|A| * |B|,?_⟩
  intro x
  change |f x*g x|≤_
  rw [abs_mul]
  exact mul_le_mul ((hA x).trans (le_abs_self A)) ((hB x).trans (le_abs_self B))
    (abs_nonneg _) (abs_nonneg _)

lemma BMeas.sub {f g : X→ℝ} (hf : BMeas f) (hg : BMeas g) : BMeas (f-g) := by
  have hn := hg.scale (-1)
  convert hf.add hn using 1
  ext x
  change f x-g x=f x+(-1)*g x
  ring

lemma BMeas.const (c : ℝ) : BMeas (fun _ : X => c) :=
  ⟨measurable_const,|c|,fun _ => le_rfl⟩

lemma deg_bmeas (K : Kernel X) : BMeas (deg ν K) :=
  ⟨deg_measurable ν K,mass ν,fun x => by
    rw [abs_of_nonneg (deg_nonneg ν K x)]; exact deg_le_mass ν K x⟩

noncomputable def load (K : Kernel X) (D : X→ℝ) (v : X) :=
  ∫ x, D x*K.W (v,x) ∂μ

lemma load_bmeas (K : Kernel X) {D : X→ℝ} (hD : BMeas D) : BMeas (load μ K D) := by
  obtain ⟨hm,C,hC⟩ := hD
  refine ⟨?_, mass μ * |C|,?_⟩
  · exact (((hm.comp measurable_snd).mul K.measurable_W).stronglyMeasurable.integral_prod_right').measurable
  · intro v
    have hh : Integrable (fun x => D x*K.W (v,x)) μ := by
      apply Integrable.of_bound (hm.mul (rowMeasurable K v)).aestronglyMeasurable |C|
      apply ae_of_all
      intro x
      change ‖D x*K.W (v,x)‖≤|C|
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (K.nonneg (v,x))]
      exact (mul_le_mul_of_nonneg_right ((hC x).trans (le_abs_self C)) (K.nonneg _)).trans
        (by simpa using mul_le_mul_of_nonneg_left (K.le_one (v,x)) (abs_nonneg C))
    calc
      |load μ K D v| ≤ ∫ x, |D x*K.W (v,x)| ∂μ := by
        simpa only [load,Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ:=μ) (f:=fun x => D x*K.W (v,x)))
      _ ≤ mass μ*|C| := by
        have h := integral_mono hh.abs (integrable_const (μ:=μ) |C|) (fun x => by
          rw [abs_mul,abs_of_nonneg (K.nonneg (v,x))]
          exact (mul_le_mul_of_nonneg_right ((hC x).trans (le_abs_self C)) (K.nonneg _)).trans
            (by simpa using mul_le_mul_of_nonneg_left (K.le_one (v,x)) (abs_nonneg C)))
        simpa [integral_const,mass,smul_eq_mul] using h

/-- Exact Fubini rule when the anchor and allocation measures are distinct. -/
theorem load_marginal (K : Kernel X) (D : X→ℝ) (hD : BMeas D) :
    (∫ v, load μ K D v ∂ν)=∫ x, D x*deg ν K x ∂μ := by
  let F : X×X→ℝ := fun z => D z.2*K.W z
  obtain ⟨hm,C,hC⟩ := hD
  have hi : Integrable F (ν.prod μ) := by
    apply Integrable.of_bound ((hm.comp measurable_snd).mul K.measurable_W).aestronglyMeasurable |C|
    apply ae_of_all
    intro z
    change ‖D z.2*K.W z‖≤_
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (K.nonneg z)]
    exact (mul_le_mul_of_nonneg_right ((hC z.2).trans (le_abs_self C)) (K.nonneg _)).trans
      (by simpa using mul_le_mul_of_nonneg_left (K.le_one z) (abs_nonneg C))
  change (∫ v, ∫ x, F (v,x) ∂μ ∂ν)=_
  rw [← integral_prod F hi,integral_prod_symm F hi]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change (∫ v, D x*K.W (v,x) ∂ν)=D x*deg ν K x
  rw [integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun v => K.symm v x)

noncomputable def deficit (K : Kernel X) (x : X) : ℝ := 1/5-deg ν K x
noncomputable def rem (K : Kernel X) (D : X→ℝ) (v : X) : ℝ := 1/10-load μ K D v
noncomputable def defMass (K : Kernel X) (D : X→ℝ) : ℝ :=
  ∫ x, D x*deficit ν K x ∂μ
noncomputable def rowDef (K : Kernel X) (D : X→ℝ) (v : X) : ℝ :=
  load μ K (D * deficit ν K) v

theorem rem_exact (K : Kernel X) (D:X→ℝ) (hD:BMeas D)
    (hν:mass ν=2/5) (hm:(∫ x, D x ∂μ)=1/5) :
    (∫ v, rem μ K D v ∂ν)=defMass μ ν K D := by
  unfold rem defMass deficit
  rw [integral_sub (integrable_const _) (bMeas_integrable ν (load_bmeas μ K hD)),
    integral_const,load_marginal μ ν K D hD]
  have he : (fun x => D x*(1/5-deg ν K x))=
    fun x => D x*(1/5)-D x*deg ν K x := by funext x; ring
  have hi : Integrable (fun x => D x*deg ν K x) μ :=
    bMeas_integrable μ (hD.mul (deg_bmeas ν K))
  rw [he,integral_sub ((bMeas_integrable μ hD).mul_const (1/5))
    hi,integral_mul_const,hm]
  change mass ν*(1/10)-_ = _
  rw [hν]
  ring

theorem row_def_integral (K : Kernel X) (D:X→ℝ) (hD:BMeas D) :
    (∫ v, rowDef μ ν K D v ∂ν) =
    (1/5)*defMass μ ν K D-∫ x, D x*(deficit ν K x)^2 ∂μ := by
  have hδ : BMeas (deficit ν K) := (BMeas.const (1/5)).sub (deg_bmeas ν K)
  have hDδ := hD.mul hδ
  unfold rowDef defMass
  rw [load_marginal μ ν K (D*deficit ν K) hDδ,← integral_const_mul]
  have hi₁ : Integrable (fun x => (1/5)*(D x*deficit ν K x)) μ :=
    (bMeas_integrable μ hDδ).const_mul _
  have hi₂ : Integrable (fun x=>D x*(deficit ν K x)^2) μ :=
    bMeas_integrable μ (hD.mul hδ.sq)
  rw [← integral_sub hi₁ hi₂]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by change D x * deficit ν K x * deg ν K x = _; unfold deficit; ring)

#print axioms rem_exact
#print axioms row_def_integral
end SparseHalfGraphon
