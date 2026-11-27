import ReweightedEnergy

open MeasureTheory Set

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]

def BMeas (f : X→ℝ) : Prop := Measurable f ∧ ∃ C : ℝ, ∀ x, |f x|≤C

lemma BMeas.of_unit {f : X→ℝ} (h : Measurable f)
    (h0 : ∀ x, 0≤f x) (h1 : ∀ x, f x≤1) : BMeas f :=
  ⟨h,1,fun x => by simpa [abs_of_nonneg (h0 x)] using h1 x⟩

lemma BMeas.add {f g : X→ℝ} (hf : BMeas f) (hg : BMeas g) : BMeas (f+g) := by
  obtain ⟨hf,A,hA⟩ := hf
  obtain ⟨hg,B,hB⟩ := hg
  exact ⟨hf.add hg,A+B,fun x => (abs_add_le _ _).trans (add_le_add (hA x) (hB x))⟩

lemma BMeas.scale {f : X→ℝ} (hf : BMeas f) (c : ℝ) : BMeas (fun x => c*f x) := by
  obtain ⟨hf,A,hA⟩ := hf
  exact ⟨measurable_const.mul hf,|c| *A,fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg c)⟩

variable (μ : Measure X) [IsFiniteMeasure μ]

lemma bMeas_integrable {f : X→ℝ} (hf : BMeas f) : Integrable f μ := by
  obtain ⟨h,C,hC⟩ := hf
  exact Integrable.of_bound h.aestronglyMeasurable C
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hC x))

lemma energy_integrable (K : Kernel X) {f g : X→ℝ} (hf : BMeas f) (hg : BMeas g) :
    Integrable (fun z : X×X => f z.1*g z.2*K.W z) (μ.prod μ) := by
  obtain ⟨hf,A,hA⟩ := hf
  obtain ⟨hg,B,hB⟩ := hg
  have h : Measurable (fun z : X×X => f z.1*g z.2*K.W z) :=
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).mul K.measurable_W
  apply Integrable.of_bound h.aestronglyMeasurable (|A| *|B|)
  apply ae_of_all
  intro z
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (K.nonneg z)]
  have hs := mul_le_mul ((hA z.1).trans (le_abs_self A)) ((hB z.2).trans (le_abs_self B))
    (abs_nonneg _) (abs_nonneg _)
  exact (mul_le_mul_of_nonneg_right hs (K.nonneg z)).trans
    (by simpa using mul_le_mul_of_nonneg_left (K.le_one z) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))

theorem energy_symm (K : Kernel X) (f g : X→ℝ) :
    energyPair μ K f g=energyPair μ K g f := by
  unfold energyPair
  rw [← integral_prod_swap (fun z : X×X => g z.1*f z.2*K.W z)]
  apply integral_congr_ae
  apply ae_of_all
  rintro ⟨x,y⟩
  change f x*g y*K.W (x,y) = g y*f x*K.W (y,x)
  rw [K.symm x y]
  ring

theorem energy_add_left (K : Kernel X) (f g h : X→ℝ)
    (hf : BMeas f) (hg : BMeas g) (hh : BMeas h) :
    energyPair μ K (f+g) h=energyPair μ K f h+energyPair μ K g h := by
  unfold energyPair
  rw [← integral_add (energy_integrable μ K hf hh) (energy_integrable μ K hg hh)]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by change (f z.1+g z.1)*h z.2*K.W z = _; ring)

theorem energy_add_right (K : Kernel X) (f g h : X→ℝ)
    (hf : BMeas f) (hg : BMeas g) (hh : BMeas h) :
    energyPair μ K f (g+h)=energyPair μ K f g+energyPair μ K f h := by
  rw [energy_symm μ K f (g+h), energy_add_left μ K g h f hg hh hf,
    energy_symm μ K g f,energy_symm μ K h f]

omit [IsFiniteMeasure μ] in
theorem energy_scale_left (K : Kernel X) (f g : X→ℝ) (a : ℝ) :
    energyPair μ K (fun x => a*f x) g=a*energyPair μ K f g := by
  unfold energyPair
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by ring)

theorem energy_scale_right (K : Kernel X) (f g : X→ℝ) (a : ℝ) :
    energyPair μ K f (fun x => a*g x)=a*energyPair μ K f g := by
  rw [energy_symm μ K f (fun x=>a*g x),energy_scale_left,energy_symm μ K g f]

theorem energy_cross_bound (K : Kernel X) (f g : X→ℝ) (hf : BMeas f) (hg : BMeas g)
    (hnf : ∀ x, 0≤f x) (hng : ∀ x, 0≤g x) :
    energyPair μ K f g≤(∫ x, f x ∂μ)*(∫ x, g x ∂μ) := by
  rw [← integral_prod_mul]
  apply integral_mono (energy_integrable μ K hf hg)
    ((bMeas_integrable μ hf).mul_prod (bMeas_integrable μ hg))
  intro z
  exact (mul_le_mul_of_nonneg_left (K.le_one z) (mul_nonneg (hnf _) (hng _))).trans (by simp)

theorem halfEnergy_as_pair (K : Kernel X) (H : Half μ) :
    halfEnergy μ K H=energyPair μ K H.f H.f/2 := by
  have h := BMeas.of_unit H.measurable_f H.nn H.le_one
  unfold halfEnergy energyPair
  rw [integral_prod_symm _ (energy_integrable μ K h h)]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro y
  change (∫ x, K.W (x,y)*H.f x ∂μ)*H.f y =
    ∫ x, H.f x*H.f y*K.W (x,y) ∂μ
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by ring)

#print axioms energy_add_left
#print axioms energy_cross_bound
#print axioms halfEnergy_as_pair
end SparseHalfGraphon
