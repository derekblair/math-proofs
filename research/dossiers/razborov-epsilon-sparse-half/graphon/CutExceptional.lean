import CouplingCut
import CutBinaryTemplate

open MeasureTheory Set Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma gap_integrable (K J : Kernel X) : Integrable (gapW K J) (μ.prod μ) :=
  (integrable_bounded _ K.measurable_W K.nonneg K.le_one).sub
    (integrable_bounded _ J.measurable_W J.nonneg J.le_one)

theorem L1_imp_cut (K J : Kernel X) (ε : ℝ)
    (h : (∫ z, |gapW K J z| ∂μ.prod μ)≤ε) : CutBound μ K J ε := by
  intro S T hS hT
  have hb := (gap_integrable μ K J).integrableOn (s:=S×ˢT)
  have he := setIntegral_prod (gapW K J) hb
  change |∫ x in S, ∫ y in T, gapW K J (x,y) ∂μ ∂μ|≤ε
  rw [← he]
  have hnorm : |∫ z in S×ˢT, gapW K J z ∂μ.prod μ|≤
      ∫ z in S×ˢT, |gapW K J z| ∂μ.prod μ := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ:=(μ.prod μ).restrict (S×ˢT)) (f:=gapW K J)
  have hpos : 0 ≤ᵐ[μ.prod μ] fun z=>|gapW K J z| := ae_of_all _ (fun _=>abs_nonneg _)
  have hle := integral_mono_measure (Measure.restrict_le_self (s:=S×ˢT)) hpos (gap_integrable μ K J).abs
  exact hnorm.trans (hle.trans h)

theorem cut_tri (K J L : Kernel X) (ε δ : ℝ)
    (h₁ : CutBound μ K J ε) (h₂ : CutBound μ J L δ) : CutBound μ K L (ε+δ) := by
  intro S T hS hT
  have he (V W:Kernel X) : (∫ x in S, ∫ y in T, gapW V W (x,y) ∂μ ∂μ)=
      ∫ z in S×ˢT, gapW V W z ∂μ.prod μ :=
    (setIntegral_prod _ (gap_integrable μ V W).integrableOn).symm
  have hV := h₁ S T hS hT
  have hW := h₂ S T hS hT
  change |∫ x in S, ∫ y in T, gapW K J (x,y) ∂μ ∂μ|≤ε at hV
  change |∫ x in S, ∫ y in T, gapW J L (x,y) ∂μ ∂μ|≤δ at hW
  change |∫ x in S, ∫ y in T, gapW K L (x,y) ∂μ ∂μ|≤ε+δ
  rw [he K J] at hV
  rw [he J L] at hW
  rw [he K L]
  have hf : gapW K L=fun z=>gapW K J z+gapW J L z := by
    funext z; unfold gapW; ring
  rw [hf,integral_add (gap_integrable μ K J).integrableOn (gap_integrable μ J L).integrableOn]
  exact (abs_add_le _ _).trans (add_le_add hV hW)

/-- Small exceptional vertex mass gives explicit aligned cut control.
Only pairs of good vertices require pointwise approximation. -/
theorem exceptional_vertex_cut (K J : Kernel X) (B : Set X) (hB : MeasurableSet B)
    (hμ : mass μ=1) (ε : ℝ) (hε : 0≤ε)
    (hgood : ∀ x y, x∉B → y∉B → |gapW K J (x,y)|≤ε) :
    CutBound μ K J (ε+2*μ.real B) := by
  let b : X→ℝ := B.indicator (fun _=>(1:ℝ))
  have hb : Measurable b := measurable_const.indicator hB
  have hn x : 0≤b x := by by_cases hx:x∈B <;> simp [b,hx]
  have h1 x : b x≤1 := by by_cases hx:x∈B <;> simp [b,hx]
  have bi := integrable_bounded μ hb hn h1
  have he (z:X×X) : |gapW K J z|≤ε+b z.1+b z.2 := by
    rcases z with ⟨x,y⟩
    by_cases hx:x∈B
    · have hb₁ : b x=1 := by simp [b,hx]
      exact (gapW_bound K J (x,y)).trans (by dsimp; rw [hb₁]; linarith [hn y])
    · by_cases hy:y∈B
      · have hb₁ : b y=1 := by simp [b,hy]
        exact (gapW_bound K J (x,y)).trans (by dsimp; rw [hb₁]; linarith [hn x])
      · linarith [hgood x y hx hy,hn x,hn y]
  have hI₁ : Integrable (fun z : X×X => b z.1) (μ.prod μ) :=
    integrable_bounded _ (hb.comp measurable_fst) (fun _=>hn _) (fun _=>h1 _)
  have hI₂ : Integrable (fun z : X×X => b z.2) (μ.prod μ) :=
    integrable_bounded _ (hb.comp measurable_snd) (fun _=>hn _) (fun _=>h1 _)
  have hI₃ : Integrable (fun z : X×X => ε+b z.1) (μ.prod μ) :=
    (integrable_const _).add hI₁
  have hl := integral_mono (gap_integrable μ K J).abs (hI₃.add hI₂) he
  have hmass : mass (μ.prod μ)=1 := by
    unfold mass
    rw [← Set.univ_prod_univ,measureReal_prod_prod]
    change mass μ*mass μ=1
    simp [hμ]
  have hs₁ : (∫ z : X×X, b z.1 ∂μ.prod μ)=μ.real B := by
    rw [integral_prod _ hI₁]
    have hu : μ.real univ=1 := hμ
    simp only [integral_const,smul_eq_mul,hu,one_mul]
    simpa [b,smul_eq_mul] using
      (integral_indicator_const (μ:=μ) (1:ℝ) hB)
  have hs₂ : (∫ z : X×X, b z.2 ∂μ.prod μ)=μ.real B := by
    rw [integral_prod_symm _ hI₂]
    have hu : μ.real univ=1 := hμ
    simp only [integral_const,smul_eq_mul,hu,one_mul]
    simpa [b,smul_eq_mul] using
      (integral_indicator_const (μ:=μ) (1:ℝ) hB)
  change (∫ z, |gapW K J z| ∂μ.prod μ)≤∫ z : X×X, ε+b z.1+b z.2 ∂μ.prod μ at hl
  rw [integral_add hI₃ hI₂,integral_add (integrable_const _) hI₁,integral_const,
    hs₁,hs₂,smul_eq_mul] at hl
  change _≤mass (μ.prod μ)*ε+μ.real B+μ.real B at hl
  rw [hmass,one_mul] at hl
  exact L1_imp_cut μ K J _ (hl.trans (by linarith))

#print axioms cut_tri
#print axioms exceptional_vertex_cut
end SparseHalfGraphon
