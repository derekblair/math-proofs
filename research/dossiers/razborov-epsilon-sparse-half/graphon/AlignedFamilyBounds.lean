import LimitsOfBounds

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]

theorem aligned_family_upper_ae {Z : ℕ → Type*} [∀ k, MeasurableSpace (Z k)]
    (hν : mass ν=1) (g : Y→ℝ) (hg : BMeas g) (b : ℝ)
    (f : ∀ k, Z k→ℝ) (hf : ∀ k, Measurable (f k))
    (ha : ∀ ε>0, ∃ k : ℕ, ∃ π : Measure (Z k×Y),
      MeasurePreserving Prod.snd π ν ∧
      (∀ᵐ z ∂π, f k z.1≤b+ε) ∧
      Integrable (fun z=>|f k z.1-g z.2|) π ∧
      (∫ z, |f k z.1-g z.2| ∂π)≤ε) :
    ∀ᵐ y ∂ν, g y≤b := by
  apply aligned_upper_ae ν hν g hg b
  intro ε he
  obtain ⟨k,π,hp,hb,hi,hie⟩ := ha ε he
  let F : Z k×Y → ℝ×Y := fun z => (f k z.1,z.2)
  have hm : Measurable F := ((hf k).comp measurable_fst).prodMk measurable_snd
  let ρ := π.map F
  have hp' : MeasurePreserving Prod.snd ρ ν := by
    refine ⟨measurable_snd,?_⟩
    unfold ρ
    rw [Measure.map_map measurable_snd hm]
    exact hp.map_eq
  let G : ℝ×Y → ℝ := fun z => |z.1-g z.2|
  have hmG : Measurable G := continuous_abs.measurable.comp (measurable_fst.sub (hg.1.comp measurable_snd))
  have eqG : G ∘ F = fun z=>|f k z.1-g z.2| := rfl
  have Iρ : Integrable G ρ := by
    exact (integrable_map_measure hmG.aestronglyMeasurable hm.aemeasurable).mpr (eqG.symm ▸ hi)
  refine ⟨ρ,hp',?_,Iρ,?_⟩
  · apply (ae_map_iff hm.aemeasurable (measurableSet_le measurable_fst measurable_const)).mpr
    exact hb
  · have h := integral_map (μ:=π) hm.aemeasurable hmG.aestronglyMeasurable
    change (∫ z,G z ∂ρ) = _ at h
    rw [show (fun z=>G (F z)) = (fun z=>|f k z.1-g z.2|) from rfl] at h
    simpa only [G] using h.trans_le hie

#print axioms aligned_family_upper_ae
end SparseHalfGraphon
