import ProfileUniqueness
import ComplementRowsAE

open Set MeasureTheory Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]
variable (ω ν : Measure X) [IsFiniteMeasure ω] [IsFiniteMeasure ν]

/-- Restrict to the positive-mass row codes without losing any of the
nonzero kernel edges whose marked-side profiles complement each other. -/
theorem complemented_edges_atomic (K : Kernel X) (T : ℕ → Set X)
    (h : ∀ᵐ z ∂ω.prod ω, K.W z=0 ∨
      ∀ᵐ y ∂ν, (K.W (z.1,y)=0 ∧ K.W (z.2,y)=1) ∨
        (K.W (z.1,y)=1 ∧ K.W (z.2,y)=0)) :
    ∃ C : Set (ℕ→ℝ), C.Countable ∧
      ∀ᵐ z ∂ω.prod ω, K.W z=0 ∨
        (profileCode ν T K z.1 ∈ C ∧ profileCode ν T K z.2 ∈ C ∧
          profileCode ν T K z.2 = codeFlip ν T (profileCode ν T K z.1)) := by
  let p := profileCode ν T K
  let C := codeFlip ν T
  have hp : Measurable p := profileCode_meas ν T K
  have hc : Measurable C := codeFlip_meas ν T
  have hx : MeasurableSet {z : X×X | p z.2=C (p z.1)} :=
    measurableSet_eq_fun (hp.comp measurable_snd) (hc.comp (hp.comp measurable_fst))
  have ha := relation_on_atoms ω p hp C hx
  have hswap := (Measure.measurePreserving_swap (μ:=ω) (ν:=ω)).quasiMeasurePreserving.ae ha
  refine ⟨atomLabels ω p,atomLabels_countable ω p hp,?_⟩
  filter_upwards [h,ha,hswap] with z hz h1 h2
  rcases hz with hz | hz
  · exact Or.inl hz
  · right
    have he : p z.2=C (p z.1) := indicator_rows_codes ν T K z.1 z.2 hz
    have hf : p z.1=C (p z.2) := by rw [he]; exact (codeFlip_inv ν T _).symm
    have h2' : p z.1=C (p z.2) → p z.1 ∈ atomLabels ω p := h2
    exact ⟨h2' hf,h1 he,he⟩

/-- If a nonnull anchor distinguishes rows, a genuinely complementary
indicator pair cannot be a fixed point of the profile involution. -/
theorem complementary_codes_distinct {mx : MeasurableSpace X}
    (ν' : @Measure X mx) [IsFiniteMeasure ν'] (hmass : ν' univ ≠ 0)
    (T : ℕ → Set X) (K : @Kernel X mx)
    (hm : ∀ n, MeasurableSet (T n))
    (hg : mx=MeasurableSpace.generateFrom (range T))
    (hpi : IsPiSystem (range T)) (hu : univ∈range T) (x y:X)
    (h : ∀ᵐ z ∂ν', (K.W (x,z)=0 ∧ K.W (y,z)=1) ∨ (K.W (x,z)=1 ∧ K.W (y,z)=0)) :
    profileCode ν' T K x ≠ profileCode ν' T K y := by
  intro he
  have hEq := profile_code_injective_ae ν' T K hm hg hpi hu x y he
  have hno : ∀ᵐ z ∂ν', False := by
    filter_upwards [hEq,h] with z hz hr
    rcases hr with ⟨hr₁,hr₂⟩ | ⟨hr₁,hr₂⟩ <;> simp [hr₁,hr₂] at hz
  exact hmass (by simpa only [ae_iff, not_false_eq_true, setOf_true] using hno)

#print axioms complemented_edges_atomic
#print axioms complementary_codes_distinct
end SparseHalfGraphon
