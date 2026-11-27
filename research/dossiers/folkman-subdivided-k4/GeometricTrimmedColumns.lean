import GeometricKernelBernoulli

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset
open scoped ENNReal BigOperators
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- For two independent blocks, a uniform one-row density bound protects all
actual right columns from truncation, without fretting about unused types. -/
theorem all_column_energy_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω→Ω→ℝ) (bin : ∀ x y, K x y=0 ∨ K x y=1)
    (q p : ℝ) (q0 : 0≤q) (θ : ∀ y, μ.real {x | K x y=1}≤p)
    (n m k : ℕ) :
    let ν := Measure.pi (fun _ : Fin n => μ)
    let τ := Measure.pi (fun _ : Fin m => μ)
    (ν.prod τ) {z : (Fin n→Ω)×(Fin m→Ω) | ∃ j : Fin m,
      (n:ℝ)*q^2+(k:ℝ)<∑ i, (rightColumn (fun x y => K x y-q) z.1 (z.2 j) i)^2}
    ≤ (m:ℝ≥0∞)*ENNReal.ofReal (Real.exp (2*(n:ℝ)*p)/(2:ℝ)^k) := by
  classical
  intro ν τ
  let E : Set (Ω×Ω) := {z | K z.2 z.1=1}
  have em : MeasurableSet E := (show (E : Set (Ω×Ω)).Countable from to_countable _).measurableSet
  let S : Set (Ω×(Fin n→Ω)) :=
    {z | k≤(retained ((fun x => (z.1,x)) ⁻¹' E) z.2).card}
  have Sm : MeasurableSet S := by
    apply measurableSet_large_count (fun i => (fun z : Ω×(Fin n→Ω) => (z.1,z.2 i)) ⁻¹' E)
    intro i
    exact (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)) em
  let B := fun j : Fin m => (fun z : (Fin n→Ω)×(Fin m→Ω) => (z.2 j,z.1)) ⁻¹' S
  have b (j : Fin m) : (ν.prod τ) (B j) ≤ ENNReal.ofReal (Real.exp (2*(n:ℝ)*p)/(2:ℝ)^k) := by
    have jP : MeasurePreserving (fun z : Fin m→Ω => z j) τ μ := measurePreserving_eval _ j
    have P : MeasurePreserving (fun z : (Fin n→Ω)×(Fin m→Ω) => (z.2 j,z.1))
        (ν.prod τ) (μ.prod ν) :=
      (jP.prod (MeasurePreserving.id ν)).comp Measure.measurePreserving_swap
    change (ν.prod τ) ((fun z : (Fin n→Ω)×(Fin m→Ω) => (z.2 j,z.1)) ⁻¹' S) ≤ _
    rw [P.measure_preimage Sm.nullMeasurableSet]
    exact (by simpa only [Fintype.card_fin] using (conditional_row_tail (I:=Fin n) μ E em p θ k))
  have incl :
      {z : (Fin n→Ω)×(Fin m→Ω) | ∃ j : Fin m,
        (n:ℝ)*q^2+(k:ℝ)<∑ i, (rightColumn (fun x y => K x y-q) z.1 (z.2 j) i)^2}
      ⊆ ⋃ j ∈ (Finset.univ : Finset (Fin m)), B j := by
    intro z hz
    obtain ⟨j,hj⟩ := hz
    have hs := bernoulli_column_square_le K bin q q0 z.1 (z.2 j)
    have he : familyRetained (fun i => {a : Ω | K (z.1 i) a=1}) (z.2 j) =
      retained ((fun x => (z.2 j,x)) ⁻¹' E) z.1 := by
      ext i
      simp [familyRetained, retained,E]
    rw [he,Fintype.card_fin] at hs
    have hh : (k:ℝ)≤((retained ((fun x => (z.2 j,x)) ⁻¹' E) z.1).card:ℝ) := by
      linarith only [hj,hs]
    exact Set.mem_iUnion.2 ⟨j,Set.mem_iUnion.2 ⟨Finset.mem_univ _,by exact_mod_cast hh⟩⟩
  calc
    _ ≤ (ν.prod τ) (⋃ j ∈ (Finset.univ : Finset (Fin m)), B j) := measure_mono incl
    _ ≤ ∑ j : Fin m, (ν.prod τ) (B j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j : Fin m, ENNReal.ofReal (Real.exp (2*(n:ℝ)*p)/(2:ℝ)^k) :=
      Finset.sum_le_sum fun j _ => b j
    _ = _ := by simp [nsmul_eq_mul]

#print axioms all_column_energy_tail
end RobustFolkman.GeometricGap
