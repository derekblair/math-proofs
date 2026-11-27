import RectangleLoads

open Set MeasureTheory SparseHalfGraphon
open scoped ENNReal
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- A finite disjoint union of independently chosen outside pools glues
to a fractional anchor fill. All profile assumptions are rectangle-a.e.;
unused parts and null cells are immaterial. -/
theorem join_rectangles {J : Type*} [Fintype J] (K : Kernel X) (A : Set X) (hA : MeasurableSet A)
    (P S : J→Set X) (hP : ∀ j, MeasurableSet (P j))
    (hD : Pairwise fun i j => Disjoint (P i) (P j)) (hOut : ∀ j, Disjoint A (P j))
    (q : J→ℝ) (hq : ∀ j,0≤q j ∧ q j≤μ.real (P j))
    (outside : ∀ i j, ∀ᵐ z ∂(μ.restrict (P i)).prod (μ.restrict (P j)), K.W z=0)
    (cross : ∀ j, ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict (P j)),
      K.W z=(S j).indicator (fun _ => (1:ℝ)) z.1)
    (anchor : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A), K.W z=0)
    (f : X→ℝ) (hf : Measurable f) (hb : ∀ x, 0≤f x ∧ f x≤1)
    (b C : ℝ) (mass_a : (∫ x,f x ∂((10:ℝ≥0∞) • μ.restrict A))=b)
    (mass_o : ∑ j,q j=(5-b)/10)
    (cost : (∫ x, (∑ j,(S j).indicator (fun _ => 10*q j) x)*f x
      ∂((10:ℝ≥0∞) • μ.restrict A))≤C) :
    ∃ H : Half μ, halfEnergy μ K H≤C/100 := by
  classical
  let e := fun j => allocSet μ (P j) (q j)
  let g := fun x => ∑ j,e j x
  have gB j := allocSet_bmeas μ (P j) (hP j) (q j) (hq j).1 (hq j).2
  have gz (j : J) (x : X) (hx : x∉P j) : e j x=0 :=
    allocSet_support μ (P j) (q j) hx
  have gm : Measurable g := by
    apply Finset.measurable_sum
    intro j _
    exact (gB j).1
  have gp (x : X) : 0≤g x ∧ g x≤1 := by
    refine ⟨Finset.sum_nonneg (fun j _ => allocSet_nn μ (P j) (q j) (hq j).1 x),?_⟩
    by_cases hmem : ∃ j, x∈P j
    · obtain ⟨j,hj⟩ := hmem
      have E : g x=e j x := by
        apply Finset.sum_eq_single j
        · intro l _ ne; exact gz l x (fun hx => Set.disjoint_left.mp (hD ne) hx hj)
        · simp
      exact E.trans_le (allocSet_le μ (P j) (q j) (hq j).2 x)
    · have E : g x=0 := Finset.sum_eq_zero fun j _ => gz j x (fun p => hmem ⟨j,p⟩)
      rw [E]; norm_num
  have gza (x : X) (hx : x∈A) : g x=0 :=
    Finset.sum_eq_zero fun j _ => gz j x (fun h => Set.disjoint_left.mp (hOut j) hx h)
  have gQ : (∫ x,g x ∂μ)=(5-b)/10 := by
    unfold g
    rw [integral_finsetSum _ (fun j _ => bMeas_integrable μ (gB j)),←mass_o]
    exact Finset.sum_congr rfl fun j _ => allocSet_mass μ (P j) (hP j) (q j) (hq j).1 (hq j).2
  have hz (i j : J) : ∀ᵐ z ∂μ.prod μ, z.1∈P i → z.2∈P j → K.W z=0 := by
    have h := outside i j
    rw [Measure.prod_restrict,ae_restrict_iff' ((hP i).prod (hP j))] at h
    exact h.mono (fun z hz hi hj => hz ⟨hi,hj⟩)
  have g0 : energyPair μ K g g=0 := by
    apply integral_eq_zero_of_ae
    have h := ae_all_iff.2 (fun i => ae_all_iff.2 (hz i))
    filter_upwards [h] with z zy
    change g z.1*g z.2*K.W z=0
    rcases em (∃ i, z.1∈P i) with ⟨i,hi⟩|hn
    · rcases em (∃ j, z.2∈P j) with ⟨j,hj⟩|hn
      · rw [zy i j hi hj,mul_zero]
      · have E : g z.2=0 := Finset.sum_eq_zero fun j _ => gz j z.2 (fun p => hn ⟨j,p⟩)
        rw [E,mul_zero,zero_mul]
    · have E : g z.1=0 := Finset.sum_eq_zero fun j _ => gz j z.1 (fun p => hn ⟨j,p⟩)
      rw [E,zero_mul,zero_mul]
  have load_eq := load_rect_sum μ (μ.restrict A) K P S hP q hq cross
  have res : ∀ᵐ x ∂μ.restrict A, load μ K g x=
      (∑ j,(S j).indicator (fun _ => 10*q j) x)/10 := by
    filter_upwards [load_eq] with x hx
    rw [hx]
    have e (j : J) : (S j).indicator (fun _ => 10*q j) x =
        10 * (S j).indicator (fun _ => q j) x := by
      by_cases hs : x∈S j <;> simp [hs]
    simp only [e,←Finset.mul_sum]
    ring
  exact join_anchor μ K A hA f g (fun x => ∑ j,(S j).indicator (fun _=>10*q j) x)
    b C hf gm hb gp gza anchor g0 mass_a gQ res cost

#print axioms join_rectangles
end SparseHalfCountableEndpoint
