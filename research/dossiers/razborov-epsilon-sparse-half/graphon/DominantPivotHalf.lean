import OutsideGreedyModel
import DominantPivot
import RestrictedAllocations
import StrictAnchorHalf

open Set MeasureTheory Function Filter
open SparseHalfCountableEndpoint
namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma pivotEnergy_zero (K : Kernel X) (S : Set X) (f : X→ℝ)
    (off : ∀ x∉S, f x=0)
    (ind : ∀ᵐ z ∂μ.prod μ, z.1∈S → z.2∈S → K.W z=0) :
    energyPair μ K f f=0 := by
  unfold energyPair
  calc
    _ = ∫ _ : X×X, (0:ℝ) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [ind] with z hz
      by_cases x : z.1∈S
      · by_cases y : z.2∈S
        · simp [hz x y]
        · simp [off _ y]
      · simp [off _ x]
    _ = 0 := integral_zero _ _

/-- Measurable realization of one pivot orientation. The outside union has
one chosen side per pair, plus isolates, and has zero internal energy. -/
theorem pivot_fill_half (K : Kernel X) (A F D Z : Set X)
    (ma : MeasurableSet A) (mf : MeasurableSet F) (md : MeasurableSet D)
    (mz : MeasurableSet Z)
    (dis : Pairwise (Disjoint on fun i : Fin 4 => ![A,F,D,Z] i))
    (aa : ∀ᵐ z ∂μ.prod μ, z.1∈A → z.2∈A → K.W z=0)
    (oo : ∀ᵐ z ∂μ.prod μ, z.1∈F∪D∪Z → z.2∈F∪D∪Z → K.W z=0)
    (a : μ.real A=1/5)
    (free : ∀ᵐ x ∂μ.restrict F, deg (μ.restrict A) K x≤0)
    (cheap : ∀ᵐ x ∂μ.restrict D, deg (μ.restrict A) K x≤1/10)
    {C : ℝ} (fill : PivotFill (10*(μ.real F+μ.real D)) (10*μ.real F) (10*μ.real Z) C)
    (lt : C<2) :
    ∃ H : Half μ, halfEnergy μ K H<1/50 := by
  classical
  obtain ⟨d,z,d0,dd,z0,zz,mas,cost⟩ := fill
  let f (i : Fin 4) := ![allocSet μ A (1/5), allocSet μ F (μ.real F),
    allocSet μ D (d/10), allocSet μ Z (z/10)] i
  let T (i : Fin 4) := ![A,F,D,Z] i
  have dc : d/10≤μ.real D := by linarith
  have zc : z/10≤μ.real Z := by linarith
  have b (i : Fin 4) : BMeas (f i) := by
    fin_cases i
    · exact allocSet_bmeas μ A ma _ (by norm_num) a.ge
    · exact allocSet_bmeas μ F mf _ measureReal_nonneg le_rfl
    · exact allocSet_bmeas μ D md _ (by positivity) dc
    · exact allocSet_bmeas μ Z mz _ (by positivity) zc
  have nn (i : Fin 4) (x : X) : 0≤f i x := by
    fin_cases i
    · exact allocSet_nn μ A _ (by norm_num) _
    · exact allocSet_nn μ F _ measureReal_nonneg _
    · exact allocSet_nn μ D _ (by positivity) _
    · exact allocSet_nn μ Z _ (by positivity) _
  have le1 (i : Fin 4) (x : X) : f i x≤1 := by
    fin_cases i
    · exact allocSet_le μ A _ a.ge _
    · exact allocSet_le μ F _ le_rfl _
    · exact allocSet_le μ D _ dc _
    · exact allocSet_le μ Z _ zc _
  have off (i : Fin 4) (x : X) (h : x∉T i) : f i x=0 := by
    fin_cases i <;> exact allocSet_support μ _ _ h
  let B := f 1 + f 2 + f 3
  have bb : BMeas B := ((b 1).add (b 2)).add (b 3)
  have sumle (x : X) : (∑ i, f i x)≤1 := by
    by_cases e : ∃ i, x∈T i
    · obtain ⟨i,hi⟩ := e
      rw [Finset.sum_eq_single i]
      · exact le1 i x
      · intro j _ hj
        exact off j x (fun h=>Set.disjoint_left.mp (dis hj) h hi)
      · simp
    · have eq : ∀ i, f i x=0 := fun i=>off i x (fun h=>e ⟨i,h⟩)
      simp [eq]
  have bf : (∫ x,f 1 x ∂μ)=μ.real F := allocSet_mass μ F mf _ measureReal_nonneg le_rfl
  have bd : (∫ x,f 2 x ∂μ)=d/10 := allocSet_mass μ D md _ (by positivity) dc
  have bz : (∫ x,f 3 x ∂μ)=z/10 := allocSet_mass μ Z mz _ (by positivity) zc
  have ba : (∫ x,f 0 x ∂μ)=1/5 := allocSet_mass μ A ma _ (by norm_num) a.ge
  have Hle : ∀ x, (f 0+B) x≤1 := by
    intro x
    simpa only [Fin.sum_univ_four,Pi.add_apply,B,add_assoc] using sumle x
  have Hmass : (∫ x,(f 0+B) x ∂μ)=1/2 := by
    rw [integral_add' (bMeas_integrable μ (b 0)) (bMeas_integrable μ bb)]
    unfold B
    rw [integral_add' (bMeas_integrable μ ((b 1).add (b 2))) (bMeas_integrable μ (b 3)),
      integral_add' (bMeas_integrable μ (b 1)) (bMeas_integrable μ (b 2)),ba,bf,bd,bz]
    linarith
  let H : Half μ := ⟨f 0+B,((b 0).add bb).1,
    fun x=>add_nonneg (nn 0 x) (add_nonneg (add_nonneg (nn 1 x) (nn 2 x)) (nn 3 x)), Hle, Hmass⟩
  have za := pivotEnergy_zero μ K A (f 0) (off 0) aa
  have zo : energyPair μ K B B=0 := pivotEnergy_zero μ K _ _ (fun x hx=>by
    have g : x∉F ∧ x∉D ∧ x∉Z := by simpa [not_or,or_assoc] using hx
    simp only [B,Pi.add_apply,off 1 x g.1,off 2 x g.2.1,off 3 x g.2.2,add_zero]) oo
  have bound (i : Fin 4) (m : MeasurableSet (T i)) (c : ℝ)
      (hc : ∀ᵐ x ∂μ.restrict (T i), deg (μ.restrict A) K x≤c) :
      energyPair μ K (f 0) (f i)≤c*(∫ x,f i x ∂μ) := by
    rw [energy_row μ K _ _ (b 0) (b i)]
    have rwdeg : ∀ x, weightedDegree μ K (f 0) x = deg (μ.restrict A) K x := by
      intro x
      change weightedDegree μ K (allocSet μ A (1/5)) x=_
      have E : allocSet μ A (1/5)=indicatorWeight A := by simp [allocSet,indicatorWeight,a]
      have mm : Measurable (indicatorWeight A) := measurable_const.indicator ma
      have en (y : X) : 0 ≤ indicatorWeight A y := by
        simp [indicatorWeight,Set.indicator_apply]; split <;> norm_num
      rw [E,weightedDegree_eq_reweight μ K (indicatorWeight A) mm en,
        indicatorWeight_reweight μ A ma]
    simp_rw [rwdeg]
    rw [←integral_const_mul]
    apply integral_mono_ae (bMeas_integrable μ ((b i).mul (deg_bmeas (μ.restrict A) K)))
      ((bMeas_integrable μ (b i)).const_mul c)
    filter_upwards [(ae_restrict_iff' m).mp hc] with x hx
    by_cases px : x∈T i
    · simpa only [Pi.mul_apply,mul_comm c] using mul_le_mul_of_nonneg_left (hx px) (nn i x)
    · simp [off i x px]
  have hf := bound 1 mf 0 free
  have hd := bound 2 md (1/10) cheap
  have hz := bound 3 mz (1/5) (ae_of_all _ (fun x=>by
    calc
      deg (μ.restrict A) K x ≤ mass (μ.restrict A) := deg_le_mass _ _ _
      _ = 1/5 := by rw [mass,measureReal_def,Measure.restrict_apply_univ,←measureReal_def,a]))
  rw [bf,zero_mul] at hf
  rw [bd] at hd
  rw [bz] at hz
  refine ⟨H,?_⟩
  rw [halfEnergy_as_pair]
  change energyPair μ K (f 0+B) (f 0+B)/2<_
  rw [energy_add_left μ K _ _ _ (b 0) bb ((b 0).add bb),
      energy_add_right μ K _ _ _ (b 0) (b 0) bb,
      energy_add_right μ K _ _ _ bb (b 0) bb,za,zo,energy_symm μ K B (f 0)]
  have Bsplit : energyPair μ K (f 0) B =
      energyPair μ K (f 0) (f 1)+energyPair μ K (f 0) (f 2)+energyPair μ K (f 0) (f 3) := by
    unfold B
    rw [energy_add_right μ K _ _ _ (b 0) ((b 1).add (b 2)) (b 3),
        energy_add_right μ K _ _ _ (b 0) (b 1) (b 2)]
  rw [Bsplit]
  linarith

#print axioms pivot_fill_half
end SparseHalfGraphon
