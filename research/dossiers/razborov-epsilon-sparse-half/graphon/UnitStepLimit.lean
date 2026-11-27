import UnitStepKernels
import MeanTower
import KernelL1Limit

open Set MeasureTheory Function Filter Topology
namespace SparseHalfGraphon.CoherentTables

variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
variable [∀ n, MeasurableSpace (I n)] [∀ n, MeasurableSingletonClass (I n)]
variable {p : ∀ n, I (n+1) → I n} (B : CoherentTables I p)

lemma unit_parent_factor (i j : ℕ) (hij : i ≤ j) :
    ∃ q : I j → I i, ∀ x, B.unitLabel i x = q (B.unitLabel j x) := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨id, fun _ => rfl⟩
  | succ j hij ih =>
    obtain ⟨q,hq⟩ := ih
    refine ⟨q ∘ p j,fun x => ?_⟩
    rw [comp_apply,B.unitLabel_parent,hq]

lemma unit_coarse_mean (i j : ℕ) (hij : i < j) :
    meanBlock (unitμ.prod unitμ) (pairLabel (B.unitLabel i)) (B.unitStep j).W =
      (B.unitStep i).W := by
  have h : i+1 ≤ j := hij
  induction j,h using Nat.le_induction with
  | base =>
    exact congrArg Kernel.W (B.unitStep_means i)
  | succ j hj ih =>
    obtain ⟨q,hq⟩ := B.unit_parent_factor i j (Nat.le_trans (Nat.le_succ i) hj)
    let P : I j × I j → I i × I i := fun z => (q z.1,q z.2)
    have hQ (z : UnitHalfOpen × UnitHalfOpen) :
        pairLabel (B.unitLabel i) z = P (pairLabel (B.unitLabel j) z) :=
      Prod.ext (hq z.1) (hq z.2)
    have ht := meanBlock_tower (μ:=unitμ.prod unitμ) (pairLabel (B.unitLabel i))
      (pairLabel (B.unitLabel j)) P (pair_label_meas _ (B.unitLabel_meas j))
      hQ (B.unitStep (j+1)).W (B.unitStep (j+1)).bmeas
    have ha := congrArg Kernel.W (B.unitStep_means j)
    change meanBlock (unitμ.prod unitμ) (pairLabel (B.unitLabel j)) (B.unitStep (j+1)).W =
        (B.unitStep j).W at ha
    rw [ha,ih hj] at ht
    exact ht.symm

theorem unitStep_energy_gap (i j : ℕ) (hij : i ≤ j) :
    (∫ z, ((B.unitStep j).W z - (B.unitStep i).W z)^2 ∂unitμ.prod unitμ) =
      blockEnergy unitμ (B.unitStep j) - blockEnergy unitμ (B.unitStep i) := by
  obtain ⟨q,hq⟩ := B.unit_parent_factor i j hij
  let P : I j × I j → I i × I i := fun z => (q z.1,q z.2)
  have hQ (z : UnitHalfOpen × UnitHalfOpen) :
      pairLabel (B.unitLabel i) z = P (pairLabel (B.unitLabel j) z) :=
    Prod.ext (hq z.1) (hq z.2)
  have hh := refinement_energy (unitμ.prod unitμ)
    (pairLabel (B.unitLabel i)) (pairLabel (B.unitLabel j)) P
    (pair_label_meas _ (B.unitLabel_meas i)) (pair_label_meas _ (B.unitLabel_meas j))
    hQ (B.unitStep (j+1)).W (B.unitStep (j+1)).bmeas
  rw [B.unit_coarse_mean j (j+1) (Nat.lt_succ_self j),
    B.unit_coarse_mean i (j+1) (Nat.lt_succ_of_le hij)] at hh
  exact hh.symm

/-- Coherent nested tables are realized by an actual bounded symmetric
Lebesgue kernel, with both L¹ and cut convergence of the realizing steps. -/
theorem unitStep_limit :
    ∃ K : Kernel UnitHalfOpen,
      Tendsto (fun n => kernelL1 unitμ (B.unitStep n)) atTop (𝓝 (kernelL1 unitμ K)) ∧
      ∀ ε > 0, ∀ᶠ n in atTop, CutBound unitμ (B.unitStep n) K ε := by
  let E (n : ℕ) := blockEnergy unitμ (B.unitStep n)
  have hE : Monotone E := by
    intro i j hij
    apply sub_nonneg.mp
    change 0 ≤ blockEnergy unitμ (B.unitStep j) - blockEnergy unitμ (B.unitStep i)
    rw [← B.unitStep_energy_gap i j hij]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hm : mass (unitμ.prod unitμ) = 1 := by
    simp [mass, Measure.real, ← Set.univ_prod_univ, Measure.prod_prod, unitμ_univ]
  obtain ⟨F,hF⟩ := coherent_table_L1_limit (unitμ.prod unitμ) hm
    (fun n => (B.unitStep n).W) (fun n => (B.unitStep n).bmeas)
    E hE (fun n => (block_energy_range unitμ (B.unitStep n) unitμ_mass).2)
    B.unitStep_energy_gap
  obtain ⟨K,hK,hcut⟩ := kernel_L1_limit_cut unitμ (B.unitStep) F hF
  refine ⟨K,?_,hcut⟩
  rw [hK]
  exact hF

#print axioms unitStep_energy_gap
#print axioms unitStep_limit
end SparseHalfGraphon.CoherentTables
