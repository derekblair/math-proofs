import NestedIntervals
import KernelBlockMeans

open Set MeasureTheory Function
open scoped ENNReal BigOperators
namespace SparseHalfGraphon

abbrev UnitHalfOpen := Ico (0:ℝ) 1

lemma unit_val_emb : MeasurableEmbedding ((↑) : UnitHalfOpen → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Ico

noncomputable def unitμ : Measure UnitHalfOpen := volume.comap Subtype.val

lemma unitμ_apply (s : Set UnitHalfOpen) :
    unitμ s = volume (((↑) : UnitHalfOpen → ℝ) '' s) :=
  unit_val_emb.comap_apply volume s

lemma unitμ_univ : unitμ univ = 1 := by
  rw [unitμ_apply, image_univ, Subtype.range_coe_subtype]
  change volume (Ico (0:ℝ) 1) = 1
  rw [Real.volume_Ico]
  norm_num

instance : IsFiniteMeasure unitμ := ⟨by rw [unitμ_univ]; exact ENNReal.one_lt_top⟩

lemma unitμ_mass : mass unitμ = 1 := by
  simp [mass, Measure.real, unitμ_univ]

namespace CoherentTables
variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
variable {p : ∀ n, I (n+1) → I n} (B : CoherentTables I p)

lemma region_in_unit (n : ℕ) (i : I n) : B.region n i ⊆ UnitHalfOpen := by
  intro x hx
  change x ∈ Ico (0:ℝ) 1
  rw [← B.region_cover n]
  exact mem_iUnion.mpr ⟨i,hx⟩

lemma region_exists (n : ℕ) (x : UnitHalfOpen) : ∃ i, x.val ∈ B.region n i := by
  apply mem_iUnion.mp
  rw [B.region_cover n]
  exact x.property

noncomputable def unitLabel (n : ℕ) (x : UnitHalfOpen) : I n :=
  (B.region_exists n x).choose

lemma unitLabel_mem (n : ℕ) (x : UnitHalfOpen) :
    x.val ∈ B.region n (B.unitLabel n x) :=
  (B.region_exists n x).choose_spec

lemma unitLabel_eq (n : ℕ) (x : UnitHalfOpen) (i : I n) :
    B.unitLabel n x = i ↔ x.val ∈ B.region n i := by
  constructor
  · rintro rfl
    exact B.unitLabel_mem n x
  · intro h
    by_contra hn
    exact Set.disjoint_left.mp (B.region_disjoint n hn) (B.unitLabel_mem n x) h

lemma unitLabel_parent (n : ℕ) (x : UnitHalfOpen) :
    p n (B.unitLabel (n+1) x) = B.unitLabel n x :=
  ((B.unitLabel_eq n x _).mpr (B.region_nested n _ (B.unitLabel_mem (n+1) x))).symm

lemma unitLabel_fiber (n : ℕ) (i : I n) :
    B.unitLabel n ⁻¹' {i} = Subtype.val ⁻¹' B.region n i := by
  ext x
  exact B.unitLabel_eq n x i

lemma unitLabel_meas (n : ℕ) [MeasurableSpace (I n)] :
    Measurable (B.unitLabel n) := by
  apply measurable_to_countable'
  intro i
  rw [B.unitLabel_fiber]
  exact unit_val_emb.measurable (B.region_measurable n i)

lemma unitLabel_mass (n : ℕ) (i : I n) :
    unitμ.real (B.unitLabel n ⁻¹' {i}) = B.cell n i := by
  unfold Measure.real
  rw [B.unitLabel_fiber, unitμ_apply]
  have h : ((↑) : UnitHalfOpen → ℝ) '' (Subtype.val ⁻¹' B.region n i) = B.region n i := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    exact inter_eq_left.mpr (B.region_in_unit n i)
  rw [h]
  exact B.region_mass n i
end CoherentTables

#print axioms CoherentTables.unitLabel_parent
#print axioms CoherentTables.unitLabel_mass
end SparseHalfGraphon
