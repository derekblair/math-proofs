import DominantPivotHalf

open Set MeasureTheory Function Filter
open SparseHalfCountableEndpoint
namespace SparseHalfGraphon
variable {X I : Type*} [MeasurableSpace X] [Countable I]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma pivot_row_inter (K : Kernel X) (A T C V : Set X)
    (mc : MeasurableSet C) (ht : T⊆A)
    (e : ∀ᵐ x ∂μ.restrict V,
      (fun y=>K.W (x,y)) =ᵐ[μ.restrict A] oneOn C) :
    ∀ᵐ x ∂μ.restrict V, deg (μ.restrict T) K x=μ.real (C∩T) := by
  filter_upwards [e] with x hx
  have sub : μ.restrict T≤μ.restrict A := Measure.restrict_mono ht le_rfl
  have eq := hx.filter_mono sub.absolutelyContinuous.ae_le
  rw [deg,integral_congr_ae eq,oneOn,integral_indicator mc,setIntegral_const,smul_eq_mul,mul_one]
  simp [measureReal_def,Measure.restrict_apply mc]

lemma pivot_split_compl (A C : Set X) (ma : MeasurableSet A) (mc : MeasurableSet C) :
    μ.real (C∩A)+μ.real (Cᶜ∩A)=μ.real A := by
  have eq : Cᶜ∩A=A\(C∩A) := by ext x; simp; tauto
  rw [eq,measureReal_sdiff inter_subset_right (mc.inter ma)]
  ring

lemma pivot_split_of_cover (B D C : Set X) (mb : MeasurableSet B) (md : MeasurableSet D)
    (mc : MeasurableSet C) (dis : Disjoint B D) :
    μ.real (C∩B)+μ.real (C∩D)=μ.real (C∩(B∪D)) := by
  rw [←measureReal_union (dis.mono inter_subset_right inter_subset_right) (mc.inter md)]
  congr 1
  ext x
  simp
  tauto

/-- Choose opposite sides of a nonpivot pair for the two anchor halves. -/
theorem opposite_cheap_orientations (K : Kernel X) (A B D C P Q : Set X)
    (ma : MeasurableSet A) (mb : MeasurableSet B) (md : MeasurableSet D)
    (mc : MeasurableSet C) (cover : B∪D=A) (dis : Disjoint B D)
    (capB : μ.real B=1/5) (capD : μ.real D=1/5)
    (capC : μ.real (C∩A)=1/5)
    (hp : ∀ᵐ x ∂μ.restrict P, (fun y => K.W (x,y)) =ᵐ[μ.restrict A] oneOn C)
    (hq : ∀ᵐ x ∂μ.restrict Q, (fun y => K.W (x,y)) =ᵐ[μ.restrict A] oneOn Cᶜ) :
    ((∀ᵐ x ∂μ.restrict P, deg (μ.restrict B) K x≤1/10) ∧
     (∀ᵐ x ∂μ.restrict Q, deg (μ.restrict D) K x≤1/10)) ∨
    ((∀ᵐ x ∂μ.restrict Q, deg (μ.restrict B) K x≤1/10) ∧
     (∀ᵐ x ∂μ.restrict P, deg (μ.restrict D) K x≤1/10)) := by
  have eB : B⊆A := cover ▸ subset_union_left
  have eD : D⊆A := cover ▸ subset_union_right
  have pp := pivot_row_inter μ K A B C P mc eB hp
  have pq := pivot_row_inter μ K A B Cᶜ Q mc.compl eB hq
  have qp := pivot_row_inter μ K A D C P mc eD hp
  have qq := pivot_row_inter μ K A D Cᶜ Q mc.compl eD hq
  have ca := pivot_split_of_cover μ B D C mb md mc dis
  rw [cover,capC] at ca
  have cb := pivot_split_compl μ B C mb mc
  have cd := pivot_split_compl μ D C md mc
  by_cases h : μ.real (C∩B)≤1/10
  · left
    constructor
    · filter_upwards [pp] with x hx using by linarith
    · filter_upwards [qq] with x hx using by linarith
  · right
    constructor
    · filter_upwards [pq] with x hx using by linarith
    · filter_upwards [qp] with x hx using by linarith

#print axioms opposite_cheap_orientations
end SparseHalfGraphon
