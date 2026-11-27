import ComplementRowsAE
import TriangleAE

open Set MeasureTheory Filter Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]

lemma complement_degree_sum (ν : Measure X) [IsFiniteMeasure ν]
    (W : Kernel X) (x y : X)
    (h : ∀ᵐ v ∂ν, (W.W (x,v)=0 ∧ W.W (y,v)=1) ∨ (W.W (x,v)=1 ∧ W.W (y,v)=0)) :
    deg ν W x + deg ν W y = mass ν := by
  have hh : (fun v=>W.W (x,v)+W.W (y,v)) =ᵐ[ν] (fun _=>1) := by
    filter_upwards [h] with v hv
    rcases hv with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp [h1,h2]
  have he := integral_congr_ae hh
  rw [integral_add (row_integrable ν W x) (row_integrable ν W y),integral_const,
    smul_eq_mul,mul_one] at he
  exact he

theorem outside_edges_equal_degree (μ ν ω : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ω]
    (hν : ν ≪ μ) (hω : ω ≪ μ) (W : Kernel X)
    (ht : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle W z=0)
    (hd : ∀ᵐ x ∂ω, mass ν/2≤deg ν W x) :
    ∀ᵐ z ∂ω.prod ω, W.W z=0 ∨
      (deg ν W z.1=mass ν/2 ∧ deg ν W z.2=mass ν/2) := by
  have hD : MeasurableSet {x | mass ν/2≤deg ν W x} :=
    measurableSet_le measurable_const (deg_measurable ν W)
  have hD' : MeasurableSet {z:X×X | mass ν/2≤deg ν W z.1 ∧ mass ν/2≤deg ν W z.2} :=
    (measurable_fst hD).inter (measurable_snd hD)
  have hd' : ∀ᵐ z ∂ω.prod ω, mass ν/2≤deg ν W z.1 ∧ mass ν/2≤deg ν W z.2 := by
    apply (Measure.ae_prod_iff_ae_ae hD').mpr
    filter_upwards [hd] with x hx
    filter_upwards [hd] with y hy
    exact ⟨hx,hy⟩
  filter_upwards [edge_complement μ ν ω hν hω W ht hd, hd'] with z hz hdz
  rcases hz with h0 | hc
  · exact Or.inl h0
  · have hh := complement_degree_sum ν W z.1 z.2 hc
    exact Or.inr ⟨by linarith [hdz.1,hdz.2],by linarith [hdz.1,hdz.2]⟩

#print axioms outside_edges_equal_degree
end SparseHalfGraphon
