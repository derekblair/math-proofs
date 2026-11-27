import FiniteKernelIndependence
import CouplingFractional

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace SparseHalfGraphon
variable {V U : Type*} [Fintype V] [Fintype U]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [MeasurableSpace U] [MeasurableSingletonClass U]

theorem blowup_uniform_product :
    (uniformVertices : Measure (V×U)) =
      (uniformVertices : Measure V).prod (uniformVertices : Measure U) := by
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  rintro ⟨v,u⟩
  rw [show ({(v,u)} : Set (V×U)) = ({v} : Set V) ×ˢ ({u} : Set U) by
    ext x
    simp [Prod.ext_iff]]
  rw [measureReal_prod_prod,uniform_singleton,uniform_singleton]
  rw [← show ({(v,u)} : Set (V×U)) = ({v} : Set V) ×ˢ ({u} : Set U) by
    ext x
    simp [Prod.ext_iff]]
  rw [uniform_singleton,Fintype.card_prod,Nat.cast_mul]
  simp [one_div,mul_comm]

theorem blowup_uniform_fst (hU : 0 < Fintype.card U) :
    MeasurePreserving (Prod.fst : V×U → V) uniformVertices uniformVertices := by
  letI : IsProbabilityMeasure (uniformVertices : Measure U) := uniform_probability hU
  rw [blowup_uniform_product]
  exact measurePreserving_fst

def blownAdj (G : V → V → Bool) (v w : V×U) : Bool := G v.1 w.1

theorem blown_sym (G : V → V → Bool) (sym : ∀ u v, G u v = G v u) :
    ∀ u v : V×U, blownAdj G u v = blownAdj G v u :=
  fun _ _ => sym _ _

theorem blown_loop (G : V → V → Bool) (loop : ∀ v, G v v = false) :
    ∀ v : V×U, blownAdj G v v = false :=
  fun _ => loop _

theorem blown_triangle (G : V → V → Bool)
    (h : ∀ u v w, G u v = true → G u w = true → G v w = false) :
    ∀ u v w : V×U, blownAdj G u v = true → blownAdj G u w = true → blownAdj G v w = false :=
  fun _ _ _ => h _ _ _

theorem blown_beta (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (pos : 0 < Fintype.card V) (hU : 0 < Fintype.card U) :
    beta (uniformVertices : Measure (V×U)) (adjacencyKernel (blownAdj G) (blown_sym (U:=U) G sym)) =
      beta (uniformVertices : Measure V) (adjacencyKernel G sym) := by
  let hp := blowup_uniform_fst (V := V) (U := U) hU
  exact beta_pull _ _ Prod.fst hp (uniform_mass pos) (adjacencyKernel G sym)

theorem blown_alpha (G : V → V → Bool) (pos : 0 < Fintype.card V) (hU : 0 < Fintype.card U) (α : ℝ)
    (h : ∀ s : Finset V, IndependentCells G (s : Set V) →
      (s.card : ℝ)/(Fintype.card V : ℝ) ≤ α) :
    ∀ t : Finset (V×U), IndependentCells (blownAdj G) (t : Set (V×U)) →
      (t.card : ℝ)/(Fintype.card (V×U) : ℝ) ≤ α := by
  classical
  intro t hi
  let s := t.image Prod.fst
  have si : IndependentCells G (s : Set V) := by
    intro u hu v hv
    obtain ⟨a,ha,E⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,F⟩ := Finset.mem_image.mp hv
    exact E ▸ F ▸ hi a ha b hb
  have sub : t ⊆ s.product Finset.univ := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,Finset.mem_univ _⟩
  have hc : t.card ≤ Fintype.card U*s.card := by
    have e := Finset.card_le_card sub
    simpa [Finset.card_product,mul_comm] using e
  have hc' : (t.card : ℝ) ≤ (Fintype.card U:ℝ)*(s.card : ℝ) := by exact_mod_cast hc
  have N : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast pos.ne'
  calc
    _ ≤ ((Fintype.card U:ℝ)*(s.card : ℝ))/(Fintype.card (V×U) : ℝ) :=
      div_le_div_of_nonneg_right hc' (Nat.cast_nonneg _)
    _ = (s.card : ℝ)/(Fintype.card V : ℝ) := by
      rw [Fintype.card_prod]
      push_cast
      have N' : (Fintype.card U:ℝ) ≠ 0 := by exact_mod_cast hU.ne'
      field_simp
    _ ≤ α := h s si


theorem blown_independent (G : V → V → Bool) (s : Finset V) (hs : IndependentCells G (s:Set V)) :
    IndependentCells (blownAdj (U:=U) G) (s.product (Finset.univ : Finset U) : Set (V×U)) := by
  intro x hx y hy
  exact hs x.1 (Finset.mem_product.mp hx).1 y.1 (Finset.mem_product.mp hy).1

theorem blown_mark_mass (s : Finset V) (hU : 0 < Fintype.card U) :
    ((s.product (Finset.univ : Finset U)).card:ℝ)/(Fintype.card (V×U):ℝ) =
      (s.card:ℝ)/(Fintype.card V:ℝ) := by
  change ((s ×ˢ (Finset.univ : Finset U)).card:ℝ)/(Fintype.card (V×U):ℝ) = (s.card:ℝ)/(Fintype.card V:ℝ)
  rw [Finset.card_product,Finset.card_univ, Fintype.card_prod]
  push_cast
  have N : (Fintype.card U:ℝ) ≠ 0 := by exact_mod_cast hU.ne'
  exact mul_div_mul_right _ _ N

#print axioms blown_mark_mass
#print axioms blown_alpha
#print axioms blown_beta
end SparseHalfGraphon
