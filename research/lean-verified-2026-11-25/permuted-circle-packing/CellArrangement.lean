import CellSets
import Mathlib.MeasureTheory.Measure.NullMeasurable

namespace PermCircles
open Set MeasureTheory Function
open scoped ENNReal BigOperators

def box (a b : ℝ) : Set Point := Icc a b ×ˢ Icc a b

lemma volume_box (a b : ℝ) (h : a ≤ b) :
    volume (box a b) = ENNReal.ofReal ((b-a)^2) := by
  change (volume : Measure ℝ).prod (volume : Measure ℝ) (Icc a b ×ˢ Icc a b) = _
  rw [Measure.prod_prod,Real.volume_Icc,pow_two,ENNReal.ofReal_mul (sub_nonneg.mpr h)]

lemma distance_tie_null {a b : Point} (hn : a.1 ≠ b.1) :
    volume {z : Point | sqDist z a = sqDist z b} = 0 := by
  let c := 2*(b.1-a.1)
  let s := 2*(b.2-a.2)
  let t := sqDist b 0-sqDist a 0
  let L : Point →ₗ[ℝ] Point := Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![c,s;0,1]
  have hc : c ≠ 0 := by dsimp [c]; intro h; apply hn; linarith
  have hL : L.det = c := by
    rw [show L = Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![c,s;0,1] by rfl,
      LinearMap.det_toLin, Matrix.det_fin_two_of]
    ring
  have hset : {z : Point | sqDist z a = sqDist z b} =
      L ⁻¹' ({t} ×ˢ (univ : Set ℝ)) := by
    ext z
    change (sqDist z a = sqDist z b) ↔ (L z).1 = t ∧ _
    have he : (L z).1 = c*z.1+s*z.2 := by
      dsimp only [L]
      rw [Matrix.toLin_finTwoProd_apply]
    rw [he]
    simp only [mem_univ, and_true]
    unfold sqDist
    dsimp [c,s,t,sqDist]
    constructor <;> intro h <;> linear_combination h
  rw [hset,Measure.addHaar_preimage_linearMap volume (hL ▸ hc)]
  have hm : volume ({t} ×ˢ (univ : Set ℝ)) = 0 := by
    change (volume : Measure ℝ).prod (volume : Measure ℝ) ({t} ×ˢ univ) = 0
    rw [Measure.prod_prod,measure_singleton,zero_mul]
  rw [hm,mul_zero]

lemma cells_aeDisjoint {I : Type*} [Fintype I] {p : I → Point}
    (hp : Function.Injective fun i => (p i).1) (R : ℝ) :
    Pairwise (AEDisjoint volume on cell R p) := by
  intro i j hne
  change volume (cell R p i ∩ cell R p j) = 0
  apply measure_mono_null _ (distance_tie_null (fun e => hne (hp e)))
  intro z hz
  exact le_antisymm (hz.1.2 j) (hz.2.2 i)

lemma disk_in_box {R M : ℝ} (hR : 0 ≤ R) {a : Point} (ha : a ∈ box 0 M) :
    disk R a ⊆ box (-R) (M+R) := by
  intro z hz
  change (z.1-a.1)^2+(z.2-a.2)^2 ≤ R^2 at hz
  have h₁ : |z.1-a.1| ≤ R := by
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (z.2-a.2)]
  have h₂ : |z.2-a.2| ≤ R := by
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (z.1-a.1)]
  rcases abs_le.mp h₁ with ⟨hl,hh⟩
  rcases abs_le.mp h₂ with ⟨hl',hh'⟩
  have ha1 : 0 ≤ a.1 ∧ a.1 ≤ M := ha.1
  have ha2 : 0 ≤ a.2 ∧ a.2 ≤ M := ha.2
  exact ⟨⟨by linarith [ha1.1],by linarith [ha1.2]⟩,⟨by linarith [ha2.1],by linarith [ha2.2]⟩⟩

lemma global_area_from_cells {n : ℕ} {R M V : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hV : 0 ≤ V) (p : Fin n → Point)
    (hp : Function.Injective fun i => (p i).1) (hb : ∀ i, p i ∈ box 0 M)
    (hcell : ∀ i, ENNReal.ofReal V ≤ volume (cell R p i)) :
    (n:ℝ)*V ≤ (M+2*R)^2 := by
  classical
  have hU : (⋃ i, cell R p i) ⊆ box (-R) (M+R) := by
    intro z hz
    rcases mem_iUnion.mp hz with ⟨i,h⟩
    exact disk_in_box hR (hb i) h.1
  have hsum := measure_mono hU (μ:=volume)
  rw [measure_iUnion₀ (cells_aeDisjoint hp R)
      (fun i => (cell_measurable R p i).nullMeasurableSet), tsum_fintype] at hsum
  have hv : ENNReal.ofReal ((n:ℝ)*V) = ∑ _i : Fin n, ENNReal.ofReal V := by
    rw [ENNReal.ofReal_mul (by positivity)]
    simp
  have he := (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hcell i)).trans hsum
  rw [← hv, volume_box _ _ (by linarith)] at he
  have hmn : (0:ℝ) ≤ (M+R-(-R))^2 := sq_nonneg _
  have hineq : (n:ℝ)*V ≤ (M+R-(-R))^2 := (ENNReal.ofReal_le_ofReal_iff hmn).mp he
  convert hineq using 1
  ring

#print axioms global_area_from_cells
end PermCircles
