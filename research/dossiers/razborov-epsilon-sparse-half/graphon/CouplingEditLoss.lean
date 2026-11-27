import CouplingEditMatrix
import CutBinaryTemplate
open MeasureTheory Set Function
open scoped BigOperators
namespace SparseHalfGraphon
open SparseHalfEditRound

variable {X V I : Type*} [MeasurableSpace X]
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable (μ : Measure X) [IsFiniteMeasure μ]

def boolReal (a : Bool) : ℝ := if a then 1 else 0

theorem abs_bool_gap (G : V → V → Bool) (B : I → I → Bool) (v w : V) (i j : I) :
    |boolReal (G v w)-boolReal (B i j)| = boolLoss G B v w i j := by
  cases H : G v w <;> cases T : B i j <;> norm_num [boolReal,boolLoss,H,T]

theorem coupling_loss (f : X → V) (g : X → I) (hf : Measurable f) (hg : Measurable g)
    (pos : 0 < Fintype.card V) (G : V → V → Bool) (B : I → I → Bool) :
    fractionalLoss (couplingMatrix μ f g) (boolLoss G B)/(Fintype.card V : ℝ)^2 =
      ∫ z : X×X, |boolReal (G (f z.1) (f z.2))-boolReal (B (g z.1) (g z.2))| ∂μ.prod μ := by
  classical
  let c : X → V×I := fun x => (f x,g x)
  have hc : Measurable c := hf.prodMk hg
  let F (p : (V×I)×(V×I)) := boolLoss G B p.1.1 p.2.1 p.1.2 p.2.2
  have h := integral_parent_cell (μ := μ.prod μ) (fun _ : X×X => ())
    (pairLabel c) (fun _ => ()) (pair_label_meas c hc) (fun _ => rfl) F ()
  have h' : (∫ z : X×X, F (pairLabel c z) ∂μ.prod μ) =
      ∑ a : (V×I)×(V×I), (μ.prod μ).real (cell (pairLabel c) a)*F a := by
    simpa [cell] using h
  have hc' (p : V×I) : cell c p = cell f p.1 ∩ cell g p.2 := by
    ext x
    simp [cell,c,Prod.ext_iff]
  let n : ℝ := Fintype.card V
  have np : n ≠ 0 := by dsimp [n]; exact_mod_cast pos.ne'
  have he (p : (V×I)×(V×I)) :
      (μ.prod μ).real (cell (pairLabel c) p)*F p =
      (μ.real (cell f p.1.1 ∩ cell g p.1.2)) *
        (μ.real (cell f p.2.1 ∩ cell g p.2.2)) * F p := by
    rcases p with ⟨a,b⟩
    rw [pair_cell,measureReal_prod_prod,hc',hc']
  rw [← show (∫ z : X×X, F (pairLabel c z) ∂μ.prod μ) =
      ∫ z : X×X, |boolReal (G (f z.1) (f z.2))-boolReal (B (g z.1) (g z.2))| ∂μ.prod μ by
    apply integral_congr_ae
    exact ae_of_all _ (fun z => (abs_bool_gap G B _ _ _ _).symm)]
  rw [h']
  simp_rw [he]
  let L (v w : V) (i j : I) :=
    μ.real (cell f v ∩ cell g i)*μ.real (cell f w ∩ cell g j)*boolLoss G B v w i j
  change fractionalLoss (couplingMatrix μ f g) (boolLoss G B)/n^2 =
    ∑ p : (V×I)×(V×I), L p.1.1 p.2.1 p.1.2 p.2.2
  have order : (∑ p : (V×I)×(V×I), L p.1.1 p.2.1 p.1.2 p.2.2) =
      ∑ v, ∑ w, ∑ i, ∑ j, L v w i j := by
    rw [← Finset.univ_product_univ,Finset.sum_product]
    simp_rw [← Finset.univ_product_univ,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro v _
    exact Finset.sum_comm
  rw [order]
  unfold fractionalLoss
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold couplingMatrix L n at *
  rw [← div_eq_mul_inv]
  field_simp

#print axioms coupling_loss
end SparseHalfGraphon
