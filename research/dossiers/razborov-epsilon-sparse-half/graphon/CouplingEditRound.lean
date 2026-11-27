import CouplingEditLoss
open MeasureTheory Set Function
open scoped BigOperators
namespace SparseHalfGraphon
open SparseHalfEditRound

variable {X Y V I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable (μ : Measure X) [IsFiniteMeasure μ]

theorem real_cell_comp_preserving {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure Y) (p : X → Y) (h : MeasurePreserving p μ ν)
    (g : Y → A) (hg : Measurable g) (i : A) :
    μ.real (cell (g ∘ p) i) = ν.real (cell g i) := by
  unfold Measure.real
  change (μ (p ⁻¹' cell g i)).toReal = _
  have hc : MeasurableSet (cell g i) := hg (measurableSet_singleton i)
  rw [← Measure.map_apply (μ := μ) h.measurable hc,h.map_eq]

theorem real_cell_preserving {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure A) (f : X → A) (h : MeasurePreserving f μ ν) (i : A) :
    μ.real (cell f i) = ν.real {i} :=
  real_cell_comp_preserving μ ν f h id measurable_id i

theorem coupling_cut_loss_le (f : X → V) (g : X → I) (hf : Measurable f) (hg : Measurable g)
    (pos : 0 < Fintype.card V) (G : V → V → Bool) (B : I → I → Bool)
    (K J : Kernel X) (ε : ℝ) (cut : CutBound μ K J ε)
    (hK : ∀ x y, K.W (x,y) = boolReal (G (f x) (f y)))
    (hJ : ∀ x y, J.W (x,y) = boolReal (B (g x) (g y))) :
    fractionalLoss (couplingMatrix μ f g) (boolLoss G B)/(Fintype.card V : ℝ)^2 ≤
      (Fintype.card I : ℝ)^2*ε := by
  rw [coupling_loss μ f g hf hg pos G B]
  have he (z : X×X) : |boolReal (G (f z.1) (f z.2))-boolReal (B (g z.1) (g z.2))| =
      |gapW K J z| := by
    rcases z with ⟨x,y⟩
    simp only [gapW,hK,hJ]
  simp_rw [he]
  exact cut_to_binary_L1 μ K J ε cut g (fun i => hg (measurableSet_singleton i)) B hJ

variable [DecidableEq V] [DecidableEq I]

/-- Rounds directly from a cut coupling to an actual finite coloring
close in both class masses and directed edge disagreements. -/
theorem coupling_cut_round (f : X → V) (g : X → I) (hf : Measurable f) (hg : Measurable g)
    (pos : 0 < Fintype.card V)
    (uniform : ∀ v, μ.real (cell f v) = 1/(Fintype.card V : ℝ))
    (G : V → V → Bool) (B : I → I → Bool)
    (gl : ∀ v, G v v = false) (bl : ∀ i, B i i = false)
    (K J : Kernel X) (ε : ℝ) (cut : CutBound μ K J ε)
    (hK : ∀ x y, K.W (x,y) = boolReal (G (f x) (f y)))
    (hJ : ∀ x y, J.W (x,y) = boolReal (B (g x) (g y)))
    (target : I → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (mass : ∀ i, |μ.real (cell g i) - target i| ≤ b)
    (budget : (Fintype.card I : ℝ)^2*ε + (Fintype.card I : ℝ)/(Fintype.card V : ℝ) ≤ a^2) :
    ∃ q : V → I,
      (∀ i, |((Finset.univ.filter (fun v => q v = i)).card : ℝ)/
        (Fintype.card V : ℝ)-target i| ≤ a+b) ∧
      ((Finset.univ.filter (fun z : V × V => G z.1 z.2 ≠ B (q z.1) (q z.2))).card : ℝ)/
        (Fintype.card V : ℝ)^2 ≤ a^2 := by
  have z := coupling_cut_loss_le μ f g hf hg pos G B K J ε cut hK hJ
  have d := coupling_entry_bounds μ f g hf hg pos uniform
  refine round_directed (couplingMatrix μ f g) (fun v i => (d v i).1) (fun v i => (d v i).2)
    (coupling_row μ f g hf hg pos uniform) G B gl bl pos target a b ha ?_ ?_
  · intro i
    rw [coupling_mass μ f g hf hg pos i]
    exact mass i
  · exact (add_le_add z (le_refl _)).trans budget

#print axioms real_cell_comp_preserving
#print axioms coupling_cut_loss_le
#print axioms coupling_cut_round
end SparseHalfGraphon
