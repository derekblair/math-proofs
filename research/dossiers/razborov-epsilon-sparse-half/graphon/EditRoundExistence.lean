import EditRoundLoss
open scoped BigOperators
namespace SparseHalfEditRound
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- A single labeling attains this joint loss and count-deviation budget. -/
theorem round_joint (r : V → I → ℝ) (hr : ∀ v i, 0 ≤ r v i)
    (hu : ∀ v i, r v i ≤ 1) (hs : ∀ v, ∑ i, r v i = 1)
    (F : V → V → I → I → ℝ) (hf : ∀ v w i j, 0 ≤ F v w i j) :
    ∃ q : V → I,
      integralLoss F q + (∑ i, (actualCount q i - meanCount r i)^2)
        ≤ fractionalLoss r F + (Fintype.card I : ℝ) * (Fintype.card V : ℝ) := by
  let f (q : V → I) := integralLoss F q + (∑ i, (actualCount q i - meanCount r i)^2)
  obtain ⟨q,hq⟩ := exists_le_mean r hr hs f
  refine ⟨q, hq.trans ?_⟩
  change expectation r (fun q => integralLoss F q + (∑ i, (actualCount q i - meanCount r i)^2)) ≤ _
  rw [ex_add,ex_sum]
  apply add_le_add (loss_bound r hr hs F hf)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    Finset.sum_le_sum (s := (Finset.univ : Finset I))
      (fun i _ => variance_bound r hr hu hs i)

theorem round_directed (r : V → I → ℝ) (hr : ∀ v i, 0 ≤ r v i)
    (hu : ∀ v i, r v i ≤ 1) (hs : ∀ v, ∑ i, r v i = 1)
    (G : V → V → Bool) (B : I → I → Bool) (gl : ∀ v, G v v = false)
    (bl : ∀ i, B i i = false)
    (n_pos : 0 < Fintype.card V) (target : I → ℝ)
    (a b : ℝ) (ha : 0 ≤ a)
    (mass : ∀ i, |meanCount r i / (Fintype.card V : ℝ) - target i| ≤ b)
    (budget : fractionalLoss r (boolLoss G B)/(Fintype.card V : ℝ)^2 +
      (Fintype.card I : ℝ)/(Fintype.card V : ℝ) ≤ a^2) :
    ∃ q : V → I,
      (∀ i, |((Finset.univ.filter (fun v => q v = i)).card : ℝ)/
        (Fintype.card V : ℝ)-target i| ≤ a+b) ∧
      ((Finset.univ.filter (fun z : V × V => G z.1 z.2 ≠ B (q z.1) (q z.2))).card : ℝ)/
        (Fintype.card V : ℝ)^2 ≤ a^2 := by
  let n : ℝ := Fintype.card V
  have np : 0 < n := by dsimp [n]; exact_mod_cast n_pos
  have ns : 0 < n^2 := pow_pos np 2
  let F := boolLoss G B
  obtain ⟨q,hq⟩ := round_joint r hr hu hs F (boolLoss_nonneg G B)
  have C : fractionalLoss r F+(Fintype.card I : ℝ)*n ≤ a^2*n^2 := by
    have B' := mul_le_mul_of_nonneg_right budget ns.le
    change (fractionalLoss r F / n^2 + (Fintype.card I : ℝ)/n)*n^2 ≤ _ at B'
    have eq : (fractionalLoss r F / n^2 + (Fintype.card I : ℝ)/n)*n^2 =
        fractionalLoss r F+(Fintype.card I : ℝ)*n := by field_simp
    rw [eq] at B'
    exact B'
  have D := hq.trans C
  have hF := integralLoss_nonneg F (boolLoss_nonneg G B) q
  have hS : 0 ≤ ∑ i, (actualCount q i-meanCount r i)^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨q,?_ ,?_⟩
  · intro i
    have H := Finset.single_le_sum (f := fun i => (actualCount q i-meanCount r i)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hi : (actualCount q i-meanCount r i)^2 ≤ (a*n)^2 := by
      nlinarith only [H,D,hF]
    have hj : |actualCount q i-meanCount r i| ≤ a*n := by
      have he : |actualCount q i-meanCount r i|^2 = (actualCount q i-meanCount r i)^2 := sq_abs _
      by_contra! h
      have p := mul_self_lt_mul_self (mul_nonneg ha np.le) h
      nlinarith only [p,he,hi]
    have hk : |actualCount q i/n-meanCount r i/n| ≤ a := by
      rw [← sub_div,abs_div,abs_of_pos np]
      exact (div_le_iff₀ np).mpr hj
    rw [← count_is_fiber q i]
    change |actualCount q i/n-target i| ≤ a+b
    calc
      _ = |(actualCount q i/n-meanCount r i/n)+(meanCount r i/n-target i)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hk (mass i))
  · rw [← directed_count G B q gl bl]
    exact (div_le_iff₀ ns).mpr (by linarith)

#print axioms round_joint
#print axioms round_directed
end SparseHalfEditRound
