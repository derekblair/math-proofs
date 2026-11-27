import PetersenCost

open scoped BigOperators
namespace PetersenStability

noncomputable def Y (w : V → ℝ) : ℝ := ∑ v with 10 ≤ v.val, w v

private theorem base_sum (w : V → ℝ) (h : Balanced w) :
    (∑ v with v.val < 10, w v) = 1 - Y w := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset V)) (p := fun v => v.val < 10) (f := w)
  simp only [Nat.not_lt, h.mass] at hsplit
  unfold Y
  linarith

private theorem flip_sum (p : C → V → Prop) [∀ c v, Decidable (p c v)] (w : V → ℝ) :
    (∑ c : C, ∑ v with p c v, w v) =
      ∑ v : V, ((Finset.univ.filter (fun c : C => p c v)).card : ℝ) * w v := by
  calc
    _ = ∑ c : C, ∑ v : V, if p c v then w v else 0 := by simp only [Finset.sum_filter]
    _ = ∑ v : V, ∑ c : C, if p c v then w v else 0 := Finset.sum_comm
    _ = _ := by simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

private theorem all_total (w : V → ℝ) (h : Balanced w) :
    ∑ c, total w c = 6 * (1-Y w) := by
  have hz : ∀ v : V, 10 ≤ v.val →
      (Finset.univ.filter (fun c : C => full c v = true)).card = 0 := by decide
  unfold total F
  rw [flip_sum, ← base_sum w h, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases H : v.val < 10
  · simp [H, countF_at v H]
  · simp [H, hz v (Nat.le_of_not_gt H)]

private theorem all_extra (f : C → V)
    (hf : ∀ v : V, 10 ≤ v.val → (Finset.univ.filter (fun c : C => f c = v)).card = 4)
    (hz : ∀ v : V, v.val < 10 → (Finset.univ.filter (fun c : C => f c = v)).card = 0)
    (w : V → ℝ) :
    (∑ c, w (f c)) = 4 * Y w := by
  have hh (c : C) : (∑ v with f c = v, w v) = w (f c) := by
    simp [Finset.sum_filter, eq_comm]
  simp_rw [← hh]
  rw [flip_sum]
  unfold Y
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases H : v.val < 10
  · simp [hz v H, Nat.not_le_of_gt H]
  · have H' : 10 ≤ v.val := Nat.le_of_not_gt H
    simp [H',hf v H']

theorem sparse_average (w : V → ℝ) (h : Balanced w) :
    (∑ c, cost w c)/20 ≤ 1/50 := by
  have hn : 0 ≤ Y w := Finset.sum_nonneg fun v _ => h.nonneg v
  have hA0 : ∀ v : V, v.val < 10 →
      (Finset.univ.filter (fun c : C => anchor c = v)).card = 0 := by decide
  have hB0 : ∀ v : V, v.val < 10 →
      (Finset.univ.filter (fun c : C => side c = v)).card = 0 := by decide
  have H := cost_bound (total w) (fun c => w (anchor c)) (fun c => w (side c)) (Y w) hn
    (fun c => by linarith [(total_bounds w h c).1]) (fun c => h.nonneg _)
    (fun c => h.nonneg _) (all_total w h) (all_extra anchor countAnchor hA0 w)
    (all_extra side countSide hB0 w)
  simp_rw [exact_cost]
  linarith

/-- Twenty equidistributed admissible halves on the extended Petersen graph.
The expected cost is at most 1/50, and each weighted edge is seen at rate ≥1/80. -/
theorem weighted_petersen_uniform (w : V → ℝ) (h : Balanced w) :
    (∀ c, ∑ v, half w c v = 1/2) ∧
    (∀ c v, 0 ≤ half w c v ∧ half w c v ≤ w v) ∧
    (∀ a b, edge a b = true →
      w a * w b / 80 ≤ (∑ c : C, half w c a * half w c b)/20) ∧
    (∑ c, cost w c)/20 ≤ 1/50 :=
  ⟨mass w, admissible w h, uniform w h, sparse_average w h⟩

#print axioms weighted_petersen_uniform
end PetersenStability
