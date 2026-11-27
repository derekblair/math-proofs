import Mathlib.Tactic

open scoped BigOperators

namespace ModularForestCertificate

/-- A sequence of advances by zero or one hits every intermediate integer.
Reducing the initial segment counts modulo q is the residue-coverage step.
This statement does not formalize the permanent or directed graph. -/
theorem prefix_true_count (xs : List Bool) (k : ℕ)
    (hk : k ≤ (xs.filter id).length) :
    ∃ pre post : List Bool, xs = pre ++ post ∧ (pre.filter id).length = k := by
  induction xs generalizing k with
  | nil =>
      have h0 : k = 0 := by simpa using hk
      exact ⟨[], [], rfl, h0.symm⟩
  | cons x xs ih =>
      cases k with
      | zero => exact ⟨[], x :: xs, rfl, rfl⟩
      | succ k =>
          cases x with
          | false =>
              have h0 : k + 1 ≤ (xs.filter id).length := by simpa using hk
              obtain ⟨pre, post, hp, hc⟩ := ih (k + 1) h0
              exact ⟨false :: pre, post, by rw [hp]; rfl, by simpa using hc⟩
          | true =>
              have h0 : k ≤ (xs.filter id).length := by simpa using hk
              obtain ⟨pre, post, hp, hc⟩ := ih k h0
              exact ⟨true :: pre, post, by rw [hp]; rfl, by simp [hc]⟩

/-- Distinct variable labels cannot charge the same forest edge. -/
theorem sum_required_le_edges {E C : Type*} [DecidableEq C]
    (edges : Finset E) (colors : Finset C) (label : E → C) (need : C → ℕ)
    (h : ∀ c ∈ colors, need c ≤ (edges.filter (fun e => label e = c)).card) :
    ∑ c ∈ colors, need c ≤ edges.card := by
  classical
  calc
    ∑ c ∈ colors, need c ≤
        ∑ c ∈ colors, (edges.filter (fun e => label e = c)).card :=
      Finset.sum_le_sum h
    _ = (edges.filter (fun e => label e ∈ colors)).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ edges.card := Finset.card_le_card (Finset.filter_subset _ _)

#print axioms prefix_true_count
#print axioms sum_required_le_edges

/-- Arithmetic comparison used to invoke the classical long-cycle edge bound. -/
theorem woodall_missing_edge_threshold (n q : ℤ) (h : 3 * q + 1 ≤ n) :
    q * (n - q) - 1 ≤ (q + 1) * (n - q - 2) := by
  nlinarith only [h]

#print axioms woodall_missing_edge_threshold

end ModularForestCertificate
