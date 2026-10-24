import Mathproofs.Girth5Floor3v

/-!
Actual edge accounting and global extremality for three-vertex replacement.
The extremality hypothesis compares all girth-at-least-five graphs on `V` by
cardinality of their unordered edge sets. It contains no local score condition.
-/

open Finset

namespace Girth5Floor3v

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary simple graph underlying a girth-five graph. -/
def Girth5Graph.toSimpleGraph (G : Girth5Graph V) : SimpleGraph V where
  Adj := G.adj
  symm := ⟨fun _ _ h => G.symm _ _ h⟩
  loopless := ⟨G.irrefl⟩

/-- Number of unordered edges, using Mathlib's `SimpleGraph.edgeFinset`. -/
noncomputable def edgeCount (G : Girth5Graph V) : ℕ := by
  classical
  exact G.toSimpleGraph.edgeFinset.card

/-- Global maximum edge count among all girth-five graphs on the same vertex set. -/
def IsExtremal (G : Girth5Graph V) : Prop :=
  ∀ H : Girth5Graph V, edgeCount H ≤ edgeCount G

/-- Adjacency indicator, used only for edge bookkeeping. -/
def adjIndicator (G : Girth5Graph V) (x y : V) : ℕ :=
  if G.adj x y then 1 else 0

omit [Fintype V] [DecidableEq V] in
@[simp] theorem adjIndicator_self (G : Girth5Graph V) (x : V) :
    adjIndicator G x x = 0 := by simp [adjIndicator, G.irrefl]

theorem adjIndicator_symm (G : Girth5Graph V) (x y : V) :
    adjIndicator G x y = adjIndicator G y x := if_adj_symm G x y

omit [DecidableEq V] in
/-- Handshaking, expressed as a sum of adjacency indicators. -/
theorem two_mul_edgeCount (G : Girth5Graph V) :
    2 * edgeCount G = ∑ x, ∑ y, adjIndicator G x y := by
  classical
  unfold edgeCount
  rw [SimpleGraph.two_mul_card_edgeFinset, Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases ha : G.adj x y <;> simp [Girth5Graph.toSimpleGraph, adjIndicator, ha]

/-- Twice the number of old edges completely outside the chosen triple. -/
def outsideArcCount (G : Girth5Graph V) (u v w : V) : ℕ :=
  ∑ x ∈ W G u v w, ∑ y ∈ W G u v w, adjIndicator G x y

private theorem sum_split_triple (G : Girth5Graph V) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (f : V → ℕ) :
    ∑ x, f x = f u + f v + f w + ∑ x ∈ W G u v w, f x := by
  simpa [W, Finset.sum_insert, huv, huw, hvw, add_assoc] using
    (Finset.sum_add_sum_compl ({u, v, w} : Finset V) f).symm

private theorem sum_adj_W_A (G : Girth5Graph V) (u v w : V) :
    ∑ x ∈ W G u v w, adjIndicator G u x = (A G u v w).card := by
  simp_rw [adjIndicator]
  rw [← Finset.card_filter]
  congr 1
  ext x
  rw [Finset.mem_filter, mem_W, mem_A]
  constructor
  · tauto
  · rintro ⟨h, hv, hw⟩
    exact ⟨⟨fun he => G.irrefl u (he ▸ h), hv, hw⟩, h⟩

private theorem sum_adj_W_B (G : Girth5Graph V) (u v w : V) :
    ∑ x ∈ W G u v w, adjIndicator G v x = (B G u v w).card := by
  simp_rw [adjIndicator]
  rw [← Finset.card_filter]
  congr 1
  ext x
  rw [Finset.mem_filter, mem_W, mem_B]
  constructor
  · tauto
  · rintro ⟨h, hu, hw⟩
    exact ⟨⟨hu, fun he => G.irrefl v (he ▸ h), hw⟩, h⟩

private theorem sum_adj_W_C (G : Girth5Graph V) (u v w : V) :
    ∑ x ∈ W G u v w, adjIndicator G w x = (C G u v w).card := by
  simp_rw [adjIndicator]
  rw [← Finset.card_filter]
  congr 1
  ext x
  rw [Finset.mem_filter, mem_W, mem_C]
  constructor
  · tauto
  · rintro ⟨h, hu, hv⟩
    exact ⟨⟨hu, hv, fun he => G.irrefl w (he ▸ h)⟩, h⟩

/-- Partition all edges into those outside the triple and those incident to it. -/
theorem edgeCount_partition (G : Girth5Graph V) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    2 * edgeCount G = outsideArcCount G u v w +
      2 * score (A G u v w) (B G u v w) (C G u v w) (P G u v w) := by
  rw [two_mul_edgeCount, sum_split_triple G u v w huv huw hvw]
  simp_rw [sum_split_triple G u v w huv huw hvw]
  simp only [Finset.sum_add_distrib, adjIndicator_self, zero_add, add_zero]
  simp_rw [adjIndicator_symm G v u, adjIndicator_symm G w u,
    adjIndicator_symm G w v]
  have hu : (∑ x ∈ W G u v w, adjIndicator G x u) = (A G u v w).card := by
    simp_rw [adjIndicator_symm G _ u]
    exact sum_adj_W_A G u v w
  have hv : (∑ x ∈ W G u v w, adjIndicator G x v) = (B G u v w).card := by
    simp_rw [adjIndicator_symm G _ v]
    exact sum_adj_W_B G u v w
  have hw : (∑ x ∈ W G u v w, adjIndicator G x w) = (C G u v w).card := by
    simp_rw [adjIndicator_symm G _ w]
    exact sum_adj_W_C G u v w
  rw [hu, hv, hw, sum_adj_W_A, sum_adj_W_B, sum_adj_W_C]
  simp only [score, P_card G u v w huv huw hvw, outsideArcCount, adjIndicator]
  omega

/-- The replacement graph has exactly the prescribed attachments at `u`. -/
theorem emitted_A (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V)) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h : IsFeasible G u v w A' B' C' P') :
    A (emittedGraph G u v w A' B' C' P' huv huw hvw h) u v w = A' := by
  have hn := not_mem_attach_of_mem_tri G u v w A' h.attachA
  ext x
  rw [mem_A]
  change (emitAdj G u v w A' B' C' P' u x ∧ x ≠ v ∧ x ≠ w) ↔ x ∈ A'
  by_cases hxu : x = u
  · subst x
    simp [emitAdj_irrefl G u v w A' B' C' P' huv huw hvw
      h.attachA h.attachB h.attachC, hn.1]
  by_cases hxv : x = v
  · subst x; simp [hn.2.1]
  by_cases hxw : x = w
  · subst x; simp [hn.2.2]
  simp [emitAdj, huv, huw, hxu, hxv, hxw]

/-- The replacement graph has exactly the prescribed attachments at `v`. -/
theorem emitted_B (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V)) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h : IsFeasible G u v w A' B' C' P') :
    B (emittedGraph G u v w A' B' C' P' huv huw hvw h) u v w = B' := by
  have hn := not_mem_attach_of_mem_tri G u v w B' h.attachB
  ext x
  rw [mem_B]
  change (emitAdj G u v w A' B' C' P' v x ∧ x ≠ u ∧ x ≠ w) ↔ x ∈ B'
  by_cases hxu : x = u
  · subst x; simp [hn.1]
  by_cases hxv : x = v
  · subst x
    simp [emitAdj_irrefl G u v w A' B' C' P' huv huw hvw
      h.attachA h.attachB h.attachC, hn.2.1]
  by_cases hxw : x = w
  · subst x; simp [hn.2.2]
  simp [emitAdj, hvw, Ne.symm huv, hxu, hxv, hxw]

/-- The replacement graph has exactly the prescribed attachments at `w`. -/
theorem emitted_C (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V)) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h : IsFeasible G u v w A' B' C' P') :
    C (emittedGraph G u v w A' B' C' P' huv huw hvw h) u v w = C' := by
  have hn := not_mem_attach_of_mem_tri G u v w C' h.attachC
  ext x
  rw [mem_C]
  change (emitAdj G u v w A' B' C' P' w x ∧ x ≠ u ∧ x ≠ v) ↔ x ∈ C'
  by_cases hxu : x = u
  · subst x; simp [hn.1]
  by_cases hxv : x = v
  · subst x; simp [hn.2.1]
  by_cases hxw : x = w
  · subst x
    simp [emitAdj_irrefl G u v w A' B' C' P' huv huw hvw
      h.attachA h.attachB h.attachC, hn.2.2]
  simp [emitAdj, Ne.symm huw, Ne.symm hvw, hxu, hxv, hxw]

/-- The replacement graph has exactly the prescribed internal edges. -/
theorem emitted_P (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V)) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h : IsFeasible G u v w A' B' C' P') :
    P (emittedGraph G u v w A' B' C' P' huv huw hvw h) u v w = P' := by
  have huvE := emitAdj_uv G u v w A' B' C' P' huv huw hvw h.attachA h.attachB
  have huwE := emitAdj_uw G u v w A' B' C' P' huv huw hvw h.attachA h.attachC
  have hvwE := emitAdj_vw G u v w A' B' C' P' huv huw hvw h.attachB h.attachC
  ext ⟨x, y⟩
  simp only [P, Finset.mem_filter]
  change ((x, y) ∈ ({(u, v), (u, w), (v, w)} : Finset (V × V)) ∧
    emitAdj G u v w A' B' C' P' x y) ↔ (x, y) ∈ P'
  constructor
  · rintro ⟨hm, he⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huvE.mp he
    · exact huwE.mp he
    · exact hvwE.mp he
  · intro hp
    have hm := h.internal hp
    refine ⟨hm, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huvE.mpr hp
    · exact huwE.mpr hp
    · exact hvwE.mpr hp

/-- Replacement leaves all edges outside the triple unchanged. -/
theorem emitted_outsideArcCount (G : Girth5Graph V) (u v w : V)
    (A' B' C' : Finset V) (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h : IsFeasible G u v w A' B' C' P') :
    outsideArcCount (emittedGraph G u v w A' B' C' P' huv huw hvw h) u v w =
      outsideArcCount G u v w := by
  unfold outsideArcCount
  change (∑ x ∈ W G u v w, ∑ y ∈ W G u v w, _) = _
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [mem_W] at hx hy
  simp [adjIndicator, emittedGraph, emitAdj, hx.1, hx.2.1, hx.2.2,
    hy.1, hy.2.1, hy.2.2]

/-- Exact edge accounting: the removed edges number `D`, and the added edges
number the move's score. This form avoids truncated natural subtraction. -/
theorem emitted_edgeCount_balance (G : Girth5Graph V) (u v w : V)
    (A' B' C' : Finset V) (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h : IsFeasible G u v w A' B' C' P') :
    edgeCount (emittedGraph G u v w A' B' C' P' huv huw hvw h) + D G u v w =
      edgeCount G + score A' B' C' P' := by
  have hold := edgeCount_partition G u v w huv huw hvw
  have hnew := edgeCount_partition
    (emittedGraph G u v w A' B' C' P' huv huw hvw h) u v w huv huw hvw
  rw [score_identity G u v w huv huw hvw] at hold
  rw [emitted_A, emitted_B, emitted_C, emitted_P, emitted_outsideArcCount] at hnew
  omega

/-- Signed form of exact edge accounting. -/
theorem emitted_edgeCount_difference (G : Girth5Graph V) (u v w : V)
    (A' B' C' : Finset V) (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h : IsFeasible G u v w A' B' C' P') :
    (edgeCount (emittedGraph G u v w A' B' C' P' huv huw hvw h) : ℤ) -
      edgeCount G = (score A' B' C' P' : ℤ) - D G u v w := by
  have hb := emitted_edgeCount_balance G u v w A' B' C' P' huv huw hvw h
  omega

/-- Global edge maximality forbids every improving feasible replacement. -/
theorem score_le_D_of_extremal (G : Girth5Graph V) (u v w : V)
    (A' B' C' : Finset V) (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hG : IsExtremal G) (h : IsFeasible G u v w A' B' C' P') :
    score A' B' C' P' ≤ D G u v w := by
  have hb := emitted_edgeCount_balance G u v w A' B' C' P' huv huw hvw h
  have hle := hG (emittedGraph G u v w A' B' C' P' huv huw hvw h)
  omega

/-- Every enumerated move satisfies the score ceiling in a globally extremal graph. -/
theorem scores_le_D_of_extremal (G : Girth5Graph V) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hG : IsExtremal G) :
    ∀ s ∈ scores G u v w, s ≤ D G u v w := by
  intro s hs
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hs
  have hf := (Finset.mem_filter.mp hm).2
  exact score_le_D_of_extremal G u v w m.1 m.2.1 m.2.2.1 m.2.2.2
    huv huw hvw hG hf

/-- Global extremality implies three-vertex rigidity, with no score-ceiling assumption. -/
theorem three_v_rigidity_of_extremal (G : Girth5Graph V) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hG : IsExtremal G) :
    (scores G u v w).max' (scores_nonempty G u v w huv huw hvw) = D G u v w :=
  three_v_rigidity G u v w huv huw hvw
    (scores_le_D_of_extremal G u v w huv huw hvw hG)

/-- In a globally extremal graph, the manuscript's three-vertex gap is exactly −1. -/
theorem three_v_gap_of_extremal (G : Girth5Graph V) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hG : IsExtremal G) :
    ((scores G u v w).max' (scores_nonempty G u v w huv huw hvw) : ℤ) -
      (D G u v w : ℤ) - 1 = -1 := by
  rw [three_v_rigidity_of_extremal G u v w huv huw hvw hG]
  omega

end Girth5Floor3v
