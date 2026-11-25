import Big269
open SimpleGraph
open scoped BigOperators
namespace Refute269

def row (v : Big) : Nat := ∑ w : Big, value v w
def rp (r : Fin 4) : Nat := if r = 0 ∨ r = 3 then 563 else 579
def ra (r : Fin 4) : Nat := if r = 0 ∨ r = 1 then 786 else 824
def rb (_ : Fin 2) : Nat := 804

def smallRow (s : Small) : Nat :=
  (∑ p : Fin 4, dd s (P p)) +
    ((∑ r : Fin 4, (dd s (A 0 r) + 34 * dd s (A 1 r))) +
     (∑ r : Fin 2, (dd s (B 0 r) + 61 * dd s (B 1 r))))

lemma sum_color {m : Nat} (a : Fin m) (F : Fin 2 → Nat) :
    (∑ j : Fin m, F (color a j)) = F 0 + (m-1) * F 1 := by
  classical
  have ha : a ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
  have he : (∑ j ∈ (Finset.univ : Finset (Fin m)).erase a, F (color a j)) =
      ∑ j ∈ (Finset.univ : Finset (Fin m)).erase a, F 1 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [color, ite_eq_right (Finset.ne_of_mem_erase hj)]
  calc
    _ = (∑ j ∈ (Finset.univ : Finset (Fin m)).erase a, F (color a j)) + F (color a a) :=
      (Finset.sum_erase_add _ _ ha).symm
    _ = _ := by
      rw [he, Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem ha, Finset.card_univ, Fintype.card_fin]
      rw [show color a a = 0 by simp [color]]
      exact Nat.add_comm _ _

lemma rowPartA (d : Small) (u : Fin 35) :
    (∑ i : Fin 35, ∑ r : Fin 4, dd d (A (color u i) r)) =
      ∑ r : Fin 4, (dd d (A 0 r) + 34 * dd d (A 1 r)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  exact sum_color u (fun k => dd d (A k r))

lemma rowPartB (d : Small) (u : Fin 62) :
    (∑ i : Fin 62, ∑ r : Fin 2, dd d (B (color u i) r)) =
      ∑ r : Fin 2, (dd d (B 0 r) + 61 * dd d (B 1 r)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  exact sum_color u (fun k => dd d (B k r))

lemma value_p (v : Big) (r : Fin 4) : value v (P r) = dd (down v v) (P r) := rfl
lemma value_a (v : Big) (i : Fin 35) (r : Fin 4) :
    value v (A i r) = dd (down v v) (A (color (ia v) i) r) := rfl
lemma value_b (v : Big) (i : Fin 62) (r : Fin 2) :
    value v (B i r) = dd (down v v) (B (color (ib v) i) r) := rfl

lemma calc_row (v : Big) : row v = smallRow (down v v) := by
  unfold row smallRow
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  change (∑ p : Fin 4, value v (P p)) +
    ((∑ i : Fin 35, ∑ r : Fin 4, value v (A i r)) +
     (∑ i : Fin 62, ∑ r : Fin 2, value v (B i r))) = _
  simp only [value_p, value_a, value_b, rowPartA, rowPartB]

set_option maxRecDepth 16000
set_option maxHeartbeats 300000
lemma rowPsmall : ∀ r : Fin 4, smallRow (P r) = rp r := by decide
lemma rowAsmall : ∀ r : Fin 4, smallRow (A 0 r) = ra r := by decide
lemma rowBsmall : ∀ r : Fin 2, smallRow (B 0 r) = rb r := by decide

lemma rowP (r : Fin 4) : row (P r) = rp r := by rw [calc_row]; exact rowPsmall r

lemma all_rowA (i : Fin 35) (r : Fin 4) : row (A i r) = ra r := by
  rw [calc_row]
  change smallRow (A (color i i) r) = ra r
  rw [show color i i = 0 by simp [color]]
  exact rowAsmall r

lemma all_rowB (i : Fin 62) (r : Fin 2) : row (B i r) = rb r := by
  rw [calc_row]
  change smallRow (B (color i i) r) = rb r
  rw [show color i i = 0 by simp [color]]
  exact rowBsmall r

lemma totalA (i : Fin 35) : (∑ r : Fin 4, row (A i r)) = 3220 := by
  simp only [all_rowA]
  decide
lemma totalB (i : Fin 62) : (∑ r : Fin 2, row (B i r)) = 1608 := by
  simp only [all_rowB]
  decide
lemma totalP : (∑ r : Fin 4, row (P r)) = 2284 := by
  simp only [rowP]
  decide

lemma sumTracksA : (∑ a : Fin 35 × Fin 4, row (.inr (.inl a))) = 112700 := by
  calc
    _ = ∑ i : Fin 35, ∑ r : Fin 4, row (A i r) := Fintype.sum_prod_type (fun a : Fin 35 × Fin 4 => row (.inr (.inl a)))
    _ = ∑ _i : Fin 35, 3220 := Finset.sum_congr rfl fun i _ => totalA i
    _ = _ := by simp [Finset.sum_const]

lemma sumTracksB : (∑ b : Fin 62 × Fin 2, row (.inr (.inr b))) = 99696 := by
  calc
    _ = ∑ i : Fin 62, ∑ r : Fin 2, row (B i r) := Fintype.sum_prod_type (fun b : Fin 62 × Fin 2 => row (.inr (.inr b)))
    _ = ∑ _i : Fin 62, 1608 := Finset.sum_congr rfl fun i _ => totalB i
    _ = _ := by simp [Finset.sum_const]

lemma splitTriple {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α ⊕ (β ⊕ γ) → Nat) (u v w : Nat)
    (ha : (∑ a : α, f (.inl a)) = u)
    (hb : (∑ b : β, f (.inr (.inl b))) = v)
    (hc : (∑ c : γ, f (.inr (.inr c))) = w) :
    (∑ x : α ⊕ (β ⊕ γ), f x) = u + (v+w) := by
  rw [Fintype.sum_sum_type f, Fintype.sum_sum_type (fun s : β ⊕ γ => f (.inr s)), ha, hb, hc]

theorem row_sum : (∑ v : Big, row v) = 214680 := by
  have hh : 2284 + (112700 + 99696) = 214680 := by norm_num
  exact (splitTriple row 2284 112700 99696 totalP sumTracksA sumTracksB).trans hh

lemma sumRows {V : Type} [Fintype V] (f : V → V → Nat) (r : V → Nat)
    (h : ∀ v, (∑ w : V, f v w) = r v) :
    (∑ p : V × V, f p.1 p.2) = ∑ v : V, r v := by
  calc
    _ = ∑ v : V, ∑ w : V, f v w := Fintype.sum_prod_type (fun p : V × V => f p.1 p.2)
    _ = _ := Finset.sum_congr rfl fun v _ => h v

theorem all_distance_sum : (∑ p : Big × Big, G.dist p.1 p.2) = 214680 := by
  have hr (v : Big) : (∑ w : Big, G.dist v w) = row v :=
    Finset.sum_congr rfl fun w _ => dist_value v w
  exact (sumRows G.dist row hr).trans row_sum

lemma pairs : Wow268.centerPairs G = (Finset.univ : Finset Big).offDiag := by
  ext p
  simp only [Wow268.member_centerPairs, Finset.mem_offDiag, center_all, Finset.mem_univ, true_and]

lemma pair_count : (Wow268.centerPairs G).card = 71556 := by
  rw [pairs, Finset.offDiag_card]
  simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]

lemma sum_offDiag_eq {V : Type} [Fintype V] [DecidableEq V] (f : V × V → Nat)
    (hdiag : ∀ v : V, f (v,v) = 0) :
    (∑ p ∈ (Finset.univ : Finset V).offDiag, f p) = ∑ p : V × V, f p := by
  have he : (Finset.univ : Finset V).offDiag =
      (Finset.univ : Finset (V × V)).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  rintro ⟨v,w⟩ _
  by_cases h : v = w
  · subst w
    simp [hdiag]
  · exact ite_eq_left h

theorem pair_distance_sum : (∑ p ∈ Wow268.centerPairs G, G.dist p.1 p.2) = 214680 := by
  rw [pairs]
  exact (sum_offDiag_eq (fun p : Big × Big => G.dist p.1 p.2) (fun v => G.dist_self (v := v))).trans
    all_distance_sum

theorem avg_exact : Wow268.avg G = (17890/5963 : ℚ) := by
  rw [Wow268.avg, pair_distance_sum, pair_count]
  norm_num

#print axioms avg_exact
end Refute269
