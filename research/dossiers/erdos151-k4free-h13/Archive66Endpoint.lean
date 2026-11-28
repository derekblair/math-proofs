import Archive66Numeric

namespace Erdos151Ramsey.Archive66
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem graph_symm {a b : Fin 66} (h : graph a b) : graph b a := by
  have t : ∀ x y : Fin 66, graph x y → graph y x := by decide +kernel
  exact t _ _ h

theorem graph_irrefl : ∀ a : Fin 66, ¬ graph a a := by decide +kernel

private theorem triangle_check : ∀ a b : Fin 66,
    (adj a b = true) → (masks[a.val]! &&& masks[b.val]!) = 0 := by
  decide +kernel

theorem graph_triangle_free : TriangleFree graph := by
  intro a b c hab hbc hac
  have hz := congrArg (fun m : Nat => m.testBit c.val) (triangle_check a b hab)
  change masks[b.val]!.testBit c.val = true at hbc
  change masks[a.val]!.testBit c.val = true at hac
  simp [hbc, hac] at hz

theorem alpha_le_thirteen (S : Finset (Fin 66)) (ind : Independent graph S) : S.card ≤ 13 := by
  apply Nat.le_of_lt_succ
  apply check_sound p0 73786976294838206463 14 c0 S _ ind
  intro x hx
  simp only [vv, Finset.mem_filter, Finset.mem_univ, true_and]
  have E : (73786976294838206463 : Nat) = 2^66-1 := rfl
  rw [E, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true x.isLt

theorem alphaWitness_card : alphaWitness.card = 13 := by decide +kernel

theorem alphaWitness_ind : Independent graph alphaWitness := by
  change ∀ a ∈ alphaWitness, ∀ b ∈ alphaWitness, ¬ graph a b
  decide +kernel

theorem ramsey314_ge67 :
    ∃ R : Fin 66 → Fin 66 → Prop, (∀ {a b}, R a b → R b a) ∧ (∀ a, ¬ R a a) ∧
      TriangleFree R ∧ (∀ S : Finset (Fin 66), Independent R S → S.card ≤ 13) :=
  ⟨graph, @graph_symm, graph_irrefl, graph_triangle_free, alpha_le_thirteen⟩

theorem not_universal14 :
    ¬ (∀ R : Fin 66 → Fin 66 → Prop, (∀ {a b}, R a b → R b a) → (∀ a, ¬ R a a) →
      TriangleFree R → ∃ S : Finset (Fin 66), 14 ≤ S.card ∧ Independent R S) := by
  intro h
  obtain ⟨S, hs, hI⟩ := h graph @graph_symm graph_irrefl graph_triangle_free
  have := alpha_le_thirteen S hI
  omega

#print axioms ramsey314_ge67
#print axioms not_universal14
end Erdos151Ramsey.Archive66
