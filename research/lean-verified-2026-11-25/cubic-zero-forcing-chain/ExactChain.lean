import Shape

namespace ZFChain
open Finset

noncomputable def domNumber (n : ℕ) : ℕ := by
  classical
  exact Nat.find (p := fun k => ∃ D : Finset (V n), Dominates D ∧ D.card = k)
    ⟨_, domWitness n⟩

noncomputable def zeroForcingNumber (n : ℕ) : ℕ := by
  classical
  exact Nat.find (p := fun k => ∃ S : Finset (V n), Reach adj S univ ∧ S.card = k)
    ⟨_, forceWitness n⟩

theorem exactDom (n : ℕ) : domNumber n = 7*(n+2)/3 := by
  classical
  have hex : ∃ k, ∃ D : Finset (V n), Dominates D ∧ D.card = k := ⟨_,domWitness n⟩
  have h₁ := Nat.find_min' hex (domWitness n)
  obtain ⟨D,hD,hk⟩ := Nat.find_spec hex
  have h₂ := chainDomLower D hD
  change D.card = domNumber n at hk
  change domNumber n ≤ 2*(n+2)+(n+2)/3 at h₁
  omega

theorem exactZF (n : ℕ) : zeroForcingNumber n = 3*(n+2)+1 := by
  classical
  have hex : ∃ k, ∃ S : Finset (V n), Reach adj S univ ∧ S.card = k := ⟨_,forceWitness n⟩
  have h₁ := Nat.find_min' hex (forceWitness n)
  obtain ⟨S,hS,hk⟩ := Nat.find_spec hex
  have h₂ := chainForcingLower n S hS
  change S.card = zeroForcingNumber n at hk
  change zeroForcingNumber n ≤ 3*(n+2)+1 at h₁
  omega

/-- Section 7's simultaneous formulas for the source chain with k ≥ 2 blocks.
    Chain index n is k-2; ports and all edges are specified by Chain.lean. -/
theorem publishedChainConjecture (k : ℕ) (hk : 2 ≤ k) :
    domNumber (k-2) = 7*k/3 ∧ zeroForcingNumber (k-2) = 3*k+1 := by
  have h : k-2+2 = k := by omega
  simp only [exactDom,exactZF,h,and_self]

/-- A single connected cubic triangle-free family has no bounded additive gap. -/
theorem unboundedGap (c : ℕ) :
    ∃ n, (chain n).Connected ∧
      (haveI := Classical.decRel (chain n).Adj; ∀ x, (chain n).degree x = 3) ∧
      (∀ x y z, (chain n).Adj x y → (chain n).Adj y z → ¬ (chain n).Adj z x) ∧
      c + domNumber n < zeroForcingNumber n := by
  refine ⟨3*c,connectedChain _,?_,graph_triangleFree,?_⟩
  · intro x
    exact chain_degree x
  · rw [exactDom,exactZF]
    omega

#print axioms publishedChainConjecture
#print axioms unboundedGap
end ZFChain
