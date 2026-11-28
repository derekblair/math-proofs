import UnblockingTheorem
import MaximalClique
import RamseyExoo
import RamseyPullback
import Mathlib.Data.Fintype.EquivFin

namespace Erdős151

theorem eleven_implies_at_least_47 {V : Type*} [Fintype V]
    (H : TriangleIndependentEleven V) : 47 ≤ Fintype.card V := by
  classical
  by_contra h
  have hs : Fintype.card V ≤ 46 := by omega
  obtain ⟨R,sym,irr,tf,cap⟩ :=
    Erdos151Ramsey.triangleFree_fin_mono hs Erdos151Ramsey.Exoo.ramsey311_ge47
  let f := (Fintype.equivFin V).toEmbedding
  obtain ⟨S,hS,hind⟩ := H (fun a b => R (f a) (f b))
    (fun {_ _} h => sym _ _ h) (fun a => irr (f a))
    (Erdos151Ramsey.pullback_triangleFree f R tf)
  have hb := Erdos151Ramsey.pullback_independence_cap f R 10 cap S hind
  omega

/-- Erdős–Gallai–Tuza clique transversal conjecture for K4-free
graphs in the Ramsey regime H(n)=11. The input H is the lower-bound half
H(n)≥11; the conclusion in fact holds under this weaker input. -/
theorem erdos151_k4free_H11 {V : Type*} [Fintype V] (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G) (H : TriangleIndependentEleven V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V - 11 ∧
      ∀ C, MaximalNontrivialClique G C → ∃ x ∈ C, x ∈ T := by
  classical
  have hn := eleven_implies_at_least_47 H
  obtain ⟨S,hs,hfree⟩ := k4free_of_triangle_independent_eleven G sym irr link hn H
  let T := Finset.univ \ S
  refine ⟨T, ?_, ?_⟩
  · dsimp only [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  · have hit := (free_iff_complement_hits G sym irr link (S : Set V)).mp hfree
    intro C hc
    obtain ⟨x,hx,hnot⟩ := hit C hc
    exact ⟨x,hx,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnot⟩⟩

#print axioms eleven_implies_at_least_47
#print axioms erdos151_k4free_H11
end Erdős151
