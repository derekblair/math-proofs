import HostIncidence
import CoreExtractMinimal
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open scoped BigOperators
namespace Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]

def asSimple (G : V → V → Prop) (sym : ∀ {a b}, G a b → G b a)
    (irr : ∀ a, ¬G a a) : SimpleGraph V := ⟨G,⟨fun {_ _} h => sym h⟩,⟨irr⟩⟩

theorem clique_rosters_closed (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ t ∈ G.cliqueFinset 3, ∀ e ⊆ t, (e:Finset V).card = 2 → e ∈ G.cliqueFinset 2 := by
  intro t ht e he hc
  apply SimpleGraph.mem_cliqueFinset_iff.mpr
  exact ⟨(SimpleGraph.mem_cliqueFinset_iff.mp ht).isClique.subset (by simpa using he),hc⟩

theorem sum_vertex_triangle_counts (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, ((G.cliqueFinset 3).filter (fun t => v ∈ t)).card) =
      3 * (G.cliqueFinset 3).card := by
  let T := G.cliqueFinset 3
  have eq (v : V) : ((G.cliqueFinset 3).filter (fun t => v∈t)).card =
      ∑ t ∈ T, if v∈t then (1:ℕ) else 0 := by
    rw [← Finset.sum_filter]; simp [T]
  simp only [eq]
  rw [Finset.sum_comm]
  have hc (t : Finset V) (ht : t∈T) : (∑ v : V, if v∈t then (1:ℕ) else 0) = 3 := by
    rw [← Finset.sum_filter]
    simpa using (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  rw [show (∑ t ∈ T, ∑ v : V, if v∈t then (1:ℕ) else 0) = ∑ _t ∈ T, (3:ℕ)
      from Finset.sum_congr rfl hc]
  simp [T,Nat.mul_comm]

#print axioms clique_rosters_closed
#print axioms sum_vertex_triangle_counts
end Erdős151.H12
