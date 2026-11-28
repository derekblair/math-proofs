import AtlasHostTransport
import AtlasEight

namespace Erdős151.H12

theorem verified_degree_eight_atlas {V : Type*} [Fintype V] [DecidableEq V] :
    DegreeEightAtlas V :=
  atlas_host_transport BikovEight.marked_atlas

/-- Erdős–Gallai–Tuza's K4-free H(n)=12 case, conditional only on
Angeltveit's published finite Ramsey upper bound R(3,10) ≤ 41.
The input is explicit, not a custom Lean axiom. -/
theorem erdos151_k4free_H12_of_Ramsey41 {V : Type*} [Fintype V] [DecidableEq V]
    (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (Ramsey41 : ∀ n, 41 ≤ n → H10.TriangleIndependentTen (Fin n))
    (H : Erdos151H12.TriangleIndependentAtLeast 12 V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-12 ∧
      ∀ C, MaximalNontrivialClique G C → ∃ x ∈ C, x∈T :=
  erdos151_k4free_H12_of_atlas G sym irr link Ramsey41 verified_degree_eight_atlas H

#print axioms verified_degree_eight_atlas
#print axioms erdos151_k4free_H12_of_Ramsey41
end Erdős151.H12
