import GeometricAssembly
import GeometricChargeCount
import GeometricTriangleCount

namespace RobustFolkman
open Finset Moment
variable {Ω V K : Type*} [Fintype Ω] [DecidableEq V] [Fintype V]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The fixed-pattern probabilities suffice for the actual Folkman conclusion.
The analytic random-graph argument still needs to supply these probabilities,
a spectral coloring margin with small exceptional mass, and the combined
strict numerical inequality. -/
theorem from_pattern_probabilities (p : Ω→K) (p0 : ∀ ω, 0≤p ω) (p1 : (∑ ω,p ω)=1)
    (G : Ω → EdgeGraph V) (good : Ω → Bool) (a u d ph pj : K) (a0 : 0<a) (d0 : 0≤d)
    (mean0 : 0<(↑((Fintype.card V).choose 3) : K)*u)
    (m : ∀ i∈(univ : Finset V).powersetCard 3, mean p (fun ω => triangleIndicator (G ω) i)=u)
    (cor : ∀ i j, i∈(univ : Finset V).powersetCard 3 → j∈(univ : Finset V).powersetCard 3 →
      i≠j → (j∩i).card≠2 →
      mean p (fun ω => triangleIndicator (G ω) i * triangleIndicator (G ω) j) ≤ u^2)
    (dia : ∀ i j, i∈(univ : Finset V).powersetCard 3 → j∈(univ : Finset V).powersetCard 3 →
      i≠j → (j∩i).card=2 →
      mean p (fun ω => triangleIndicator (G ω) i * triangleIndicator (G ω) j) ≤ d)
    (mh : ∀ r : Tuple5 V, mean p (fun ω => copyIndicator (G ω) r) ≤ ph)
    (mj : ∀ rw : Tuple5 V × V, mean p (fun ω => freshIndicator (G ω) rw) ≤ pj)
    (monoMargin : ∀ ω, good ω=true → ∀ c : Finset V → Bool,
      a*((triangles (G ω)).card : K) ≤ ((mono (triangles (G ω)) c).card : K))
    (bound :
      let μ := (↑((Fintype.card V).choose 3) : K)*u
      mean p (bad good) +
        4/μ^2 * ((↑((Fintype.card V).choose 3) : K)*(u+(↑(3*(Fintype.card V-3)) : K)*d)) +
        2/(a*μ) * (3*(Fintype.card V : K)^5*ph+(Fintype.card V : K)^6*pj) < 1) :
    ∃ G' : EdgeGraph V, ¬Paraglider.Contains (hasEdge G') ∧
      ∀ c : Finset V → Bool, ∃ t∈triangles G', Monochrom c t := by
  apply from_robust_moments G (fun _ => marked) p p0 p1 good _ a mean0 a0
    (fun ω H h => marked_hit (G ω) H h) monoMargin
  have variance := variance_actual_triangles_upper p p1 G u d d0 m cor dia
  have charge := mean_actual_charge_upper p p0 G ph pj mh mj
  let μ : K := (↑((Fintype.card V).choose 3) : K)*u
  have cv : 0≤(4:K)/μ^2 := div_nonneg (by norm_num) (sq_nonneg _)
  have cc : 0≤(2:K)/(a*μ) := div_nonneg (by norm_num) (mul_nonneg a0.le mean0.le)
  exact (add_le_add (add_le_add_right
    (mul_le_mul_of_nonneg_left variance cv) _)
    (mul_le_mul_of_nonneg_left charge cc)).trans_lt bound

#print axioms from_pattern_probabilities
end RobustFolkman
