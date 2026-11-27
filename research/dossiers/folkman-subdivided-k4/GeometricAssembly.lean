import GeometricMoment
import GeometricGraphEdit

namespace RobustFolkman
open Finset Moment
variable {Ω V 𝕜 : Type*} [Fintype Ω] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- End-to-end finite reduction. The spherical part of the argument
remains to supply the three quantitative input bounds. -/
theorem from_robust_moments (G : Ω → EdgeGraph V) (pick : Ω → EdgeGraph V → Finset V)
    (p : Ω → 𝕜) (p0 : ∀ ω, 0≤p ω) (p1 : (∑ ω,p ω)=1)
    (good : Ω → Bool) (μ a : 𝕜) (μ0 : 0<μ) (a0 : 0<a)
    (hit : ∀ ω H, H∈forbiddenCopies (G ω) → pick ω H∈H)
    (monoMargin : ∀ ω, good ω=true → ∀ c : Finset V → Bool,
      a*((triangles (G ω)).card : 𝕜) ≤ ((mono (triangles (G ω)) c).card : 𝕜))
    (bound : mean p (bad good) +
       4/μ^2 * mean p (fun ω => (((triangles (G ω)).card : 𝕜)-μ)^2) +
       2/(a*μ) * mean p (fun ω => (charge (triangles (G ω)) (forbiddenCopies (G ω)) (pick ω) : 𝕜)) < 1) :
    ∃ G' : EdgeGraph V, ¬Paraglider.Contains (hasEdge G') ∧
      ∀ c : Finset V → Bool, ∃ t∈triangles G', Monochrom c t := by
  classical
  obtain ⟨ω,go,_,lt⟩ := select_good p p0 p1 good
    (fun w => ((triangles (G w)).card : 𝕜))
    (fun w => (charge (triangles (G w)) (forbiddenCopies (G w)) (pick w) : 𝕜))
    (fun w => Nat.cast_nonneg _) μ a μ0 a0 bound
  have rob (c : Finset V → Bool) :
      charge (triangles (G ω)) (forbiddenCopies (G ω)) (pick ω) < (mono (triangles (G ω)) c).card := by
    exact_mod_cast lt.trans_le (monoMargin ω go c)
  obtain ⟨G',_,no,arrow⟩ := avoid_subdivided_k4 (G ω) (pick ω) (hit ω) rob
  exact ⟨G',no,arrow⟩

#print axioms from_robust_moments
end RobustFolkman
