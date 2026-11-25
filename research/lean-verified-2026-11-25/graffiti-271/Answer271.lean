import Degree271

namespace Wow271
open Wow268
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def maxDegreeDistance (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : V×V => MaxDegree G p.1 ∧ MaxDegree G p.2)).sup
    (fun p => G.dist p.1 p.2)

lemma maximum_square_bound (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    {S : Finset V} (h : TotalDominating G S) : 2*maxDegreeDistance G≤S.card^2 := by
  classical
  have hd : maxDegreeDistance G≤S.card^2/2 := by
    unfold maxDegreeDistance
    apply Finset.sup_le
    intro p hp
    obtain ⟨ha,hb⟩ := (Finset.mem_filter.mp hp).2
    have h' := square_bound hc h ha hb
    exact (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (by omega)
  omega

/-- Written on the Wall II, Conjecture 271. The maximum is over pairs of
    maximum-degree vertices, with value zero for a singleton. -/
theorem conjecture271 (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hc : G.Connected) :
    Int.ceil (Real.sqrt (2*(maxDegreeDistance G:ℝ))) ≤ (gammaT G hc:ℤ) := by
  classical
  obtain ⟨S,hS,hTd⟩ := Nat.find_spec (td_exists G hc)
  have hs : S.card=gammaT G hc := hS
  have hsq := maximum_square_bound G hc hTd
  apply Int.ceil_le.mpr
  change Real.sqrt (2*(maxDegreeDistance G:ℝ)) ≤ (gammaT G hc:ℝ)
  refine Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩
  rw [←hs]
  exact_mod_cast hsq

#print axioms conjecture271
end Wow271
