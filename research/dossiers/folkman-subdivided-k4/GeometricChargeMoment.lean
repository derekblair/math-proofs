import GeometricVariance

namespace RobustFolkman.Moment
open Finset
variable {Ω I J 𝕜 : Type*} [Fintype Ω]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- A charge on candidate graph outcomes can be dominated by two finite
classes of certificates: copies alone and copies with a fresh attachment.
The certificate counts are fixed before sampling; their indicators may
be arbitrarily dependent. -/
theorem expected_charge_upper
    (p : Ω → 𝕜) (p0 : ∀ ω, 0≤p ω)
    (C : Ω → 𝕜) (s : Finset I) (t : Finset J)
    (A : I → Ω → 𝕜) (B : J → Ω → 𝕜) (k a b : 𝕜)
    (k0 : 0≤k)
    (dom : ∀ ω, C ω ≤ k*(∑ i ∈ s, A i ω)+(∑ i ∈ t, B i ω))
    (ma : ∀ i∈s, mean p (A i) ≤ a)
    (mb : ∀ j∈t, mean p (B j) ≤ b) :
    mean p C ≤ k*(s.card : 𝕜)*a+(t.card : 𝕜)*b := by
  let F : Ω → 𝕜 := fun ω => ∑ i ∈ s, A i ω
  let G : Ω → 𝕜 := fun ω => ∑ j ∈ t, B j ω
  have muladd :
      mean p (fun ω => k*F ω+G ω)=k*mean p F+mean p G := by
    unfold mean
    calc
      _ = (∑ ω,(k*(p ω*F ω)+p ω*G ω)) := by
        apply sum_congr rfl
        intro ω _
        ring
      _ = _ := by rw [sum_add_distrib, ←Finset.mul_sum]
  have major : mean p C ≤ mean p (fun ω => k*F ω + G ω) := by
    unfold mean
    exact sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (dom ω) (p0 ω))
  have Aupper : mean p F ≤ (s.card : 𝕜)*a := by
    change mean p (fun ω => ∑ i ∈ s, A i ω) ≤ _
    rw [mean_sum_of]
    exact (sum_le_sum ma).trans_eq (by simp)
  have Bupper : mean p G ≤ (t.card : 𝕜)*b := by
    change mean p (fun ω => ∑ j ∈ t, B j ω) ≤ _
    rw [mean_sum_of]
    exact (sum_le_sum mb).trans_eq (by simp)
  rw [muladd] at major
  rw [mul_assoc]
  exact major.trans (add_le_add (mul_le_mul_of_nonneg_left Aupper k0) Bupper)

#print axioms expected_charge_upper
end RobustFolkman.Moment
