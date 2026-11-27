import CountableDual

namespace SparseHalfCountableEndpoint
variable {ι : Type*}

/-- The heavy-isolate budget leaves exactly one nontrivial block, on an
arbitrary summable bank. In graph units this is the completed C₅ shape. -/
theorem large_isolate (p q : ι → ℝ) (θ h : ℝ)
    (hθ : 0≤θ ∧ θ≤2)
    (hp : ∀ i, p i≤2) (hq : ∀ i, 0≤q i) (hqp : ∀ i, q i≤p i)
    (hs : Summable (fun i => p i+q i))
    (hh : 2≤h) (hmass : (∑' i, (p i+q i))+h=6)
    (obs : 2≤dual p q θ) :
    θ=2 ∧ h=2 ∧ ∃ j : ι, p j=2 ∧ q j=2 ∧
      ∀ i≠j, p i=0 ∧ q i=0 := by
  have bd := small_price_bound p q θ h hθ.1 hq hqp hs hmass
  have z := mul_nonneg hθ.1 (show 0≤h-2 by linarith)
  have θ2 : θ=2 := by nlinarith
  have h2 : h=2 := by rw [θ2] at bd obs; nlinarith
  have f : (fun i => q i*min θ (p i)) = (fun i => q i*(p i)) :=
    funext fun i => by rw [θ2,min_eq_right (hp i)]
  unfold dual at obs
  rw [f,θ2] at obs
  have p0 i := (hq i).trans (hqp i)
  have lowest i : 0≤q i*p i := mul_nonneg (hq i) (p0 i)
  have middle i : q i*p i≤2*q i := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hp i) (hq i)
  have upper i : q i*p i≤p i+q i := by linarith [middle i,hqp i]
  have hm : (∑' i, (p i+q i))≤ ∑' i, q i*p i := by linarith
  have sat := rigid_of_summable_gap _ _ hs lowest upper hm
  have pair i : (p i=0 ∧ q i=0) ∨ (p i=2 ∧ q i=2) := by
    have pq : p i=q i := by linarith [sat i,middle i,hqp i]
    have hi := sat i
    rw [pq] at hi
    have z : q i*(q i-2)=0 := by nlinarith
    rcases mul_eq_zero.mp z with z | z
    · left; exact ⟨pq.trans z,z⟩
    · right; have q2 := sub_eq_zero.mp z; exact ⟨pq.trans q2,q2⟩
  obtain ⟨s,mem,out,total⟩ := exact_support p q (by norm_num : (0:ℝ)<2)
    (by norm_num : (0:ℝ)≤2) hs pair hmass
  have cs : (s.card:ℝ)=1 := by linarith
  have cs' : s.card=1 := by exact_mod_cast cs
  obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp cs'
  have pj := (mem j).1 (Finset.mem_singleton_self _)
  exact ⟨θ2,h2,j,pj.1,pj.2,fun i hi => out i (fun h => hi (Finset.mem_singleton.mp h))⟩

#print axioms large_isolate
end SparseHalfCountableEndpoint
