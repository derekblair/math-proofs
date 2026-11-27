import CountableGreedy
import CountableDual

namespace SparseHalfCountableEndpoint
variable {ι : Type*}

/-- The normalized saturated outside bank either has enough free mass,
or the positive fill cost exactly equals the threshold dual. -/
theorem greedy_half (p q : ι → ℝ) (h : ℝ)
    (hs : Summable (fun i => p i+q i))
    (hp : ∀ i, p i≤2) (hq : ∀ i,0≤q i) (hqp : ∀ i,q i≤p i)
    (hmass : (∑' i, (p i+q i))+h=6) :
    5≤h+(∑' i,p i) ∨
    ∃ θ k : ℝ, 0≤θ ∧ θ≤2 ∧ 0≤k ∧ k≤1 ∧
      ∃ x : ι → ℝ,
      (∀ i, x i = if p i<θ then q i else if p i=θ then k*q i else 0) ∧
      (∀ i, 0≤x i ∧ x i≤q i) ∧
      h+(∑' i,p i)+(∑' i,x i)=5 ∧
      (∑' i,p i*x i)=dual p q θ ∧
      (∀ z : ι → ℝ, (∀ i, 0≤z i ∧ z i≤q i) →
        h+(∑' i,p i)+(∑' i,z i)=5 → (∑' i,p i*x i)≤∑' i,p i*z i) := by
  by_cases free : 5≤h+(∑' i,p i)
  · exact Or.inl free
  · right
    have pn i := (hq i).trans (hqp i)
    have sp := Summable.of_nonneg_of_le pn (fun i => by linarith [hq i]) hs
    have sq := Summable.of_nonneg_of_le hq (fun i => by linarith [pn i]) hs
    rw [sp.tsum_add sq] at hmass
    let t := 5-h-(∑' i,p i)
    obtain ⟨θ,k,θ0,θ2,k0,k1,x,shape,feas,tx,cost,best⟩ :=
      greedy p q t sp sq hp hq hqp (by dsimp [t]; linarith) (by dsimp [t]; linarith)
    have eq : (∑' i,q i)-t=1 := by dsimp [t]; linarith
    rw [eq,mul_one] at cost
    refine ⟨θ,k,θ0,θ2,k0,k1,x,shape,feas,?_,cost,?_⟩
    · rw [tx]; dsimp [t]; ring
    · intro z zfeas zfull
      exact best z zfeas (by dsimp [t]; linarith)

#print axioms greedy_half
end SparseHalfCountableEndpoint
