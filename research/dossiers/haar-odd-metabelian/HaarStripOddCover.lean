import HaarStripComplete
import HaarStripGauge

namespace HaarStripOddCover
open HaarStripVoltage
variable {A : Type*} [AddCommGroup A]

theorem finite_odd_noTwo [Finite A] (hodd : Odd (Nat.card A)) (a : A) (h : a+a=0) : a=0 := by
  have h2 : addOrderOf a ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by simpa [two_nsmul] using h)
  have hA : addOrderOf a ∣ Nat.card A := addOrderOf_dvd_natCard a
  have e : addOrderOf a ≤ 2 := Nat.le_of_dvd (by decide) h2
  have odd : ¬ 2 ∣ Nat.card A := by
    rcases hodd with ⟨k,hk⟩
    intro q
    rcases q with ⟨l,hl⟩
    omega
  have a1 : addOrderOf a = 1 := by
    have n : addOrderOf a ≠ 0 := by
      intro e0
      rw [e0] at h2
      exact (by decide : ¬ (0 : Nat) ∣ 2) h2
    have n2 : addOrderOf a ≠ 2 := by
      intro e2
      rw [e2] at hA
      exact odd hA
    omega
  simpa using a1

theorem any_cover (W : B → B → A) (anti : ∀ u v, W v u = -W u v)
    (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarStripGauge.HasCycle W n := by
  obtain ⟨n, hn, hc⟩ := HaarStripData.any_voltage (HaarStripGauge.map W) noTwo
  exact ⟨n,hn,HaarStripGauge.ungauge W anti hc⟩

theorem finite_odd [Finite A] (hodd : Odd (Nat.card A))
    (W : B → B → A) (anti : ∀ u v, W v u = -W u v) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarStripGauge.HasCycle W n :=
  any_cover W anti (finite_odd_noTwo hodd)

end HaarStripOddCover
#print axioms HaarStripOddCover.finite_odd
