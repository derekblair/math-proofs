import Lean.Elab.Tactic.Omega

namespace QuorumMinimum

theorem half8 (s : Nat → Nat) (j : Nat)
    (H : ∀ i, 8*s (i+1) ≤ 7*s i) :
    2 * s (j+8) ≤ s j := by
  have a := H j
  have b := H (j+1)
  have c := H (j+2)
  have d := H (j+3)
  have e := H (j+4)
  have f := H (j+5)
  have g := H (j+6)
  have h := H (j+7)
  change 8*s (j+2) ≤ 7*s (j+1) at b
  change 8*s (j+3) ≤ 7*s (j+2) at c
  change 8*s (j+4) ≤ 7*s (j+3) at d
  change 8*s (j+5) ≤ 7*s (j+4) at e
  change 8*s (j+6) ≤ 7*s (j+5) at f
  change 8*s (j+7) ≤ 7*s (j+6) at g
  change 8*s (j+8) ≤ 7*s (j+7) at h
  omega

theorem geometric (s : Nat → Nat) (L : Nat)
    (H : ∀ i, 8*s (i+1) ≤ 7*s i) :
    2^L*s (8*L) ≤ s 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
    have step : 2*s (8*(L+1)) ≤ s (8*L) := by
      have he : 8*(L+1)=8*L+8 := by omega
      simpa only [he] using half8 s (8*L) H
    calc
      2^(L+1)*s (8*(L+1)) = 2^L*(2*s (8*(L+1))) := by
        rw [Nat.pow_succ,Nat.mul_assoc]
      _ ≤ 2^L*s (8*L) := Nat.mul_le_mul_left _ step
      _ ≤ s 0 := ih

/-- Independent arithmetic step for peeling full classes. Once the remaining
support is smaller than T, its size itself bounds the remaining color count. -/
theorem reaches_small (s : Nat → Nat) (L T : Nat) (t2 : 2 ≤ T)
    (init : s 0 ≤ 2^L) (mono : ∀ i, s (i+1) ≤ s i)
    (H : ∀ i, T ≤ s i → 8*s (i+1) ≤ 7*s i) :
    s (8*L) < T := by
  let u (i : Nat) : Nat := if T ≤ s i then s i else 0
  have shrink : ∀ i, 8*u (i+1) ≤ 7*u i := by
    intro i
    by_cases y : T ≤ s (i+1)
    · have x : T ≤ s i := Nat.le_trans y (mono i)
      simpa [u,x,y] using H i x
    · simp [u,y]
  have le := Nat.le_trans (geometric u L shrink)
    (show u 0 ≤ 2^L by unfold u; split <;> omega)
  by_cases ge : T ≤ s (8*L)
  · have ht : 2 ≤ u (8*L) := by simpa [u,ge] using Nat.le_trans t2 ge
    have big : 2^L*2 ≤ 2^L*u (8*L) := Nat.mul_le_mul_left _ ht
    rw [Nat.mul_two] at big
    have pos : 0 < (2:Nat)^L := Nat.pow_pos (by decide)
    omega
  · exact Nat.lt_of_not_ge ge

#print axioms reaches_small

end QuorumMinimum
