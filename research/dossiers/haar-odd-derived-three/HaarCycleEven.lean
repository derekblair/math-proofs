import HaarHalfCollision

namespace HaarCycleEven
open HaarAllNoncommuting HaarHalfCollision
variable {G : Type*} [Group G]

theorem even_positive {k : ℕ} (pos : 0<k) {x y : G}
    (cycle : HasCycle x y k) : Even k := by
  obtain ⟨v,_,edges⟩ := cycle
  let side (i : ℕ) := (v ⟨i%k,Nat.mod_lt i pos⟩).1
  have step (n : ℕ) : side (n+1) = !side n := by
    have h := (branch x y _ _ (edges ⟨n%k,Nat.mod_lt n pos⟩)).1
    change (v ⟨(n%k+1)%k,Nat.mod_lt _ pos⟩).1 = !side n at h
    have eq : (⟨(n%k+1)%k,Nat.mod_lt _ pos⟩ : Fin k)=⟨(n+1)%k,Nat.mod_lt _ pos⟩ :=
      Fin.ext (Nat.mod_add_mod n k 1)
    rw [eq] at h
    exact h
  have sides (n : ℕ) : side n = (if n%2=0 then side 0 else !side 0) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [step,ih]
      by_cases hn : n%2=0
      · have hs : (n+1)%2 ≠ 0 := by omega
        simp [hn,hs]
      · have hs : (n+1)%2 = 0 := by omega
        simp [hn,hs]
  have wrap : side k=side 0 := by simp [side]
  have eq := sides k
  rw [wrap] at eq
  by_cases h : k%2=0
  · exact Nat.even_iff.mpr h
  · rw [if_neg h] at eq
    exact ((Bool.not_eq_self (side 0)).mp eq.symm).elim

end HaarCycleEven
#print axioms HaarCycleEven.even_positive
