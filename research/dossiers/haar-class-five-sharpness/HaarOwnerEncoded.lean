import HaarOwnerBind

namespace HaarOwnerEncoded

def owner (raw : ℕ → ℕ) (stride k : ℕ) : ℕ × ℕ := (raw k / stride, raw k % stride)

def check (raw : ℕ → ℕ) (stride s : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, k::ks =>
    i.blt stride && (raw k == s*stride+i) && check raw stride s (i+1) ks

theorem link (raw : ℕ → ℕ) (stride s i : ℕ) (l : List ℕ)
    (h : check raw stride s i l=true) :
    HaarOwnerCertificate.checkShard (owner raw stride) s i l = true := by
  induction l generalizing i with
  | nil => rfl
  | cons k l ih =>
    have h' : (i<stride ∧ raw k=s*stride+i) ∧ check raw stride s (i+1) l = true := by
      simpa [check, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] using h
    have hs : 0<stride := Nat.zero_lt_of_lt h'.1.1
    have own : owner raw stride k = (s,i) := by
      unfold owner
      rw [h'.1.2]
      apply Prod.ext
      · change (s*stride+i)/stride=s
        rw [Nat.mul_comm s stride,Nat.mul_add_div hs,Nat.div_eq_of_lt h'.1.1,Nat.add_zero]
      · change (s*stride+i)%stride=i
        exact Nat.mul_add_mod_of_lt h'.1.1
    simp [HaarOwnerCertificate.checkShard,own,ih _ h'.2]

theorem certify (l : List (List ℕ)) (raw : ℕ → ℕ) (stride : ℕ)
    (h : ∀ s<l.length, check raw stride s 0 l[s]! = true) : l.flatten.Nodup :=
  HaarOwnerBind.certify l (owner raw stride) (fun s hs => link raw stride s 0 _ (h s hs))

end HaarOwnerEncoded
#print axioms HaarOwnerEncoded.certify
