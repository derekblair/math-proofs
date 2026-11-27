import HaarClass3Odd

namespace HaarVoltage
open HaarCycle HaarAllNoncommuting

variable {G H : Type*} [Group G] [Group H]

def withLabel (x y : G) (s : G) := s = 1 ∨ s = x ∨ s = y

def stepLabel (b : Bool) (s : G) := if b then s⁻¹ else s

theorem labeled_of_adj (φ : G →* H) (x y : G) (a b : Bool × H)
    (h : haarAdj (φ x) (φ y) a b) :
    ∃ s, withLabel x y s ∧ a.1 ≠ b.1 ∧ b.2 = a.2 * φ (stepLabel a.1 s) := by
  rcases a with ⟨a,u⟩
  rcases b with ⟨b,v⟩
  cases a <;> cases b <;> simp [haarAdj] at h
  · rcases h with e | e | e
    · exact ⟨1,Or.inl rfl,by simp,by simpa [stepLabel] using e⟩
    · exact ⟨x,Or.inr (Or.inl rfl),by simp,by simpa [stepLabel] using e⟩
    · exact ⟨y,Or.inr (Or.inr rfl),by simp,by simpa [stepLabel] using e⟩
  · rcases h with e | e | e
    · exact ⟨1,Or.inl rfl,by simp,by simpa [stepLabel] using e.symm⟩
    · refine ⟨x,Or.inr (Or.inl rfl),by simp,?_⟩
      change v = u * φ (stepLabel true x)
      rw [e]; simp [stepLabel,mul_assoc]
    · refine ⟨y,Or.inr (Or.inr rfl),by simp,?_⟩
      change v = u * φ (stepLabel true y)
      rw [e]; simp [stepLabel,mul_assoc]

theorem adj_of_labeled (x y : G) (a b : Bool × G) (s : G)
    (hs : withLabel x y s) (hn : a.1 ≠ b.1) (h : b.2 = a.2 * stepLabel a.1 s) :
    haarAdj x y a b := by
  rcases a with ⟨a,u⟩
  rcases b with ⟨b,v⟩
  cases a <;> cases b <;> simp at hn
  · change v = u * stepLabel false s at h
    rw [h]
    rcases hs with rfl | rfl | rfl <;> simp [haarAdj,stepLabel]
  · change v = u * stepLabel true s at h
    have h' : u = v*s := by rw [h]; simp [stepLabel,mul_assoc]
    rcases hs with rfl | rfl | rfl <;> simp [haarAdj,h']

def index (k : ℕ) [NeZero k] (i : ℕ) : Fin k :=
  ⟨i%k, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne k))⟩

theorem index_succ (k : ℕ) [NeZero k] (i : ℕ) : index k (i+1) = index k i + 1 := by
  apply Fin.ext
  change (i+1)%k = (_+_)%k
  rw [Nat.add_mod i 1]

theorem index_lt (k : ℕ) [NeZero k] {i : ℕ} (h : i < k) : (index k i).val=i :=
  Nat.mod_eq_of_lt h

theorem index_period (k : ℕ) [NeZero k] (i : ℕ) : index k (k+i)=index k i := by
  apply Fin.ext
  exact Nat.add_mod_left k i

def pathVal {k : ℕ} [NeZero k] (L : Fin k → G) : ℕ → G
  | 0 => 1
  | n+1 => pathVal L n * L (index k n)

theorem prefix_period {k : ℕ} [NeZero k] (L : Fin k → G) (n : ℕ) :
    pathVal L (k+n) = pathVal L k * pathVal L n := by
  induction n with
  | zero => simp [pathVal]
  | succ n ih =>
    change pathVal L (k+n) * L (index k (k+n)) = pathVal L k * (pathVal L n * L (index k n))
    rw [index_period,ih,mul_assoc]

theorem prefix_blocks {k : ℕ} [NeZero k] (L : Fin k → G) (q r : ℕ) :
    pathVal L (q*k+r) = pathVal L k ^ q * pathVal L r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q+1)*k+r=k+(q*k+r) by rw [Nat.add_mul]; omega,
      prefix_period, ih,pow_succ',mul_assoc]

theorem prefix_project (φ : G →* H) {k : ℕ} [NeZero k] (B : Fin k → Bool × H)
    (L : Fin k → G)
    (h : ∀ i, (B (i+1)).2 = (B i).2 * φ (L i)) (n : ℕ) :
    (B (index k 0)).2 * φ (pathVal L n) = (B (index k n)).2 := by
  induction n with
  | zero => simp [pathVal]
  | succ n ih =>
    rw [pathVal,map_mul,← mul_assoc,ih,index_succ,h]

theorem voltage_kernel (φ : G →* H) {k : ℕ} [NeZero k] (B : Fin k → Bool × H)
    (L : Fin k → G) (h : ∀ i, (B (i+1)).2 = (B i).2 * φ (L i)) :
    pathVal L k ∈ φ.ker := by
  have e := prefix_project φ B L h k
  have i : index k k = index k 0 := by simpa only [Nat.add_zero] using index_period k 0
  rw [i] at e
  change φ (pathVal L k) = 1
  exact mul_left_cancel (e.trans (mul_one _).symm)

end HaarVoltage

#print axioms HaarVoltage.voltage_kernel
