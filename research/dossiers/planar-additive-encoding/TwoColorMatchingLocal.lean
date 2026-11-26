import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace TwoColorMatchingLocal

/-- Adjacent indices on an alternating path have differences 0 and 1.
Within a path on at most (2m-1) vertices, no other difference is mistaken
for either adjacent difference modulo (m). -/
theorem path_residues (m : ℕ) (hm : 2 ≤ m) [NeZero m] (d : ℤ)
    (lo : 2 - (m : ℤ) ≤ d) (hi : d ≤ (m : ℤ) - 1) :
    (((d : ZMod m) = 0) ↔ d = 0) ∧ (((d : ZMod m) = 1) ↔ d = 1) := by
  have H (s : ℤ) (hs : 0 ≤ s ∧ s ≤ 1) :
      ((d : ZMod m) = (s : ZMod m)) ↔ d = s := by
    rw [← sub_eq_zero,← Int.cast_sub,ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨k,e⟩
      by_contra ne
      have kp : k ≠ 0 := by
        intro zz
        simp [zz] at e
        omega
      rcases lt_or_gt_of_ne kp with kneg|kpos
      · have em : (m : ℤ)*(k+1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
        nlinarith
      · have em : 0 ≤ (m : ℤ)*(k-1) :=
          mul_nonneg (by positivity) (by omega)
        nlinarith
    · intro e
      simp [e]
  exact ⟨by simpa using H 0 (by omega), by simpa using H 1 (by omega)⟩

/-- Along alternating edges with labels zero and t, the B-potentials form
an arithmetic progression. The repeated endpoint of a cycle of half-length
k therefore forces k•t=0. -/
theorem walk_torsion {G : Type*} [AddCommGroup G] (B C : ℕ → G) (t : G) (k : ℕ)
    (h0 : ∀ i < k, B i + C i = 0) (h1 : ∀ i < k, B (i+1) + C i = t)
    (close : B k = B 0) : k • t = 0 := by
  have step (i : ℕ) (hi : i < k) : B (i+1) = B i + t := by
    apply add_right_cancel (b := C i)
    rw [h1 i hi]
    rw [add_right_comm,h0 i hi,zero_add]
  have pos (i : ℕ) (hi : i ≤ k) : B i = B 0 + i • t := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [step i (by omega),ih (by omega),succ_nsmul,add_assoc]
  have e := pos k (Nat.le_refl k)
  rw [close] at e
  exact (add_left_cancel ((add_zero (B 0)).trans e)).symm

/-- A length-(2m-1) path oriented from B starts with the 0-edge and
ends with a 0-edge. A modulus-m label difference falsely forces its two
endpoints to be joined by a 1-edge. -/
theorem path_forces_false {G : Type*} [AddCommGroup G] (B C : ℕ → G) (t : G)
    (m : ℕ) (hm : 2 ≤ m) (zero : m • t = 0)
    (h0 : ∀ i < m, B i + C i = 0) (h1 : ∀ i < m-1, B (i+1) + C i = t) :
    B 0 + C (m-1) = t := by
  have step (i : ℕ) (hi : i < m-1) : B (i+1) = B i + t := by
    apply add_right_cancel (b := C i)
    rw [h1 i hi]
    rw [add_right_comm,h0 i (by omega),zero_add]
  have pos (i : ℕ) (hi : i ≤ m-1) : B i = B 0 + i • t := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [step i (by omega),ih (by omega),succ_nsmul,add_assoc]
  have e := h0 (m-1) (by omega)
  rw [pos (m-1) (Nat.le_refl _)] at e
  have mz : (m-1) • t + t = 0 := by
    rw [← succ_nsmul,show m-1+1=m by omega,zero]
  apply add_left_cancel (a := (m-1) • t)
  rw [mz,add_left_comm]
  simpa only [add_assoc] using e

/-- Different path or cycle components can share the same local group
without creating any accidental joint hits: add opposite integer tags. -/
theorem component_tags {A B C G : Type*} [AddCommGroup G]
    (f : A → G) (g : B → G) (h : C → G) (bcomp : B → ℤ) (ccomp : C → ℤ)
    (a : A) (b : B) (c : C) :
    ((f a, (0 : ℤ)) + (g b,bcomp b) + (h c,-ccomp c) : G × ℤ) = 0 ↔
      f a + g b + h c = 0 ∧ bcomp b = ccomp c := by
  change (f a + g b + h c, 0+bcomp b+-ccomp c) = (0,0) ↔ _
  simp only [Prod.mk.injEq,zero_add,← sub_eq_add_neg,sub_eq_zero]

end TwoColorMatchingLocal

#print axioms TwoColorMatchingLocal.path_residues
#print axioms TwoColorMatchingLocal.walk_torsion
#print axioms TwoColorMatchingLocal.path_forces_false
#print axioms TwoColorMatchingLocal.component_tags
