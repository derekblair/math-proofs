import Mathlib.Tactic

namespace HaarMetaShortRelations

private def order (r : Fin 6) (p : Fin 3) : Fin 3 :=
  match r.val with
  | 0 => ![0,1,2] p
  | 1 => ![0,2,1] p
  | 2 => ![1,0,2] p
  | 3 => ![1,2,0] p
  | 4 => ![2,0,1] p
  | _ => ![2,1,0] p

private def inverseOrder (r : Fin 6) (p : Fin 3) : Fin 3 :=
  match r.val with
  | 3 => order 4 p
  | 4 => order 3 p
  | _ => order r p

/-- The six allowed reorderings of the original three ports. -/
def perm (r : Fin 6) : Equiv.Perm (Fin 3) where
  toFun := order r
  invFun := inverseOrder r
  left_inv := by
    have h (s : Fin 6) : ∀ p, inverseOrder s (order s p) = p := by decide +revert
    exact h r
  right_inv := by
    have h (s : Fin 6) : ∀ p, order s (inverseOrder s p) = p := by decide +revert
    exact h r

private def portVec (p : Fin 3) : ℤ × ℤ := ![(0,0),(1,0),(0,1)] p

private def factor (f : Fin 4) : ℤ := ![1,-1,2,-2] f

private def form (t : Fin 7) : ℤ × ℤ :=
  ![(1,0), (2,-1), (3,-1), (4,-1), (5,-2), (3,0), (-6,3)] t

private def vec (r : Fin 6) (t : Fin 7) : ℤ × ℤ :=
  let x := portVec (order r 1) - portVec (order r 0)
  let y := portVec (order r 2) - portVec (order r 0)
  (form t).1 • x + (form t).2 • y

private theorem certificate (i j : Fin 7) :
    (i.val : ℤ) - 3 ≠ 0 ∨ (j.val : ℤ) - 3 ≠ 0 →
      ∃ (r : Fin 6) (t : Fin 7) (f : Fin 4),
        factor f • vec r t = ((i.val : ℤ) - 3, (j.val : ℤ) - 3) := by
  decide +revert

variable {A : Type*} [AddCommGroup A]

/-- The original ordered ports in the additive quotient. -/
def ports (a b : A) (p : Fin 3) : A := ![0,a,b] p

private def eval (a b : A) : (ℤ × ℤ) →+ A where
  toFun v := v.1 • a + v.2 • b
  map_zero' := by simp
  map_add' _ _ := by simp [add_zsmul]; abel

private theorem eval_port (a b : A) (p : Fin 3) :
    eval a b (portVec p) = ports a b p := by
  fin_cases p <;> simp [eval, portVec, ports]

private theorem cancel_factor (h₂ : ∀ z : A, (2 : ℤ) • z = 0 → z = 0)
    (f : Fin 4) (z : A) (h : factor f • z = 0) : z = 0 := by
  fin_cases f
  · simpa [factor] using h
  · simpa [factor] using h
  · exact h₂ z (by simpa [factor] using h)
  · apply h₂ z
    have hh : (-(2 : ℤ)) • z = 0 := by simpa [factor] using h
    simpa [neg_smul] using hh

/-- The seven relevant normal forms after permutation and translation of the ports. -/
def NormalForm (x y : A) : Prop :=
  x = 0 ∨ y = (2 : ℤ) • x ∨ y = (3 : ℤ) • x ∨ y = (4 : ℤ) • x ∨
  (5 : ℤ) • x = (2 : ℤ) • y ∨ (3 : ℤ) • x = 0 ∨
  (3 : ℤ) • (y - (2 : ℤ) • x) = 0

private theorem form_sound (x y : A) (t : Fin 7)
    (h : (form t).1 • x + (form t).2 • y = 0) : NormalForm x y := by
  fin_cases t
  · exact Or.inl (by simpa [form] using h)
  · apply Or.inr; apply Or.inl
    exact (sub_eq_zero.mp (by simpa [form, sub_eq_add_neg] using h : (2 : ℤ) • x - y = 0)).symm
  · apply Or.inr; apply Or.inr; apply Or.inl
    exact (sub_eq_zero.mp (by simpa [form, sub_eq_add_neg] using h : (3 : ℤ) • x - y = 0)).symm
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    exact (sub_eq_zero.mp (by simpa [form, sub_eq_add_neg] using h : (4 : ℤ) • x - y = 0)).symm
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    exact sub_eq_zero.mp (by simpa [form, sub_eq_add_neg, neg_smul] using h)
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    simpa [form] using h
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    rw [smul_sub, smul_smul, sub_eq_add_neg, add_comm]
    simpa [form, neg_smul] using h

/-- A nonzero short relation in a group without 2-torsion yields a canonical
relation for a permuted port list, after translating its new origin to zero. -/
theorem normalize (a b : A) (h₂ : ∀ z : A, (2 : ℤ) • z = 0 → z = 0)
    (i j : ℤ) (hi : -3 ≤ i ∧ i ≤ 3) (hj : -3 ≤ j ∧ j ≤ 3)
    (hn : i ≠ 0 ∨ j ≠ 0) (h : i • a + j • b = 0) :
    ∃ σ : Equiv.Perm (Fin 3),
      NormalForm (ports a b (σ 1) - ports a b (σ 0))
        (ports a b (σ 2) - ports a b (σ 0)) := by
  let I : Fin 7 := ⟨(i + 3).toNat, by omega⟩
  let J : Fin 7 := ⟨(j + 3).toNat, by omega⟩
  have hI : (I.val : ℤ) - 3 = i := by dsimp [I]; omega
  have hJ : (J.val : ℤ) - 3 = j := by dsimp [J]; omega
  obtain ⟨r,t,f,hf⟩ := certificate I J (by simpa [hI, hJ] using hn)
  rw [hI,hJ] at hf
  have hs : factor f • eval a b (vec r t) = 0 := by
    rw [← map_zsmul, hf]
    exact h
  have hz := cancel_factor h₂ f _ hs
  refine ⟨perm r, form_sound _ _ t ?_⟩
  change (form t).1 • (ports a b (order r 1) - ports a b (order r 0)) +
    (form t).2 • (ports a b (order r 2) - ports a b (order r 0)) = 0
  simpa only [vec, map_add, map_sub, map_zsmul, eval_port] using hz

#print axioms normalize
end HaarMetaShortRelations
