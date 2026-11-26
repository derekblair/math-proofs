import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Abel

namespace HaarMetaQuotientGeometry

variable {Q : Type*} [AddCommGroup Q]

def Spans (x y : Q) : Prop := AddSubgroup.closure ({x,y} : Set Q) = ⊤

theorem cyclic_of_mem (x y z : Q) (gen : Spans x y)
    (hx : x ∈ AddSubgroup.zmultiples z) (hy : y ∈ AddSubgroup.zmultiples z) :
    AddSubgroup.zmultiples z = ⊤ := by
  apply top_unique
  rw [← gen]
  apply (AddSubgroup.closure_le _).mpr
  intro a ha
  have h : a=x ∨ a=y := by simpa using ha
  rcases h with h|h
  · simpa [h] using hx
  · simpa [h] using hy

theorem primitive_013 (x y : Q) (gen : Spans x y) (h : y=(3:ℤ) • x) :
    AddSubgroup.zmultiples x = ⊤ :=
  cyclic_of_mem x y x gen (AddSubgroup.mem_zmultiples _) (h ▸ AddSubgroup.zsmul_mem_zmultiples x 3)

theorem primitive_014 (x y : Q) (gen : Spans x y) (h : y=(4:ℤ) • x) :
    AddSubgroup.zmultiples x = ⊤ :=
  cyclic_of_mem x y x gen (AddSubgroup.mem_zmultiples _) (h ▸ AddSubgroup.zsmul_mem_zmultiples x 4)

theorem primitive_025 (x y : Q) (gen : Spans x y) (h : (5:ℤ) • x=(2:ℤ) • y) :
    let z := y-(2:ℤ) • x
    x=(2:ℤ) • z ∧ y=(5:ℤ) • z ∧ AddSubgroup.zmultiples z=⊤ := by
  let z := y-(2:ℤ) • x
  have hx : x=(2:ℤ) • z := by
    calc x = (5:ℤ) • x-(4:ℤ) • x := by abel
         _ = (2:ℤ) • y-(4:ℤ) • x := by rw [h]
         _ = (2:ℤ) • z := by dsimp [z]; abel
  have hy : y=(5:ℤ) • z := by
    have hy' : y=z+(2:ℤ) • x := by dsimp [z]; abel
    calc y=z+(2:ℤ) • x := hy'
         _=(5:ℤ) • z := by rw [hx]; abel
  exact ⟨hx,hy,cyclic_of_mem x y z gen (hx ▸ AddSubgroup.zsmul_mem_zmultiples z 2)
    (hy ▸ AddSubgroup.zsmul_mem_zmultiples z 5)⟩

def proj (t : Q) := QuotientAddGroup.mk' (AddSubgroup.zmultiples t)

noncomputable def relativeOrder (t z : Q) : ℕ := addOrderOf (proj t z)

theorem projected_t (t : Q) : proj t t = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_zmultiples t)

theorem nsmul_inj_bounded (x : Q) (w : ℕ) (hw : w ≤ addOrderOf x) :
    Function.Injective (fun i : Fin w => i.val • x) := by
  have forward (i j : Fin w) (hij : i.val<j.val) (e : i.val • x=j.val • x) : False := by
    have e' : (j.val-i.val) • x=0 := by
      have hsum : (j.val-i.val) • x+i.val • x = j.val • x := by
        rw [←add_nsmul, Nat.sub_add_cancel hij.le]
      rw [←e] at hsum
      exact add_right_cancel (hsum.trans (zero_add _).symm)
    have dv := addOrderOf_dvd_iff_nsmul_eq_zero.mpr e'
    have ub := Nat.le_of_dvd (by omega : 0<j.val-i.val) dv
    omega
  intro i j e
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with h|h|h
  · exact (forward i j h e).elim
  · exact h
  · exact (forward j i h e.symm).elim

def cylinder (t z : Q) (w : ℕ) (ij : Fin w × Fin 3) : Q :=
  ij.1.val • z + ij.2.val • t

theorem cylinder_injective (t z : Q) (w : ℕ) (ht : addOrderOf t=3)
    (hw : w≤relativeOrder t z) : Function.Injective (cylinder t z w) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ e
  have re := congrArg (proj t) e
  simp [cylinder, map_add, map_nsmul, projected_t] at re
  have r := nsmul_inj_bounded (proj t z) w hw re
  subst j
  have l : a.val • t=b.val • t := add_left_cancel e
  exact congrArg (Prod.mk i) (nsmul_inj_bounded t 3 (by omega) l)

theorem span_swap (x y : Q) (h : Spans x y) : Spans y x := by
  unfold Spans at *
  rwa [Set.pair_comm]

theorem span_shear (x y : Q) (k : ℤ) (gen : Spans x y) :
    Spans x (y-k • x) := by
  unfold Spans at *
  apply top_unique
  rw [← gen]
  apply (AddSubgroup.closure_le _).mpr
  intro a ha
  let S := AddSubgroup.closure ({x,y-k • x} : Set Q)
  have hx : x∈S := AddSubgroup.subset_closure (by simp)
  have ht : y-k • x∈S := AddSubgroup.subset_closure (by simp)
  have h : a=x ∨ a=y := by simpa using ha
  rcases h with h|h
  · rw [h]; exact hx
  · subst a
    change y ∈ S
    have he : y=(y-k • x)+k • x := by abel
    rw [he]
    exact S.add_mem ht (S.zsmul_mem hx _)

theorem torsion_three (t : Q) (ne : t≠0) (ht : (3:ℕ) • t=0) :
    addOrderOf t=3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact addOrderOf_eq_prime ht ne

end HaarMetaQuotientGeometry
#print axioms HaarMetaQuotientGeometry.primitive_025
#print axioms HaarMetaQuotientGeometry.cylinder_injective
