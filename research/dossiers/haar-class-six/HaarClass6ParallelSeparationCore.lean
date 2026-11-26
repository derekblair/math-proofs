import HaarClass6ParallelWords

namespace HaarClass6ParallelSeparationCore
open HaarClass3Separation64 HaarClass5TemplateClosure HaarClass4Ports HaarUniversal36
open scoped commutatorElement
variable {G : Type*} [Group G]

def small3 (d : ℤ) : Prop := -3≤d ∧ d≤3 ∧ d≠0
instance (d : ℤ) : Decidable (small3 d) := by unfold small3; infer_instance

theorem pow_distinct (odd : Odd (Nat.card G)) {g : G} (ng : g^(3:ℕ)≠1)
    {p q : ℤ} (small : small3 (p-q)) : g^p≠g^q := by
  have nt : g≠1 := by intro e; apply ng; rw [e,one_pow]
  by_cases s : HaarClass3Separation64.small (p-q)
  · exact pow_ne_odd odd nt s
  intro e
  have h : g^(p-q)=1 := by rw [zpow_sub,e,mul_inv_cancel]
  have cases3 : p-q=3 ∨ p-q= -3 := by
    unfold HaarClass3Separation64.small at s
    obtain ⟨lo,hi,ne⟩ := small
    have d : ((p-q).natAbs:ℤ)=|p-q| := Int.natCast_natAbs _
    rcases abs_choice (p-q) with t|t <;> omega
  rcases cases3 with t|t
  · apply ng
    change g^(3:ℕ)=1
    simpa only [t,show (3:ℤ)=((3:ℕ):ℤ) by rfl,zpow_natCast] using h
  · apply ng
    rw [t,zpow_neg,show (3:ℤ)=((3:ℕ):ℤ) by rfl,zpow_natCast,inv_eq_one] at h
    exact h

theorem project_c_cube (nil : L G 3=⊥) (x y : G)
    (nv : (portV x y)^(3:ℕ)≠1) :
    ((QuotientGroup.mk' (L G 2)) (portC x y))^(3:ℕ)≠1 := by
  intro eq
  let f := QuotientGroup.mk' (L G 2)
  let c := portC x y
  let v := portV x y
  have hc : c^(3:ℕ) ∈ L G 2 := (QuotientGroup.eq_one_iff _).mp (by
    change f (c^(3:ℕ))=1
    rw [map_pow]
    exact eq)
  have h := (central_2 nil hc y).commutator_eq
  have pc : Commute c ⁅c,y⁆ := (central_2 nil (layer_v x y) c).symm
  rw [←pc.commutatorElement_pow_left] at h
  exact nv h

end HaarClass6ParallelSeparationCore
#print axioms HaarClass6ParallelSeparationCore.pow_distinct
#print axioms HaarClass6ParallelSeparationCore.project_c_cube
