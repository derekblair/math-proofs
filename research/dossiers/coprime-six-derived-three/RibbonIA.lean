import RibbonDerived3Algebra

namespace RibbonIA
open HaarClass4Structure RibbonDerived3
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- Three-subgroup containment modulo a normal subgroup. -/
theorem rotate_le (A B C K : Subgroup G) [K.Normal]
    (P : ⁅⁅B,C⁆,A⁆≤K) (Q : ⁅⁅C,A⁆,B⁆≤K) : ⁅⁅A,B⁆,C⁆≤K := by
  let f := QuotientGroup.mk' K
  have h1 : ⁅⁅B.map f,C.map f⁆,A.map f⁆=⊥ := by
    rw [←Subgroup.map_commutator,←Subgroup.map_commutator,Subgroup.map_eq_bot_iff]
    rw [QuotientGroup.ker_mk']
    exact P
  have h2 : ⁅⁅C.map f,A.map f⁆,B.map f⁆=⊥ := by
    rw [←Subgroup.map_commutator,←Subgroup.map_commutator,Subgroup.map_eq_bot_iff]
    rw [QuotientGroup.ker_mk']
    exact Q
  have e := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [←Subgroup.map_commutator,←Subgroup.map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at e
  exact e

theorem weight_pair (S : Subgroup G) [S.Normal] (i j : Nat) :
    ⁅S.lowerCentralSeries i,S.lowerCentralSeries j⁆≤S.lowerCentralSeries (i+j+1) := by
  induction i generalizing j with
  | zero =>
    rw [Subgroup.lowerCentralSeries_zero,Nat.zero_add,Subgroup.commutator_comm S,Subgroup.lowerCentralSeries_succ]
  | succ i ih =>
    change ⁅⁅S.lowerCentralSeries i,S⁆,S.lowerCentralSeries j⁆≤_
    apply rotate_le
    · rw [Subgroup.commutator_comm S (S.lowerCentralSeries j),←Subgroup.lowerCentralSeries_succ,
        Subgroup.commutator_comm (S.lowerCentralSeries (j+1))]
      exact (show i+(j+1)+1=i+1+j+1 by omega) ▸ ih (j+1)
    · have h := Subgroup.commutator_mono_left
        (show ⁅S.lowerCentralSeries j,S.lowerCentralSeries i⁆≤S.lowerCentralSeries (i+j+1) by
          rw [Subgroup.commutator_comm]; exact ih j) (K:=S)
      rw [←Subgroup.lowerCentralSeries_succ] at h
      exact (show i+j+1+1=i+1+j+1 by omega) ▸ h

theorem ia_bumps (h : LS G 2 ≤ DLS G 1) (i : Nat) :
    ⁅DLS G i,(⊤ : Subgroup G)⁆≤DLS G (i+1) := by
  induction i with
  | zero => exact h
  | succ i ih =>
    change ⁅⁅DLS G i,Derived G⁆,(⊤ : Subgroup G)⁆≤DLS G (i+1+1)
    apply rotate_le
    · have e : ⁅Derived G,(⊤ : Subgroup G)⁆≤DLS G 1 := h
      exact (Subgroup.commutator_mono_left e).trans
        ((show 1+i+1=i+1+1 by omega) ▸ weight_pair (Derived G) 1 i)
    · rw [Subgroup.commutator_comm (⊤ : Subgroup G) (DLS G i)]
      exact Subgroup.commutator_mono_left ih

/-- If the third lower-central term stabilizes nontrivially while the
derived group is nilpotent, that term survives in the derived group's
abelianization. No ambient nilpotence or class cap is needed. -/
theorem stable_visible (dnil : ∃ n, DLS G n=⊥)
    (stable : LS G 2=LS G 3) (nz : LS G 2≠⊥) :
    ¬ LS G 2≤DLS G 1 := by
  intro h
  have H (i : Nat) : LS G 2≤DLS G i := by
    induction i with
    | zero => exact Subgroup.lowerCentralSeries_antitone _ (by decide : 1≤2)
    | succ j ih =>
      rw [stable]
      exact (Subgroup.commutator_mono_left ih).trans (ia_bumps h j)
  obtain ⟨n,hn⟩ := dnil
  exact nz (le_bot_iff.mp (hn ▸ H n))

end RibbonIA
#print axioms RibbonIA.stable_visible
