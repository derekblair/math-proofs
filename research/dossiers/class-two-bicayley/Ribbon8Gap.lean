import Ribbon7Family

namespace Ribbon8
open Ribbon5Bridge HaarClass4Structure HaarClass4Ports
variable {G : Type*} [Group G]

def gap7 (d : ℤ) : Prop := 0 < d.natAbs ∧ d.natAbs ≤ 7
instance (d : ℤ) : Decidable (gap7 d) := by unfold gap7; infer_instance

def separated7 (u v : Q) : Prop :=
  u.1 ≠ v.1 ∨ gap7 (u.2.1-v.2.1) ∨ gap7 (u.2.2.1-v.2.2.1) ∨
    (u.2.1=v.2.1 ∧ u.2.2.1=v.2.2.1 ∧ gap7 (u.2.2.2-v.2.2.2))
instance (u v : Q) : Decidable (separated7 u v) := by unfold separated7; infer_instance

theorem rejects (c : G) (good : ∀ k : Nat, 1≤k → k≤7 → c^k ≠ 1)
    (a b : ℤ) (h : gap7 (a-b)) : c^a ≠ c^b := by
  intro E
  have J : c^(a-b)=1 := by rw [zpow_sub,E,mul_inv_cancel]
  apply good (a-b).natAbs h.1 h.2
  by_cases Z : 0≤a-b
  · have H := Int.natAbs_of_nonneg Z
    rw [← zpow_natCast,H]
    exact J
  · have H := Int.ofNat_natAbs_of_nonpos (by omega : a-b ≤ 0)
    rw [←zpow_natCast,H,zpow_neg,J,inv_one]

theorem sep_sound (x y c : G) (cx : Commute c x) (cy : Commute c y)
    (xy : x*y=y*x*c) (good : ∀ k : Nat, 1≤k → k≤7 → c^k≠1)
    (u v : Q) (h : separated7 u v) : vert x y c u ≠ vert x y c v := by
  intro E
  have F : HaarCycle.norm x y c u.2 = HaarCycle.norm x y c v.2 := congrArg Prod.snd E
  have M := HaarBound16.conjugate_eq x y c cx cy xy F
  rcases h with h|h|h|⟨hi,hj,h⟩
  · exact h (congrArg (Prod.fst : Bool × G → Bool) E)
  · exact rejects c good _ _ h M.1
  · exact rejects c good _ _ h M.2
  · unfold HaarCycle.norm at F
    rw [hi,hj] at F
    exact rejects c good _ _ h (mul_left_cancel F)

theorem card_good [Finite G] (c : G) (hc : c≠1)
    (co : Nat.Coprime (Nat.card G) 420) (k : Nat) (lo : 1≤k) (hi : k≤7) : c^k≠1 := by
  intro E
  have D : orderOf c ∣ k := orderOf_dvd_iff_pow_eq_one.mpr E
  have e : k ∣ 420 := by interval_cases k <;> decide
  exact hc (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes co
    (orderOf_dvd_natCard c) (dvd_trans D e)))

end Ribbon8
#print axioms Ribbon8.sep_sound
#print axioms Ribbon8.card_good
