import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.OrderOfElement

namespace HaarClass5DirectionCover

abbrev Vec := ℤ × ℤ
def D0 : Fin 4 → Vec := ![(0,1),(1,0),(1,1),(1,2)]
def D1 : Fin 4 → Vec := ![(0,1),(1,-2),(1,-1),(1,0)]
def D2 : Fin 4 → Vec := ![(0,1),(1,-3),(1,-2),(1,-1)]
def D3 : Fin 4 → Vec := ![(1,-1),(1,0),(2,-1),(3,-2)]

def det (p q : Vec) : ℤ := p.1*q.2-p.2*q.1

def small (p q : Vec) : Prop := 0 < (det p q).natAbs ∧ (det p q).natAbs ≤ 4
instance (p q : Vec) : Decidable (small p q) := by unfold small; infer_instance

theorem four_choices :
    ∀ i j k l, small (D0 i) (D1 j) ∨ small (D0 i) (D2 k) ∨ small (D0 i) (D3 l) := by
  decide

variable {G : Type*} [Group G]

def rel (u v : G) (p : Vec) : Prop := u^p.1*v^p.2=1

theorem annihilate_first (u v : G) (huv : Commute u v) (p q : Vec)
    (hp : rel u v p) (hq : rel u v q) : u^(det p q)=1 := by
  have e1 : u^p.1=(v^p.2)⁻¹ := eq_inv_of_mul_eq_one_left hp
  have e2 : u^q.1=(v^q.2)⁻¹ := eq_inv_of_mul_eq_one_left hq
  have E : u^(p.1*q.2)=u^(q.1*p.2) := by
    rw [zpow_mul,zpow_mul,e1,e2,inv_zpow,inv_zpow,←zpow_mul,←zpow_mul,mul_comm p.2 q.2]
  rw [det,zpow_sub,E,mul_comm p.2 q.1,mul_inv_cancel]

theorem flip_rel (u v : G) (h : Commute u v) (p : Vec)
    (hp : rel u v p) : rel v u (p.2,p.1) := by
  change v^p.2*u^p.1=1
  rw [(h.zpow_zpow _ _).eq.symm]
  exact hp

theorem annihilate_second (u v : G) (huv : Commute u v) (p q : Vec)
    (hp : rel u v p) (hq : rel u v q) : v^(det p q)=1 := by
  have E := annihilate_first v u huv.symm (p.2,p.1) (q.2,q.1) (flip_rel u v huv p hp) (flip_rel u v huv q hq)
  have eh : det (p.2,p.1) (q.2,q.1) = -det p q := by simp [det]
  rw [eh,zpow_neg,inv_eq_one] at E
  exact E

theorem small_annihilator_gives_cube (g : G) (odd_order : Odd (orderOf g)) (e : ℤ)
    (lo : 0 < e.natAbs) (hi : e.natAbs ≤ 4) (hz : g^e=1) :
    g^(3:ℕ)=1 := by
  have ed : (orderOf g : ℤ) ∣ e := orderOf_dvd_iff_zpow_eq_one.mpr hz
  have d : orderOf g ∣ e.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr ed)
  have le : orderOf g ≤ 4 := (Nat.le_of_dvd lo d).trans hi
  have posOrThree : orderOf g=1 ∨ orderOf g=3 := by
    obtain ⟨_,e⟩ := odd_order
    omega
  apply orderOf_dvd_iff_pow_eq_one.mp
  rcases posOrThree with h|h <;> simp [h]

theorem four_collisions_force_cubes (u v : G) (comm : Commute u v)
    (uodd : Odd (orderOf u)) (vodd : Odd (orderOf v)) (i j k l : Fin 4)
    (h0 : rel u v (D0 i)) (h1 : rel u v (D1 j))
    (h2 : rel u v (D2 k)) (h3 : rel u v (D3 l)) : u^(3:ℕ)=1 ∧ v^(3:ℕ)=1 := by
  have H (p q : Vec) (hp : rel u v p) (hq : rel u v q) (s : small p q) :
      u^(3:ℕ)=1 ∧ v^(3:ℕ)=1 :=
    ⟨small_annihilator_gives_cube u uodd _ s.1 s.2 (annihilate_first u v comm p q hp hq),
     small_annihilator_gives_cube v vodd _ s.1 s.2 (annihilate_second u v comm p q hp hq)⟩
  rcases four_choices i j k l with s|s|s
  · exact H _ _ h0 h1 s
  · exact H _ _ h0 h2 s
  · exact H _ _ h0 h3 s

end HaarClass5DirectionCover
#print axioms HaarClass5DirectionCover.four_collisions_force_cubes
