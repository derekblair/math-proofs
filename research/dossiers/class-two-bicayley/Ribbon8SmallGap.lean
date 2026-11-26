import Ribbon8SmallDescent
import Ribbon8Gap

namespace Ribbon8Small
open Ribbon5Bridge
variable {G : Type*} [Group G]

private theorem order_dvd_abs (c : G) {i j : ℤ} (eq : c^i=c^j) :
    orderOf c∣(i-j).natAbs := by
  have E : c^(i-j)=1 := by rw [zpow_sub,eq,mul_inv_cancel]
  apply orderOf_dvd_iff_pow_eq_one.mpr
  by_cases h : 0 ≤ i - j
  · rw [←zpow_natCast,Int.natAbs_of_nonneg h]
    exact E
  · rw [←zpow_natCast,Int.ofNat_natAbs_of_nonpos (by omega : i-j≤0),
       zpow_neg,E,inv_one]

theorem gap_of_equal (p : Fin 2) (x y c : G)
    (cx : Commute c x) (cy : Commute c y) (xy : x*y=y*x*c)
    (order : orderOf c=prime p) (a b : Q) (low : Ribbon8.low a b)
    (e : vert x y c a=vert x y c b) :
    a.1=b.1 ∧ a.2.1=b.2.1 ∧ a.2.2.1=b.2.2.1 ∧
      (b.2.2.2-a.2.2.2).natAbs=prime p := by
  have side : a.1=b.1 := congrArg (fun u : Bool × G => u.1) e
  have F : HaarCycle.norm x y c a.2=HaarCycle.norm x y c b.2 := congrArg Prod.snd e
  have M := HaarBound16.conjugate_eq x y c cx cy xy F
  rcases low with h|⟨lo,hi⟩|⟨lo,hi⟩|⟨hx,hy,lo,hi⟩
  · exact (h side).elim
  · have H := order_dvd_abs c M.1
    rw [order] at H
    have s : 5 ≤ prime p := by fin_cases p <;> decide
    have K := Nat.le_of_dvd lo H
    omega
  · have H := order_dvd_abs c M.2
    rw [order] at H
    have s : 5 ≤ prime p := by fin_cases p <;> decide
    have K := Nat.le_of_dvd lo H
    omega
  · have E : c^(a.2.2.2)=c^(b.2.2.2) := by
      unfold HaarCycle.norm at F
      rw [hx,hy] at F
      exact mul_left_cancel F
    have D := order_dvd_abs c E
    rw [order] at D
    refine ⟨side,hx,hy,?_⟩
    have F : (a.2.2.2-b.2.2.2).natAbs = prime p := by
      fin_cases p
      · change 5∣(a.2.2.2-b.2.2.2).natAbs at D
        change _ = 5
        omega
      · change 7∣(a.2.2.2-b.2.2.2).natAbs at D
        change _ = 7
        omega
    rw [show b.2.2.2-a.2.2.2=-(a.2.2.2-b.2.2.2) by omega,Int.natAbs_neg]
    exact F

end Ribbon8Small
#print axioms Ribbon8Small.gap_of_equal
