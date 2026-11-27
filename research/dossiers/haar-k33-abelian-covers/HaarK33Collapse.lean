import HaarK33CollapseCore
import HaarAbel
import Mathlib.Tactic.Group

namespace HaarK33Collapse
open HaarAllNoncommuting HaarAbelCore
variable {G Q : Type*} [Group G] [Group Q]
def r16 : Fin 17 → Grid := ![(false,(0,0)),(false,(0,0)),(false,(-1,0)),(false,(-1,0)),(false,(-2,0)),(true,(-2,0)),(true,(-2,0)),(true,(-2,1)),(false,(-2,1)),(false,(-1,1)),(false,(-1,1)),(false,(0,1)),(false,(0,1)),(true,(0,1)),(true,(0,0)),(true,(0,0)),(false,(0,0))]
def rplus : Fin 9 → Grid := ![(false,(0,0)),(false,(0,0)),(false,(-1,0)),(false,(-1,0)),(false,(-2,0)),(true,(-2,0)),(true,(-2,0)),(true,(-2,1)),(false,(-2,1))]
def rminus : Fin 9 → Grid := ![(false,(0,0)),(false,(0,0)),(false,(-1,0)),(false,(-1,0)),(false,(-2,0)),(true,(-2,0)),(true,(-2,-1)),(true,(-2,-1)),(false,(-2,-1))]

def dShort : List P := [(0,1),(1,0),(2,0)]
def dLong : List P := [(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1)]

theorem square_ne [Finite G] (odd : Odd (Nat.card G)) (x : G) (nx : x≠1) : x^2≠1 := by
  intro h
  have d : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
  have q : Odd (orderOf x) := Odd.of_dvd_nat odd (orderOf_dvd_natCard x)
  have a : orderOf x=1 := by
    have b := Nat.le_of_dvd (show 0<2 by decide) d
    obtain ⟨k,hk⟩ := q
    omega
  exact nx (orderOf_eq_one_iff.mp a)

theorem no_invert [Finite G] (odd : Odd (Nat.card G)) (x y : G) (nx : x≠1)
    (bad : y*x=x⁻¹*y) : False := by
  have bad' : y*x⁻¹=x*y := by
    calc
      _ = x*(x⁻¹*y)*x⁻¹ := by group
      _ = x*y := by rw [← bad]; group
  have par (n : ℕ) : y^n*x=(if n%2=0 then x else x⁻¹)*y^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',mul_assoc,ih,← mul_assoc]
      by_cases d : n%2=0
      · have a : (n+1)%2 ≠ 0 := by omega
        simp [d,a,bad,mul_assoc]
      · have a : (n+1)%2 = 0 := by omega
        simp [d,a,bad',mul_assoc]
  have yodd : Odd (orderOf y) := Odd.of_dvd_nat odd (orderOf_dvd_natCard y)
  obtain ⟨k,kk⟩ := yodd
  have mod : orderOf y % 2 ≠ 0 := by omega
  have E : x = x⁻¹ := by simpa [mod,pow_orderOf_eq_one] using par (orderOf y)
  apply square_ne odd x nx
  rw [pow_two]
  exact mul_eq_one_iff_eq_inv.mpr E

set_option maxRecDepth 5000 in
theorem kernel_one_port (f : G →* Q) [Finite G] (odd : Odd (Nat.card G))
    (x y : G) (nx : x≠1) (hx : f x=1) (hy : f y≠1)
    (comm : ∀ a b : f.ker, a*b=b*a) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n := by
  let u := y*x*y⁻¹
  have rel : y*x=u*y := by dsimp [u]; group
  have hu : f u=1 := by simp [u,hx]
  have cu : Commute x u := congrArg Subtype.val (comm ⟨x,hx⟩ ⟨u,hu⟩)
  have nu : u≠1 := by
    intro h
    apply nx
    calc
      x = y⁻¹*u*y := by dsimp [u]; group
      _ = 1 := by simp [h]
  have nxx := square_ne odd x nx
  have short_safe : ∀ d∈dShort, ¬R x u d := by
    intro d hd
    simp [dShort] at hd
    rcases hd with rfl|rfl|rfl
    · simpa [R,image] using nu
    · simpa [R,image] using nx
    · simpa [R,image] using nxx
  by_cases same : u=x
  · have c : Commute x y := by
      unfold Commute SemiconjBy
      rw [same] at rel
      exact rel.symm
    have nxy : x≠y := fun h => hy (h ▸ hx)
    have ny : y≠1 := fun h => hy (by simp [h])
    rcases HaarAbel.commute_case x y c nx ny nxy with C|C|C
    · exact ⟨4, by decide,C⟩
    · exact ⟨8, by decide,C⟩
    · exact ⟨16, by decide,C⟩
  have notInv : u≠x⁻¹ := by
    intro h
    exact no_invert odd x y nx (by simpa [h] using rel)
  by_cases pos : u=x^2
  · refine ⟨8,by decide,table (by decide) (by decide) f x y u cu rel hx hu hy rplus dShort
        (by decide +kernel) (by decide +kernel) ?_ short_safe⟩
    change eval x y u (false,(-2,1)) = eval x y u (false,(0,0))
    simp [eval,image,pos,zpow_neg]
  by_cases neg : u=(x^2)⁻¹
  · refine ⟨8,by decide,table (by decide) (by decide) f x y u cu rel hx hu hy rminus dShort
        (by decide +kernel) (by decide +kernel) ?_ short_safe⟩
    change eval x y u (false,(-2,-1)) = eval x y u (false,(0,0))
    simp [eval,image,neg,zpow_neg]
  refine ⟨16,by decide,table (by decide) (by decide) f x y u cu rel hx hu hy r16 dLong
        (by decide +kernel) (by decide +kernel) rfl ?_⟩
  intro d hd bad
  simp [dLong] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact short_safe _ (by decide) bad
  · apply same
    have g : u⁻¹*x=1 := by simpa [R,image] using bad
    calc
      u = u*(u⁻¹*x) := by rw [g,mul_one]
      _ = x := by group
  · exact short_safe _ (by decide) bad
  · apply notInv
    exact mul_eq_one_iff_eq_inv.mp (by simpa [R,image] using bad)
  · apply pos
    have g : u⁻¹*x^2=1 := by simpa [R,image] using bad
    calc
      u = u*(u⁻¹*x^2) := by rw [g,mul_one]
      _ = x^2 := by group
  · exact short_safe _ (by decide) bad
  · exact neg ((mul_eq_one_iff_eq_inv).mp (by simpa [R,image] using bad))

end HaarK33Collapse
#print axioms HaarK33Collapse.kernel_one_port
