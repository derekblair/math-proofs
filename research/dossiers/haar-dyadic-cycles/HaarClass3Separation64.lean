import HaarClassFourFinite

namespace HaarClass3Separation64
open HaarClass4Structure HaarClass4Ports
open HaarClass3Table
variable {G : Type*} [Group G]

def eval (x y : G) (p : Coord) :=
  HaarClass3Collect.norm x y (portC x y) (portU x y) (portV x y) p

def i (p : Coord) : ℤ := p.1
def j (p : Coord) : ℤ := p.2.1
def k (p : Coord) : ℤ := p.2.2.1
def a (p : Coord) : ℤ := p.2.2.2.1
def b (p : Coord) : ℤ := p.2.2.2.2

def small (d : ℤ) : Prop := d.natAbs=1 ∨ d.natAbs=2

theorem two_layer (x y : G) (p q : Coord) (e : eval x y p=eval x y q) :
    let f := QuotientGroup.mk' (LS G 2)
    let C := f (portC x y)
    C^(i p)=C^(i q) ∧ C^(j p)=C^(j q) ∧
      (i p=i q → j p=j q → C^(k p)=C^(k q)) := by
  dsimp only
  let f := QuotientGroup.mk' (LS G 2)
  let X := f x
  let Y := f y
  let C := f (portC x y)
  let P : HaarCycle.Coord := (i p,j p,k p)
  let Q : HaarCycle.Coord := (i q,j q,k q)
  have u : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have v : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute C X := by
    apply commutatorElement_eq_one_iff_commute.mp
    have h := u
    rw [portU,map_commutatorElement] at h
    exact h
  have cy : Commute C Y := by
    apply commutatorElement_eq_one_iff_commute.mp
    have h := v
    rw [portV,map_commutatorElement] at h
    exact h
  have r : X*Y=Y*X*C := by
    have h := congrArg f (ports_xy x y)
    simp only [map_mul] at h
    exact h
  have E : HaarCycle.norm X Y C P=HaarCycle.norm X Y C Q := by
    have h := congrArg f e
    simp only [eval,HaarClass3Collect.norm,map_mul,map_zpow,u,v,one_zpow,mul_one] at h
    exact h
  obtain ⟨A,B⟩ := HaarBound16.conjugate_eq X Y C cx cy r E
  refine ⟨A,B,?_⟩
  intro hI hJ
  change Y^(j p)*X^(i p)*C^(k p)=Y^(j q)*X^(i q)*C^(k q) at E
  rw [hI,hJ] at E
  exact mul_left_cancel E

theorem pow_ne_odd (odd : Odd (Nat.card G)) {C : G} (hc : C≠1)
    {u v : ℤ} (h : small (u-v)) : C^u≠C^v := by
  apply HaarCycle.centralNE C hc (HaarClass3Odd.odd_no_involution odd hc)
  have ab : |u-v| = ((u-v).natAbs:ℤ) := (Int.natCast_natAbs _).symm
  rcases abs_choice (u-v) with ea|ea <;> rcases h with h|h <;> omega

theorem odd_projection (odd : Odd (Nat.card G)) : Odd (Nat.card (G ⧸ LS G 2)) :=
  Odd.of_dvd_nat odd (LS G 2).card_quotient_dvd_card

theorem reject_i (x y : G) (_nil : LS G 3=⊥) (odd : Odd (Nat.card G))
    (hc : portC x y ∉ LS G 2) (p q : Coord)
    (eq : eval x y p=eval x y q) (diff : small (i p-i q)) : False := by
  have h := (two_layer x y p q eq).1
  exact pow_ne_odd (odd_projection odd) (fun e => hc ((QuotientGroup.eq_one_iff _).mp e)) diff h

theorem reject_j (x y : G) (_nil : LS G 3=⊥) (odd : Odd (Nat.card G))
    (hc : portC x y ∉ LS G 2) (p q : Coord)
    (eq : eval x y p=eval x y q) (diff : small (j p-j q)) : False := by
  have h := (two_layer x y p q eq).2.1
  exact pow_ne_odd (odd_projection odd) (fun e => hc ((QuotientGroup.eq_one_iff _).mp e)) diff h

theorem reject_c (x y : G) (_nil : LS G 3=⊥) (odd : Odd (Nat.card G))
    (hc : portC x y ∉ LS G 2) (p q : Coord)
    (eq : eval x y p=eval x y q) (hi : i p=i q) (hj : j p=j q)
    (diff : small (k p-k q)) : False := by
  have h := (two_layer x y p q eq).2.2 hi hj
  exact pow_ne_odd (odd_projection odd) (fun e => hc ((QuotientGroup.eq_one_iff _).mp e)) diff h

theorem tail_relation (x y : G) (nil : LS G 3=⊥) (p q : Coord)
    (eq : eval x y p=eval x y q) (hi : i p=i q) (hj : j p=j q)
    (hk : k p=k q) : (portU x y)^(a q-a p)*(portV x y)^(b q-b p)=1 := by
  let U := portU x y
  let V := portV x y
  have C : LS G 2 ≤ Subgroup.center G :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mp nil
  have uv : Commute U V := (Subgroup.mem_center_iff.mp (C (layer_u x y)) _).symm
  change (y^(j p)*x^(i p)*(portC x y)^(k p))*U^(a p)*V^(b p) =
     (y^(j q)*x^(i q)*(portC x y)^(k q))*U^(a q)*V^(b q) at eq
  rw [hi,hj,hk] at eq
  simp only [mul_assoc] at eq
  have e := mul_left_cancel (mul_left_cancel (mul_left_cancel eq))
  change U^(a q-a p)*V^(b q-b p)=1
  rw [zpow_sub,zpow_sub]
  calc
    _ = U^(a q)*((U^(a p))⁻¹*V^(b q))*(V^(b p))⁻¹ := by simp only [mul_assoc]
    _ = (U^(a q)*V^(b q))*((V^(b p))⁻¹*(U^(a p))⁻¹) := by
      rw [((uv.zpow_zpow (a p) (b q)).inv_left).eq]
      simp only [mul_assoc]
      rw [((uv.zpow_zpow (a p) (b p)).inv_left.inv_right).eq]
    _ = 1 := by rw [←mul_inv_rev,←e,mul_inv_cancel]

end HaarClass3Separation64
#print axioms HaarClass3Separation64.tail_relation
#print axioms HaarClass3Separation64.reject_i
#print axioms HaarClass3Separation64.reject_j
#print axioms HaarClass3Separation64.reject_c
