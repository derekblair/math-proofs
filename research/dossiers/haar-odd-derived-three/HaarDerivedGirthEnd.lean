import HaarDerivedCheck2
import HaarDerivedCheck3
import HaarDerivedCheck4
import HaarDerivedCheck5
import HaarDerivedCheck6
import HaarDerivedCheck7
import HaarDerivedCheck8
import HaarDerivedFast9
import HaarDerivedCertified10
import Mathlib.Tactic.IntervalCases
import HaarCycleEven
import HaarDerivedWreathCore

namespace HaarDerivedGirth22
open HaarSharpLamp (scan)
open HaarAllNoncommuting HaarSharpPortGeometry
open scoped commutatorElement

theorem excluding_2n (n : ℕ) (lo : 2≤n) (hi : n≤10) : ¬ HasCycle x y (2*n) := by
  interval_cases n <;> apply no_cycle_of_check port port0 _ (by decide)
  · exact cert_sound check2
  · exact cert_sound check3
  · exact cert_sound check4
  · exact cert_sound check5
  · exact cert_sound check6
  · exact cert_sound check7
  · exact cert_sound check8
  · exact cert_fast len9 fast9
  · exact cert10

theorem no_cycle_below22 (k : ℕ) (lo : 3≤k) (hi : k<22) : ¬ HasCycle x y k := by
  intro h
  obtain ⟨n,e⟩ := HaarCycleEven.even_positive (by omega : 0<k) h
  have h' : k=2*n := by omega
  rw [h'] at h
  exact excluding_2n n (by omega) (by omega) h

def coordinates : G ≃ L × S where
  toFun g := ⟨g.left,g.right⟩
  invFun p := ⟨p.1,p.2⟩
  left_inv := by intro g; cases g; rfl
  right_inv := by intro p; cases p; rfl

instance : Finite G := Finite.of_equiv _ coordinates.symm

theorem cardinality : Nat.card G = 13 * 5^26 := by
  rw [Nat.card_congr coordinates, Nat.card_prod]
  have h : Nat.card L = 5^26 := by simp [ZMod.card]
  rw [h]
  simp [ZMod.card]

theorem odd : Odd (Nat.card G) := by rw [cardinality]; decide

def projection : G →* Multiplicative S where
  toFun g := Multiplicative.ofAdd g.right
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ker_comm (a b : G) (ha : a ∈ projection.ker) (hb : b ∈ projection.ker) : a*b=b*a := by
  change a.right=0 at ha
  change b.right=0 at hb
  apply G.ext'
  · intro t j
    change (mul a b).left t j = (mul b a).left t j
    simp [mul,ha,hb,add_comm]
  · change (mul a b).right = (mul b a).right
    simp [mul,ha,hb]

theorem length_two : derivedSeries G 2 = ⊥ := by
  rw [show (2:ℕ)=1+1 by decide, derivedSeries_succ, derivedSeries_one, eq_bot_iff]
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (ker_comm a b
    (Abelianization.commutator_subset_ker projection ha) (Abelianization.commutator_subset_ker projection hb)))

theorem x_ne_one : x≠1 := by
  intro e
  have h := congrArg G.right e
  exact (by decide : (1:S)≠0) h

theorem y_ne_one : y≠1 := by
  intro e
  have h := congrArg G.right e
  exact (by decide : (4:S)≠0) h

theorem x_ne_y : x≠y := by
  intro e
  have h := congrArg G.right e
  exact (by decide : (1:S)≠4) h

theorem wreath_candidate :
    Odd (Nat.card (HaarDerivedWreathCore.W G)) ∧ derivedSeries (HaarDerivedWreathCore.W G) 3=⊥ :=
  ⟨HaarDerivedWreathCore.odd_group odd,HaarDerivedWreathCore.derived_next 2 length_two⟩

end HaarDerivedGirth22
#print axioms HaarDerivedGirth22.no_cycle_below22
#print axioms HaarDerivedGirth22.wreath_candidate
