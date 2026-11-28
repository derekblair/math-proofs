import N63DegreeSums
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Erdos151N63
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

def rightDeg {q : Nat} (R : Fin q → V) (j : Fin q) : Nat :=
  ∑ k : Fin q, if G (R j) (R k) then 1 else 0

theorem rightDeg_lt {q : Nat} (R : Fin q → V) (irr : ∀ v, ¬G v v) (j : Fin q) :
    rightDeg G R j < q := by
  have hh : rightDeg G R j + 0 =
      ∑ i ∈ (Finset.univ : Finset (Fin q)).erase j, if G (R j) (R i) then 1 else 0 := by
    unfold rightDeg
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp [irr]
  have ht : (∑ i ∈ (Finset.univ : Finset (Fin q)).erase j, if G (R j) (R i) then 1 else 0) ≤
      ((Finset.univ : Finset (Fin q)).erase j).card := by
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin q)).erase j, (1:Nat) :=
        Finset.sum_le_sum (fun i _ => by split <;> omega)
      _ = _ := by simp
  have he := Finset.card_erase_add_one (Finset.mem_univ j)
  simp only [Finset.card_univ,Fintype.card_fin] at he
  omega

theorem right_degree_balance (w : V) {d q : Nat}
    (L : Fin d ≃ {z : V // G w z}) (R : Fin q ≃ {z : V // z≠w ∧ ¬G w z})
    (sym : ∀ a b, G a b ↔ G b a) (irr : ¬G w w)
    (hind : ∀ i j, ¬G (L i).val (L j).val) (hd : fullDeg G w=d) :
    (∑ v : V, fullDeg G v) + (∑ j, rightDeg G (fun i => (R i).val) j) =
      2*d+2*(∑ j, fullDeg G (R j).val) := by
  have dl (i : Fin d) : fullDeg G (L i).val = 1 + ∑ j : Fin q, if G (L i).val (R j).val then 1 else 0 := by
    rw [deg_over_slots G w _ irr L R]
    simp [hind,(sym _ _).mpr (L i).property]
  have dr (j : Fin q) : fullDeg G (R j).val =
      (∑ i : Fin d, if G (L i).val (R j).val then 1 else 0) +
      rightDeg G (fun i => (R i).val) j := by
    rw [deg_over_slots G w _ irr L R]
    simp only [if_neg ((sym (R j).val w).not.mpr (R j).property.2),Nat.zero_add,rightDeg]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact if_congr (sym _ _) rfl rfl
  rw [sum_over_slots G w irr L R,hd]
  simp_rw [dl,dr]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.mul_one]
  rw [Finset.sum_comm (f:=fun i : Fin d => fun j : Fin q => if G (L i).val (R j).val then (1:Nat) else 0)]
  simp only [Nat.cast_id]
  omega

#print axioms rightDeg_lt
#print axioms right_degree_balance
end Erdos151N63
