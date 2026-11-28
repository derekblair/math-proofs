import N63Moore
import Mathlib.Algebra.BigOperators.Fin

namespace Erdos151N63
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V → V → Prop) [DecidableRel G]

theorem moore_second_degree (w : V) (L : Fin 3 → V) (M : Fin 3 → Fin 2 → V)
    (bij : Function.Bijective (mooreVal w L M)) (sym : ∀ a b,G a b↔G b a)
    (mw : ∀ i j, ¬G w (M i j))
    (ml : ∀ i j k, G (L i) (M j k) ↔ i=j)
    (deg : ∀ v, fullDeg G v=3)
    (i : Fin 3) (p : Fin 2) :
    (∑ j : Fin 3, ∑ q : Fin 2, if G (M i p) (M j q) then 1 else 0) = 2 := by
  let F (z : V) : Nat := if G (M i p) z then 1 else 0
  let e : MooreSlots ≃ V := Equiv.ofBijective _ bij
  have h := Finset.sum_equiv e (s:=Finset.univ) (t:=Finset.univ)
    (f:=fun a => F (mooreVal w L M a)) (g:=F) (by simp) (by intro a _; rfl)
  have dh : (∑ z : V, F z)=3 := by
    change (∑ z : V, if G (M i p) z then 1 else 0)=3
    have hcard := deg (M i p)
    rwa [fullDeg,Finset.card_eq_sum_ones,Finset.sum_filter] at hcard
  rw [dh,Fintype.sum_option,Fintype.sum_sum_type,Fintype.sum_prod_type] at h
  have wl : ¬G (M i p) w := (sym _ _).not.mpr (mw i p)
  have mL (j : Fin 3) : G (M i p) (L j) ↔ j=i := (sym _ _).trans (ml j i p)
  simp only [mooreVal,F,if_neg wl,Nat.zero_add,mL] at h
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at h
  omega

theorem moore_matching (w : V) (L : Fin 3 → V) (M : Fin 3 → Fin 2 → V)
    (bij : Function.Bijective (mooreVal w L M))
    (sym : ∀ a b,G a b↔G b a) (tf : ∀ v x y, G v x → G v y → ¬G x y)
    (sq : AtMostOneCommon G) (mw : ∀ i j, ¬G w (M i j))
    (ml : ∀ i j k, G (L i) (M j k) ↔ i=j)
    (deg : ∀ v, fullDeg G v=3)
    (i j : Fin 3) (p : Fin 2) (hne : i≠j) :
    (G (M i p) (M j 0) ∧ ¬G (M i p) (M j 1)) ∨
      (¬G (M i p) (M j 0) ∧ G (M i p) (M j 1)) := by
  let row (k : Fin 3) : Nat := ∑ u : Fin 2, if G (M i p) (M k u) then 1 else 0
  have total := moore_second_degree G w L M bij sym mw ml deg i p
  change (∑ k : Fin 3,row k)=2 at total
  have z : row i=0 := by
    have e (u : Fin 2) : ¬G (M i p) (M i u) := tf _ _ _ ((ml i i p).mpr rfl) ((ml i i u).mpr rfl)
    simp [row,e]
  have bound (k : Fin 3) : row k≤1 := by
    by_cases h0 : G (M i p) (M k 0)
    · have h1 : ¬G (M i p) (M k 1) := by
        intro h1
        have hne' : M i p≠L k := fun h => by
          have e : (some (Sum.inr (i,p)) : MooreSlots)=some (Sum.inl k) := bij.1 h
          nomatch e
        have e := sq _ _ _ _ hne' h0 ((ml k k 0).mpr rfl) h1 ((ml k k 1).mpr rfl)
        have ee : (some (Sum.inr (k,0)) : MooreSlots)=some (Sum.inr (k,1)) := bij.1 e
        have hneq : (0:Fin 2)≠1 := by decide
        exact hneq (Prod.mk.inj (Sum.inr.inj (Option.some.inj ee))).2
      change (∑ u : Fin 2, if G (M i p) (M k u) then 1 else 0) ≤ 1
      rw [Fin.sum_univ_two,if_pos h0,if_neg h1]
    · change (∑ u : Fin 2, if G (M i p) (M k u) then 1 else 0) ≤ 1
      rw [Fin.sum_univ_two,if_neg h0]
      split <;> omega
  have pos : row j≠0 := by
    intro hj
    let A := ((Finset.univ : Finset (Fin 3)).erase i).erase j
    have h2 : (∑ k∈A,row k)=2 := by
      have h1 := Finset.sum_erase_add (s:=Finset.univ) (f:=row) (Finset.mem_univ i)
      have h' := Finset.sum_erase_add (s:=(Finset.univ : Finset (Fin 3)).erase i) (f:=row)
        (Finset.mem_erase.mpr ⟨hne.symm,Finset.mem_univ _⟩)
      change (∑ k∈A,row k)+row j=_ at h'
      omega
    have ht := Finset.sum_le_sum (s:=A) (fun k _ => bound k)
    have hc : A.card=1 := by
      simp [A,Finset.card_erase_of_mem,show j∈(Finset.univ : Finset (Fin 3)).erase i by simp [hne.symm]]
    simp [hc] at ht
    omega
  have h1 := bound j
  simp only [row,Fin.sum_univ_two] at h1 pos
  by_cases a : G (M i p) (M j 0) <;> by_cases b : G (M i p) (M j 1) <;> simp_all

#print axioms moore_second_degree
#print axioms moore_matching
end Erdos151N63
