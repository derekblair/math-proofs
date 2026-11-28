import N62PrivateSums
import N62MarkedPressure

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

theorem private_charges_total
    (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sf : Free (Forbidden G) (S : Set V))
    (blocked : ∀ x∈X, ¬Free (Forbidden G) (insert x (S : Set V))) :
    (∑ u∈S, ((privateFirst G S X u).card+(privateSecond G S X u).card)) =
      2*(privateColumns G S X).card := by
  classical
  let F (u x : V) : Prop := ((Acol G S x ∨ Bcol G S x) ∧ u∈ns (G:=G) S x) ∨
     (Ccol G S x ∧ u∈ls (G:=G) S x)
  let Q (u x : V) : Prop := (Acol G S x ∨ Ccol G S x) ∧ u∈ls (G:=G) S x
  have transF := (transpose F S X).symm
  have transQ := (transpose Q S X).symm
  change (∑ u∈S,(privateFirst G S X u).card) = ∑ x∈X, (S.filter (fun u=>F u x)).card at transF
  change (∑ u∈S,(privateSecond G S X u).card) = ∑ x∈X, (S.filter (fun u=>Q u x)).card at transQ
  have countF (x : V) (hx : x∈X) :
    (S.filter (fun u=>F u x)).card+(S.filter (fun u=>Q u x)).card =
      if Acol G S x ∨ Bcol G S x ∨ Ccol G S x then 2 else 0 := by
    have fn : S.filter (fun u=>u∈ns (G:=G) S x)=ns (G:=G) S x := by
      ext u
      simp only [Finset.mem_filter,and_iff_right_iff_imp]
      exact fun h => ((mem_ns (G:=G) S x).mp h).1
    have fl : S.filter (fun u=>u∈ls (G:=G) S x)=ls (G:=G) S x := by
      ext u
      simp only [Finset.mem_filter,and_iff_right_iff_imp]
      exact fun h => ((mem_ls (G:=G) S x).mp h).1
    by_cases a : Acol G S x
    · have n : (ns (G:=G) S x).card=1 := a
      have l := (blocked_one_lone (G:=G) S x sym irr sf (blocked x hx) n).1
      have nc : ¬Ccol G S x := fun h => by have c : (ns (G:=G) S x).card=2 := h.1; omega
      simp only [F,Q,a,nc,true_or,true_and,or_false,false_and,if_true,fn,fl,n,l]
    · by_cases b : Bcol G S x
      · have n : (ns (G:=G) S x).card=2 := b.1
        have l : (ls (G:=G) S x).card=0 := b.2
        have nc : ¬Ccol G S x := fun h => by have c : (ls (G:=G) S x).card=1 := h.2; omega
        simp only [F,Q,a,b,nc,false_or,true_and,false_and,or_false,if_true,fn,n,Finset.filter_false,Finset.card_empty,Nat.add_zero]
      · by_cases c : Ccol G S x
        · have l : (ls (G:=G) S x).card=1 := c.2
          simp only [F,Q,a,b,c,false_or,false_and,true_and,if_true,fl,l]
        · simp [F,Q,a,b,c]
  rw [Finset.sum_add_distrib,transF,transQ,←Finset.sum_add_distrib]
  have h := Finset.sum_congr (s₁:=X) (s₂:=X) rfl countF
  rw [h]
  exact (indicator_count_flexible X (fun x => Acol G S x ∨ Bcol G S x ∨ Ccol G S x) 2 _
    (fun x hx h => by simp [h]) (fun x hx h => by simp [h])).symm

theorem private_charges_saturated
    (S X : Finset V) (sc : S.card=12)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sf : Free (Forbidden G) (S : Set V)) (dis : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (pr : (privateColumns G S X).card=12) :
    ∀ u∈S, (privateFirst G S X u).card+(privateSecond G S X u).card=2 := by
  have blocked (x : V) (hx : x∈X) := all_exterior_blocked_12 G S sc upper x (Finset.disjoint_left.mp dis hx)
  have e := private_charges_total G S X sym irr sf blocked
  rw [pr] at e
  have row := private_slots_charged G S X sym irr tf sc sf dis upper
  intro u hu
  by_contra! h
  have r := row u hu
  have lt := Finset.sum_lt_sum row ⟨u,hu,show
    (privateFirst G S X u).card+(privateSecond G S X u).card < 2 by omega⟩
  rw [e] at lt
  simp [sc] at lt

#print axioms private_charges_total
#print axioms private_charges_saturated
end Erdos151N62
