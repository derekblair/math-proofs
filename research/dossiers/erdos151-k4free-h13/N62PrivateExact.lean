import H13DegreeTwelveLocal
import H12DegreeElevenLower

namespace Erdos151H12
open Erdős151
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : V → V → Prop) (S B : Finset V)

theorem degreeTwelve_exact_private_incidence [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFreeLinks G)
    (h11 : S.card=12) (hS : Free (Forbidden G) (S : Set V)) (hBS : Disjoint B S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12) :
    3*B.card ≤ (∑ x∈B,ncol G S x)+(privateColumns G S B).card+
      (specialCols G S B).card ∧ (privateColumns G S B).card≤12 := by
  classical
  let p (x : V) : Nat := if Acol G S x ∨ Bcol G S x ∨ Ccol G S x then 1 else 0
  let s (x : V) : Nat := if Acol G S x ∨ Dcol G S x then 1 else 0
  have localD (x : V) (hx : x∈B) := degreeEleven_local_demand G S sym irr hS x
    (all_exterior_blocked_12 G S h11 upper x (Finset.disjoint_left.mp hBS hx))
  have hsp : (specialCols G S B).card = ∑ x∈B,s x := by
    unfold specialCols
    rw [←Nat.one_mul ((weightedSet B (fun x => Acol G S x ∨ Dcol G S x)).card)]
    exact indicator_count_flexible B _ 1 s (fun x hx h => by simp [s,h])
      (fun x hx h => by simp [s,h])
  have hp : 2*(∑ x∈B,p x) ≤ 24 := by
    calc
      _ = ∑ x∈B,2*p x := by rw [Finset.mul_sum]
      _ ≤ ∑ x∈B,((ps (G:=G) S x).card+(qs (G:=G) S x).card) :=
        Finset.sum_le_sum (fun x hx => (localD x hx).2)
      _ = ∑ u∈S,((privatePool G S B u).card+(lonePrivatePool G S B u).card) := by
        simp only [Finset.sum_add_distrib,ps_sum_flip G S B,qs_sum_flip G S B]
      _ ≤ ∑ _u∈S,(2:Nat) :=
        Finset.sum_le_sum (degreeTwelve_private_capacity_h13 G sym irr tf S B h11 hS hBS upper)
      _ = _ := by simp [h11]
  have hw : 3*B.card ≤ (∑ x∈B,ncol G S x)+(∑ x∈B,p x)+(∑ x∈B,s x) := by
    calc
      _ = ∑ _x∈B,(3:Nat) := by simp [Nat.mul_comm]
      _ ≤ ∑ x∈B,(ncol G S x+p x+s x) := Finset.sum_le_sum (fun x hx => (localD x hx).1)
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hpc : (privateColumns G S B).card = ∑ x∈B,p x := by
    unfold privateColumns
    rw [←Nat.one_mul ((weightedSet B (fun x => Acol G S x ∨ Bcol G S x ∨ Ccol G S x)).card)]
    exact indicator_count_flexible B _ 1 p (fun x hx h => by simp [p,h])
      (fun x hx h => by simp [p,h])
  omega

#print axioms degreeTwelve_exact_private_incidence
end Erdos151H12
