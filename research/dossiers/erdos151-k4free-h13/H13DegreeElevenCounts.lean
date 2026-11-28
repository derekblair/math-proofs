import H13DegreeElevenOwners
import H12DegreeTenCounts
namespace Erdos151H12
open Erdős151 Erdos151Ramsey
open scoped BigOperators

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : V → V → Prop) (S : Finset V)

theorem degreeEleven_counts_h13 [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFreeLinks G) (h10 : S.card=11) (hS : Free (Forbidden G) (S : Set V))
    (B : Finset V) (hBS : Disjoint B S)
    (blocked : ∀ x∈B, ¬ Free (Forbidden G) (insert x (S : Set V)))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12) :
    let a := (weightedSet B (Acol G S)).card
    let b := (weightedSet B (Bcol G S)).card
    let c := (weightedSet B (Ccol G S)).card
    let d := (weightedSet B (Dcol G S)).card
    a≤22 ∧ 5*a+4*b+5*c≤110 ∧ a+c+2*d≤∑ x∈B,lcol G S x ∧
      3*B.card ≤ (∑ x∈B,ncol G S x) + (2*a+b+c+d) := by
  classical
  dsimp
  let A (x : V) : Nat := if Acol G S x then 1 else 0
  let D (x : V) : Nat := if Dcol G S x then 1 else 0
  let Q (x : V) : Nat := if Bcol G S x then 1 else 0
  let C (x : V) : Nat := if Ccol G S x then 1 else 0
  have hA : (weightedSet B (Acol G S)).card = ∑ x∈B,A x := by
    simpa only [Nat.one_mul] using indicator_count B (Acol G S) 1
  have hB : (weightedSet B (Bcol G S)).card = ∑ x∈B,Q x := by
    simpa only [Nat.one_mul] using indicator_count B (Bcol G S) 1
  have hC : (weightedSet B (Ccol G S)).card = ∑ x∈B,C x := by
    simpa only [Nat.one_mul] using indicator_count B (Ccol G S) 1
  have hD : (weightedSet B (Dcol G S)).card = ∑ x∈B,D x := by
    simpa only [Nat.one_mul] using indicator_count B (Dcol G S) 1
  have hLocal (u : V) (hu : u∈S) := degreeEleven_private_capacity_h13 G sym irr tf S B h10 hS hBS blocked upper u hu
  have hq2 (u : V) (hu : u∈S) : (lonePrivatePool G S B u).card ≤ 2 := by
    have hIso := privatePool_isolated G sym S B hS hBS blocked u
    have hi := privatePool_alpha_two_h13 G sym S B h10 hS hBS upper u hu
    exact hi _ hIso.1 (fun a ha b hb => hIso.2 a ha b (hIso.1 hb))
  have hb (x : V) (hx : x∈B) := blocked_degreeTen_local G S sym irr hS x (blocked x hx)
  rw [hA,hB,hC,hD]
  refine ⟨?_,?_,?_,?_⟩
  · calc
      ∑ x∈B,A x ≤ ∑ x∈B,(qs (G:=G) S x).card :=
        Finset.sum_le_sum (fun x hx => (hb x hx).1)
      _ = ∑ u∈S,(lonePrivatePool G S B u).card := qs_sum_flip G S B
      _ ≤ ∑ _u∈S, (2:Nat) := Finset.sum_le_sum hq2
      _ = 22 := by simp [h10]
  · calc
      5*(∑ x∈B,A x)+4*(∑ x∈B,Q x)+5*(∑ x∈B,C x) =
        ∑ x∈B,(5*A x+4*Q x+5*C x) := by simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ ∑ x∈B,(2*(ps (G:=G) S x).card+3*(qs (G:=G) S x).card) :=
        Finset.sum_le_sum (fun x hx => (hb x hx).2.1)
      _ = ∑ u∈S,(2*(privatePool G S B u).card+3*(lonePrivatePool G S B u).card) := by
        simp only [Finset.sum_add_distrib,←Finset.mul_sum,ps_sum_flip G S B,qs_sum_flip G S B]
      _ ≤ ∑ _u∈S,(10:Nat) := Finset.sum_le_sum hLocal
      _ = 110 := by simp [h10]
  · calc
      (∑ x∈B,A x)+(∑ x∈B,C x)+2*(∑ x∈B,D x) = ∑ x∈B,(A x+C x+2*D x) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ ∑ x∈B,lcol G S x := Finset.sum_le_sum (fun x hx => (hb x hx).2.2.1)
  · calc
      3*B.card = ∑ _x∈B,(3:Nat) := by simp [Nat.mul_comm]
      _ ≤ ∑ x∈B, (ncol G S x+(2*A x+Q x+C x+D x)) :=
        Finset.sum_le_sum (fun x hx => (hb x hx).2.2.2)
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.mul_sum]

end Erdos151H12
