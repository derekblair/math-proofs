import H12DegreeTenOwners

namespace Erdos151H12
open Erdős151 Erdos151Ramsey
open scoped BigOperators

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : V → V → Prop) (S : Finset V)

noncomputable def ncol (x : V) : Nat := (ns (G:=G) S x).card
noncomputable def lcol (x : V) : Nat := (ls (G:=G) S x).card

noncomputable def Acol (x : V) : Prop := ncol G S x = 1
noncomputable def Bcol (x : V) : Prop := ncol G S x = 2 ∧ lcol G S x = 0
noncomputable def Ccol (x : V) : Prop := ncol G S x = 2 ∧ lcol G S x = 1
noncomputable def Dcol (x : V) : Prop := ncol G S x = 2 ∧ lcol G S x = 2

noncomputable def weightedSet (B : Finset V) (p : V → Prop) : Finset V := by
  classical exact B.filter p

theorem indicator_count (B : Finset V) (p : V→Prop) (k : Nat) :
    k*(weightedSet B p).card = ∑ x∈B, (by classical exact if p x then k else 0) := by
  classical
  rw [←Finset.sum_filter]
  simp [weightedSet, Nat.mul_comm]

theorem blocked_degreeTen_local (sym : ∀ {a b}, G a b → G b a)
    (irr : ∀ a, ¬ G a a) (hS : Free (Forbidden G) (S : Set V))
    (x : V) (hx : ¬ Free (Forbidden G) (insert x (S : Set V))) :
    (let a := by classical exact if Acol G S x then (1 : Nat) else 0
     let b := by classical exact if Bcol G S x then (1 : Nat) else 0
     let c := by classical exact if Ccol G S x then (1 : Nat) else 0
     let d := by classical exact if Dcol G S x then (1 : Nat) else 0
     a ≤ (qs (G:=G) S x).card ∧
       5*a+4*b+5*c ≤ 2*(ps (G:=G) S x).card+3*(qs (G:=G) S x).card ∧
       a+c+2*d ≤ lcol G S x ∧
       3 ≤ ncol G S x + (2*a+b+c+d)) := by
  classical
  dsimp
  unfold Acol Bcol Ccol Dcol
  have h1 := blocked_one_lone (G:=G) S x sym irr hS hx
  have h20 := blocked_two_no_lone (G:=G) S x sym irr hS
  have h21 := blocked_two_one_lone (G:=G) S x sym irr hS
  have h := Finset.card_pos.mpr (blocked_support_ne (G:=G) S x sym irr hS hx)
  have hl := Finset.card_le_card (lone_support_subset (G:=G) S x)
  change 0 < ncol G S x at h
  change lcol G S x ≤ ncol G S x at hl
  by_cases hs1 : ncol G S x = 1
  · obtain ⟨hl1,hp,hq⟩ := h1 hs1
    change lcol G S x = 1 at hl1
    simp [hs1,hl1]
    exact ⟨Finset.card_pos.mp hq,by omega⟩
  by_cases hs2 : ncol G S x = 2
  · by_cases hl0 : lcol G S x = 0
    · have hp := h20 hs2 hl0
      simp [hs1,hs2,hl0]
      omega
    by_cases hl1 : lcol G S x = 1
    · obtain ⟨hp,hq⟩ := h21 hs2 hl1
      simp [hs1,hs2,hl1]
      omega
    have hl2 : lcol G S x = 2 := by omega
    simp [hs1,hs2,hl2]
  simp [hs1,hs2]
  omega

theorem ps_sum_flip (B : Finset V) :
    ∑ x∈B, (ps (G:=G) S x).card = ∑ u∈S,(privatePool G S B u).card := by
  classical
  let R (u x : V) : Prop := u ∈ ps (G:=G) S x
  have co (x : V) : colCount S R x = (ps (G:=G) S x).card := by
    unfold colCount
    congr 1
    ext w
    simp only [Finset.mem_filter,R]
    exact ⟨And.right,fun H => ⟨((mem_ps (G:=G) S x).mp H).1,H⟩⟩
  have row (u : V) : rowCount B R u = (privatePool G S B u).card := rfl
  simpa only [co,row] using flipCounts S B R

theorem qs_sum_flip (B : Finset V) :
    ∑ x∈B, (qs (G:=G) S x).card = ∑ u∈S,(lonePrivatePool G S B u).card := by
  classical
  let R (u x : V) : Prop := u ∈ qs (G:=G) S x
  have co (x : V) : colCount S R x = (qs (G:=G) S x).card := by
    unfold colCount
    congr 1
    ext w
    simp only [Finset.mem_filter,R]
    exact ⟨And.right,fun H => ⟨((mem_qs (G:=G) S x).mp H).1,H⟩⟩
  have row (u : V) : rowCount B R u = (lonePrivatePool G S B u).card := rfl
  simpa only [co,row] using flipCounts S B R

theorem degreeTen_counts [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFreeLinks G) (h10 : S.card=10) (hS : Free (Forbidden G) (S : Set V))
    (B : Finset V) (hBS : Disjoint B S)
    (blocked : ∀ x∈B, ¬ Free (Forbidden G) (insert x (S : Set V)))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11) :
    let a := (weightedSet B (Acol G S)).card
    let b := (weightedSet B (Bcol G S)).card
    let c := (weightedSet B (Ccol G S)).card
    let d := (weightedSet B (Dcol G S)).card
    a≤20 ∧ 5*a+4*b+5*c≤100 ∧ a+c+2*d≤∑ x∈B,lcol G S x ∧
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
  have hLocal (u : V) (hu : u∈S) := degreeTen_private_capacity G sym irr tf S B h10 hS hBS blocked upper u hu
  have hq2 (u : V) (hu : u∈S) : (lonePrivatePool G S B u).card ≤ 2 := by
    have hIso := privatePool_isolated G sym S B hS hBS blocked u
    have hi := privatePool_alpha_two G sym S B h10 hS hBS upper u hu
    exact hi _ hIso.1 (fun a ha b hb => hIso.2 a ha b (hIso.1 hb))
  have hb (x : V) (hx : x∈B) := blocked_degreeTen_local G S sym irr hS x (blocked x hx)
  rw [hA,hB,hC,hD]
  refine ⟨?_,?_,?_,?_⟩
  · calc
      ∑ x∈B,A x ≤ ∑ x∈B,(qs (G:=G) S x).card :=
        Finset.sum_le_sum (fun x hx => (hb x hx).1)
      _ = ∑ u∈S,(lonePrivatePool G S B u).card := qs_sum_flip G S B
      _ ≤ ∑ _u∈S, (2:Nat) := Finset.sum_le_sum hq2
      _ = 20 := by simp [h10]
  · calc
      5*(∑ x∈B,A x)+4*(∑ x∈B,Q x)+5*(∑ x∈B,C x) =
        ∑ x∈B,(5*A x+4*Q x+5*C x) := by simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ ∑ x∈B,(2*(ps (G:=G) S x).card+3*(qs (G:=G) S x).card) :=
        Finset.sum_le_sum (fun x hx => (hb x hx).2.1)
      _ = ∑ u∈S,(2*(privatePool G S B u).card+3*(lonePrivatePool G S B u).card) := by
        simp only [Finset.sum_add_distrib,←Finset.mul_sum,ps_sum_flip G S B,qs_sum_flip G S B]
      _ ≤ ∑ _u∈S,(10:Nat) := Finset.sum_le_sum hLocal
      _ = 100 := by simp [h10]
  · calc
      (∑ x∈B,A x)+(∑ x∈B,C x)+2*(∑ x∈B,D x) = ∑ x∈B,(A x+C x+2*D x) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ ∑ x∈B,lcol G S x := Finset.sum_le_sum (fun x hx => (hb x hx).2.2.1)
  · calc
      3*B.card = ∑ _x∈B,(3:Nat) := by simp [Nat.mul_comm]
      _ ≤ ∑ x∈B, (ncol G S x+(2*A x+Q x+C x+D x)) :=
        Finset.sum_le_sum (fun x hx => (hb x hx).2.2.2)
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.mul_sum]

#print axioms blocked_degreeTen_local
#print axioms degreeTen_counts
end Erdos151H12
