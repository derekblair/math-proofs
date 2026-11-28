import H12DegreeElevenLocal

namespace Erdos151H12
open Erdős151
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : V → V → Prop) (S B : Finset V)

noncomputable def specialCols : Finset V := weightedSet B (fun x => Acol G S x ∨ Dcol G S x)
noncomputable def privateColumns : Finset V :=
  weightedSet B (fun x => Acol G S x ∨ Bcol G S x ∨ Ccol G S x)

theorem indicator_count_flexible (B : Finset V) (p : V → Prop) (k : Nat) (f : V → Nat)
    (hit : ∀ x∈B, p x → f x = k) (miss : ∀ x∈B, ¬ p x → f x = 0) :
    k*(weightedSet B p).card = ∑ x∈B,f x := by
  classical
  rw [indicator_count]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : p x
  · rw [if_pos h,hit x hx h]
  · rw [if_neg h,miss x hx h]

theorem degreeEleven_local_demand
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (hS : Free (Forbidden G) (S : Set V))
    (x : V) (hx : ¬ Free (Forbidden G) (insert x (S : Set V))) :
      (let p := by classical exact if Acol G S x ∨ Bcol G S x ∨ Ccol G S x then (1:Nat) else 0
       let s := by classical exact if Acol G S x ∨ Dcol G S x then (1:Nat) else 0
       3 ≤ ncol G S x + p + s ∧ 2*p ≤ (ps (G:=G) S x).card + (qs (G:=G) S x).card) := by
  classical
  dsimp
  unfold Acol Bcol Ccol Dcol
  have h1 := blocked_one_lone (G:=G) S x sym irr hS hx
  have h20 := blocked_two_no_lone (G:=G) S x sym irr hS
  have h21 := blocked_two_one_lone (G:=G) S x sym irr hS
  have h := Finset.card_pos.mpr (blocked_support_ne (G:=G) S x sym irr hS hx)
  have hl := Finset.card_le_card (lone_support_subset (G:=G) S x)
  change 0<ncol G S x at h
  change lcol G S x≤ncol G S x at hl
  by_cases hs1 : ncol G S x=1
  · obtain ⟨_,hp,hq⟩ := h1 hs1
    simp [hs1]
    omega
  by_cases hs2 : ncol G S x=2
  · by_cases hl0 : lcol G S x=0
    · have hp := h20 hs2 hl0
      simp [hs2,hl0]
      omega
    by_cases hl1 : lcol G S x=1
    · obtain ⟨hp,hq⟩ := h21 hs2 hl1
      simp [hs2,hl1]
      omega
    have hl2 : lcol G S x=2 := by omega
    simp [hs2,hl2]
  simp [hs1,hs2]
  omega

theorem degreeEleven_lower_incidence [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFreeLinks G)
    (h11 : S.card=11) (hS : Free (Forbidden G) (S : Set V)) (hBS : Disjoint B S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11) :
    3*B.card ≤ (∑ x∈B,ncol G S x)+11+(specialCols G S B).card := by
  classical
  let p (x : V) : Nat := if Acol G S x ∨ Bcol G S x ∨ Ccol G S x then 1 else 0
  let s (x : V) : Nat := if Acol G S x ∨ Dcol G S x then 1 else 0
  have localD (x : V) (hx : x∈B) := degreeEleven_local_demand G S sym irr hS x
    (all_exterior_blocked_11 G S h11 upper x (Finset.disjoint_left.mp hBS hx))
  have hsp : (specialCols G S B).card = ∑ x∈B,s x := by
    unfold specialCols
    rw [←Nat.one_mul ((weightedSet B (fun x => Acol G S x ∨ Dcol G S x)).card)]
    exact indicator_count_flexible B _ 1 s (fun x hx h => by simp [s,h])
      (fun x hx h => by simp [s,h])
  have hp : 2*(∑ x∈B,p x) ≤ 22 := by
    calc
      _ = ∑ x∈B,2*p x := by rw [Finset.mul_sum]
      _ ≤ ∑ x∈B,((ps (G:=G) S x).card+(qs (G:=G) S x).card) :=
        Finset.sum_le_sum (fun x hx => (localD x hx).2)
      _ = ∑ u∈S,((privatePool G S B u).card+(lonePrivatePool G S B u).card) := by
        simp only [Finset.sum_add_distrib,ps_sum_flip G S B,qs_sum_flip G S B]
      _ ≤ ∑ _u∈S,(2:Nat) :=
        Finset.sum_le_sum (degreeEleven_private_capacity G sym irr tf S B h11 hS hBS upper)
      _ = _ := by simp [h11]
  have hw : 3*B.card ≤ (∑ x∈B,ncol G S x)+(∑ x∈B,p x)+(∑ x∈B,s x) := by
    calc
      _ = ∑ _x∈B,(3:Nat) := by simp [Nat.mul_comm]
      _ ≤ ∑ x∈B,(ncol G S x+p x+s x) := Finset.sum_le_sum (fun x hx => (localD x hx).1)
      _ = _ := by simp only [Finset.sum_add_distrib]
  omega

#print axioms degreeEleven_lower_incidence
end Erdos151H12
