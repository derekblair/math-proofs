import H13DegreeTwelveLower

namespace Erdos151H12
open Erdős151
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : V → V → Prop) (S B : Finset V)

theorem degreeTwelve_special_cost_h13 [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFreeLinks G)
    (h11 : S.card=12) (hS : Free (Forbidden G) (S : Set V)) (hBS : Disjoint B S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12) :
    2*(specialCols G S B).card ≤ (∑ x∈B,lcol G S x)+12 := by
  classical
  have blocked (x : V) (hx : x∈B) :=
    all_exterior_blocked_12 G S h11 upper x (Finset.disjoint_left.mp hBS hx)
  have hA : (weightedSet B (Acol G S)).card ≤ 12 := by
    rw [←singlesFor_sum G S B]
    have hrow (u : V) (hu : u∈S) : (singlesFor G S B u).card ≤ 1 := by
      have h0 := degreeTwelve_private_capacity_h13 G sym irr tf S B h11 hS hBS upper u hu
      have hL := privatePool_isolated G sym S B hS hBS blocked u
      have hqi := Finset.card_le_card hL.1
      have hAq := Finset.card_le_card (show singlesFor G S B u ⊆ lonePrivatePool G S B u from
        fun x hx => (singlesFor_ownership G sym irr S B hS blocked u x hx).2.2)
      omega
    have ht := Finset.sum_le_sum (g:=fun _ => 1) hrow
    simpa [h11] using ht
  have hLx (x : V) (hx : x∈B) :
      (if Acol G S x ∨ Dcol G S x then (2:Nat) else 0) ≤
        lcol G S x + (if Acol G S x then 1 else 0) := by
    unfold Acol Dcol
    by_cases ha : ncol G S x=1
    · have h := (blocked_one_lone (G:=G) S x sym irr hS (blocked x hx) ha).1
      change lcol G S x = 1 at h
      simp [ha,h]
    · by_cases hd : ncol G S x = 2 ∧ lcol G S x = 2
      · simp [ha,hd,hd.2]
      · simp [ha,hd]
  calc
    2*(specialCols G S B).card = ∑ x∈B,(if Acol G S x ∨ Dcol G S x then (2:Nat) else 0) :=
      indicator_count_flexible B _ 2 _ (fun x hx h => by simp [h]) (fun x hx h => by simp [h])
    _ ≤ ∑ x∈B,(lcol G S x + (if Acol G S x then 1 else 0)) := Finset.sum_le_sum hLx
    _ = (∑ x∈B,lcol G S x)+(weightedSet B (Acol G S)).card := by
      rw [Finset.sum_add_distrib]
      have he := indicator_count_flexible B (Acol G S) 1 (fun x => if Acol G S x then 1 else 0)
        (fun x hx h => by simp [h]) (fun x hx h => by simp [h])
      simpa only [Nat.one_mul] using congrArg ((∑ x∈B,lcol G S x)+ ·) he.symm
    _ ≤ _ := by omega

end Erdos151H12
