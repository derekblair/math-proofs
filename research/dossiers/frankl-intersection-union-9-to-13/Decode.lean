import Encode

namespace IU

def decode (n a : Nat) : Finset Nat := (Finset.range n).filter (fun i => a.testBit i = true)

theorem decode_range (n a : Nat) : decode n a⊆Finset.range n := Finset.filter_subset _ _

theorem mask_decode {n a : Nat} (h : a<2^n) : mask (decode n a) n=a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bits]
  by_cases e : i<n
  · simp only [decode,Finset.mem_filter,Finset.mem_range,e,true_and]
    cases a.testBit i <;> decide
  · rw [Nat.testBit_lt_two_pow (x:=a) (h.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (by omega)))]
    simp [e]

private theorem overlap_prefix {n t : Nat} (A B : Finset Nat) (ht : t≤n)
    (aR : A⊆Finset.range n) (bR : B⊆Finset.range n) :
    pr A t + pr B t ≤ t + (A∩B).card := by
  have sub (S : Finset Nat) (sR : S⊆Finset.range n) : below S t⊆Finset.range t := by
    intro x hx
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
  have U := Finset.card_le_card (Finset.union_subset (sub A aR) (sub B bR))
  rw [Finset.card_range] at U
  have I := Finset.card_le_card (show below A t∩below B t⊆A∩B from by
    intro x hx
    obtain ⟨a,b⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp a).1,(Finset.mem_filter.mp b).1⟩)
  have E := Finset.card_union_add_card_inter (below A t) (below B t)
  change _ = pr A t+pr B t at E
  omega

theorem decode_edge {n p q a b : Nat} (aR : a<2^n) (bR : b<2^n)
    (h : edge n p q a b=true) :
    p≤(decode n a∩decode n b).card ∧ (decode n a∪decode n b).card≤n-q := by
  unfold edge at h
  obtain ⟨t,T,ht⟩ := List.any_eq_true.mp h
  have tn : t≤n := Nat.lt_succ_iff.mp (List.mem_range.mp T)
  replace ht := of_decide_eq_true ht
  let A := decode n a
  let B := decode n b
  rw [←mask_decode aR,←mask_decode bR,rank_full (decode_range n a),rank_full (decode_range n b),
    rank_mask A tn,rank_mask B tn] at ht
  change max p (A.card+B.card-(n-q))+t≤pr A t+pr B t at ht
  have H := overlap_prefix A B tn (decode_range n a) (decode_range n b)
  have E := Finset.card_union_add_card_inter A B
  change p≤(A∩B).card ∧ (A∪B).card≤n-q
  omega

theorem clique_decode {n p q : Nat} (F : Finset Nat)
    (verts : ∀ a∈F, a∈admissible n p q)
    (edges : ∀ a∈F, ∀ b∈F, a≠b → edge n p q a b=true) :
    let G := F.image (decode n)
    G.card=F.card ∧ IsIU G n p q := by
  have bound (a : Nat) (h : a∈F) : a<2^n := List.mem_range.mp (List.mem_filter.mp (verts a h)).1
  refine ⟨Finset.card_image_of_injOn ?_,?_,?_⟩
  · intro a A b B E
    exact (mask_decode (bound a A)).symm.trans ((congrArg (fun X => mask X n) E).trans (mask_decode (bound b B)))
  · intro a ha
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp ha
    exact decode_range n u
  · intro A ha B hb
    obtain ⟨a,aF,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b,bF,rfl⟩ := Finset.mem_image.mp hb
    apply decode_edge (bound a aF) (bound b bF)
    by_cases h : a=b
    · subst b
      exact (Bool.and_eq_true_iff.mp (List.mem_filter.mp (verts a aF)).2).2
    · exact edges a aF b bF h

#print axioms decode_edge
#print axioms clique_decode
end IU
