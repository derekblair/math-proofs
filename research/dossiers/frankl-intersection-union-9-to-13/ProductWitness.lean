import Decode

namespace IU
abbrev tail (s : Finset Nat) (t : Nat) := s.filter (fun i => ¬i<t)
theorem tail_card (s : Finset Nat) (t : Nat) : (tail s t).card=s.card-pr s t := by
  have E := Finset.card_filter_add_card_filter_not (s:=s) (fun i => i<t)
  change pr s t +(tail s t).card=s.card at E
  omega

theorem product_pair {n l r p q : Nat} {A B : Finset Nat}
    (aR : A⊆Finset.range n) (bR : B⊆Finset.range n) (rq : q≤r) (rn : r≤n)
    (aL : l+p≤2*pr A l) (bL : l+p≤2*pr B l)
    (aU : 2*(tail A (n-r)).card≤r-q) (bU : 2*(tail B (n-r)).card≤r-q) :
    p≤(A∩B).card ∧ (A∪B).card≤n-q := by
  have pref (X : Finset Nat) (k : Nat) : below X k⊆Finset.range k :=
    fun x h => Finset.mem_range.mpr (Finset.mem_filter.mp h).2
  have L := Finset.card_le_card (Finset.union_subset (pref A l) (pref B l))
  rw [Finset.card_range] at L
  have I : below A l∩below B l⊆A∩B := fun x hx =>
    Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).1,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).1⟩
  have ci := Finset.card_le_card I
  have C := Finset.card_union_add_card_inter (below A l) (below B l)
  change _ = pr A l+pr B l at C
  have before : pr (A∪B) (n-r)≤n-r := by
    have h := Finset.card_le_card (pref (A∪B) (n-r))
    rwa [Finset.card_range] at h
  have E : tail (A∪B) (n-r)=tail A (n-r) ∪ tail B (n-r) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_union]
    grind
  have after : (tail (A∪B) (n-r)).card≤(tail A (n-r)).card+(tail B (n-r)).card := by
    rw [E]
    exact Finset.card_union_le _ _
  have count := tail_card (A∪B) (n-r)
  have leC : pr (A∪B) (n-r)≤(A∪B).card := Finset.card_filter_le _ _
  omega

def productMasks (n l r p q : Nat) : List Nat :=
  (List.range (2^n)).filter fun a =>
    decide (l+p≤2*rank a l ∧ 2*(rank a n-rank a (n-r))≤r-q)

theorem product_family (n l r p q : Nat) (ln : l≤n) (rn : r≤n) (qr : q≤r) :
    ∃ F : Finset (Finset Nat), IsIU F n p q ∧ F.card=(productMasks n l r p q).length := by
  let L := productMasks n l r p q
  let F := L.toFinset.image (decode n)
  have values (a : Nat) (h : a∈L) : a<2^n ∧
      l+p≤2*pr (decode n a) l ∧ 2*(tail (decode n a) (n-r)).card≤r-q := by
    obtain ⟨u,v⟩ := List.mem_filter.mp h
    have bound := List.mem_range.mp u
    have cond := of_decide_eq_true v
    rw [←mask_decode bound,rank_mask _ ln,rank_full (decode_range n a),
      rank_mask _ (Nat.sub_le ..)] at cond
    exact ⟨bound,cond.1,by rw [tail_card]; exact cond.2⟩
  refine ⟨F,⟨?_,?_⟩,?_⟩
  · intro A h
    obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp h
    exact decode_range ..
  · intro A hA B hB
    obtain ⟨a,am,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b,bm,rfl⟩ := Finset.mem_image.mp hB
    have aV := values a (List.mem_toFinset.mp am)
    have bV := values b (List.mem_toFinset.mp bm)
    exact product_pair (decode_range ..) (decode_range ..) qr rn
      aV.2.1 bV.2.1 aV.2.2 bV.2.2
  · change (L.toFinset.image (decode n)).card=L.length
    rw [Finset.card_image_of_injOn,List.toFinset_card_of_nodup]
    · exact List.Nodup.filter _ List.nodup_range
    · intro a ha b hb E
      have aa := mask_decode (values a (List.mem_toFinset.mp ha)).1
      have bb := mask_decode (values b (List.mem_toFinset.mp hb)).1
      exact aa.symm.trans ((congrArg (fun A => mask A n) E).trans bb)

#print axioms product_family
end IU
