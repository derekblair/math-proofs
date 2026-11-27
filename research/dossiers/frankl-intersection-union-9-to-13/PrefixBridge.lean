import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

namespace IU
abbrev below (s : Finset Nat) (t : Nat) := s.filter (· < t)
abbrev pr (s : Finset Nat) (t : Nat) := (below s t).card

theorem leftmost (s : Finset Nat) (k : Nat) (h : k≤s.card) :
    ∃ u ⊆ s, u.card=k ∧ ∀ t : Nat, pr u t=min k (pr s t) := by
  induction k generalizing s with
  | zero => exact ⟨∅,Finset.empty_subset _,by simp,fun _ => by simp⟩
  | succ k ih =>
    have non : s.Nonempty := Finset.card_pos.mp (by omega)
    let a := s.min' non
    have as : a∈s := Finset.min'_mem _ _
    have size : (s.erase a).card = s.card-1 := Finset.card_erase_of_mem as
    obtain ⟨u,us,uk,upr⟩ := ih (s.erase a) (by omega)
    have au : a∉u := fun hx => Finset.notMem_erase _ _ (us hx)
    refine ⟨insert a u,Finset.insert_subset as (us.trans (Finset.erase_subset _ _)),?_,?_⟩
    · rw [Finset.card_insert_of_notMem au,uk]
    · intro t
      by_cases H : a<t
      · have E : below (s.erase a) t = (below s t).erase a := by
          ext x; simp [and_assoc]
        have b : a∈below s t := Finset.mem_filter.mpr ⟨as,H⟩
        have C := upr t
        change pr u t = min k ((below (s.erase a) t).card) at C
        rw [E,Finset.card_erase_of_mem b] at C
        change pr u t = min k (pr s t-1) at C
        change (Finset.filter (·<t) (insert a u)).card = _
        rw [Finset.filter_insert,if_pos H,Finset.card_insert_of_notMem]
        · change pr u t+1 = _
          rw [C]
          have P : 0 < pr s t := Finset.card_pos.mpr ⟨a,b⟩
          omega
        · exact fun q => au ((Finset.mem_filter.mp q).1)
      · have SZ : below s t = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro b hb
          have bb := Finset.mem_filter.mp hb
          have lower : a≤b := Finset.min'_le s b bb.1
          omega
        have J : below (s.erase a) t = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have ss : below (s.erase a) t ⊆ below s t :=
            Finset.filter_subset_filter _ (Finset.erase_subset _ _)
          have x0 := ss hx
          rw [SZ] at x0
          exact Finset.notMem_empty x x0
        change (Finset.filter (·<t) (insert a u)).card = _
        rw [Finset.filter_insert,if_neg H]
        change pr u t = _
        rw [upr]
        change min k ((below (s.erase a) t).card) = min (k+1) ((below s t).card)
        rw [SZ,J]
        simp

/-- If the prefix defect of A,B never exceeds D, there is a left shift B′
with at most D overlaps with A. Coordinates are numbered 0,…,n−1. -/
theorem cap_intersection {n D : Nat} (A B : Finset Nat)
    (hA : A ⊆ Finset.range n) (hB : B ⊆ Finset.range n)
    (defect : ∀ t≤n, pr A t + pr B t ≤ t+D) :
    ∃ C ⊆ Finset.range n, C.card=B.card ∧
      (∀ t≤n, pr B t≤pr C t) ∧ (A∩C).card≤D := by
  obtain ⟨U,ua,uCard,uRanks⟩ := leftmost A (min D A.card) (Nat.min_le_right ..)
  let W := (Finset.range n \ A) ∪ U
  have wR : W ⊆ Finset.range n :=
    Finset.union_subset Finset.sdiff_subset (ua.trans hA)
  have eqR (t : Nat) (ht : t≤n) : below (Finset.range n) t = Finset.range t := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  have eqA (t : Nat) (ht : t≤n) : below A t ⊆ Finset.range t := by
    rw [←eqR t ht]
    exact Finset.filter_subset_filter _ hA
  have wr (t : Nat) (ht : t≤n) : pr W t = t - pr A t + min D (pr A t) := by
    have e : below W t = ((Finset.range t) \ below A t) ∪ below U t := by
      ext x
      simp only [W,Finset.mem_filter,Finset.mem_union,Finset.mem_sdiff,Finset.mem_range]
      constructor
      · rintro ⟨h|u,xt⟩
        · exact Or.inl ⟨xt,fun e => h.2 e.1⟩
        · exact Or.inr ⟨u,xt⟩
      · rintro (⟨xt,ha⟩|⟨hu,xt⟩)
        · exact ⟨Or.inl ⟨by omega, fun h => ha ⟨h,xt⟩⟩,xt⟩
        · exact ⟨Or.inr hu,xt⟩
    have d : Disjoint (Finset.range t \ below A t) (below U t) :=
      Finset.disjoint_left.mpr (fun x hx hu =>
        (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr
          ⟨ua (Finset.mem_filter.mp hu).1,(Finset.mem_filter.mp hu).2⟩))
    rw [show pr W t = (below W t).card from rfl,e,Finset.card_union_of_disjoint d,
      Finset.card_sdiff_of_subset (eqA t ht),Finset.card_range]
    change _ + pr U t = _
    rw [uRanks,Nat.min_assoc]
    have P : pr A t ≤ A.card := Finset.card_filter_le _ _
    rw [Nat.min_eq_right P]
  have rank_le (t : Nat) (ht : t≤n) : pr B t≤pr W t := by
    rw [wr t ht]
    have H := defect t ht
    have ba : pr B t≤t := by
      have S : below B t ⊆ below (Finset.range n) t := Finset.filter_subset_filter (·<t) hB
      rw [eqR t ht] at S
      simpa using Finset.card_le_card S
    have aa : pr A t≤t := by simpa using Finset.card_le_card (eqA t ht)
    omega
  have at_n {s : Finset Nat} (h : s ⊆ Finset.range n) : pr s n=s.card := by
    change (Finset.filter (·<n) s).card = s.card
    rw [Finset.filter_true_of_mem]
    exact fun x hx => Finset.mem_range.mp (h hx)
  have z := rank_le n le_rfl
  rw [at_n hB,at_n wR] at z
  obtain ⟨C,cW,cB,cPr⟩ := leftmost W B.card z
  refine ⟨C,cW.trans wR,cB,fun t ht => ?_,?_⟩
  · rw [cPr]
    exact le_min (Finset.card_filter_le _ _) (rank_le t ht)
  · have o : A∩C ⊆ U := by
      intro a h
      obtain ⟨aA,aC⟩ := Finset.mem_inter.mp h
      exact (Finset.mem_union.mp (cW aC)).resolve_left
        (fun h => (Finset.mem_sdiff.mp h).2 aA)
    exact (Finset.card_le_card o).trans (uCard ▸ Nat.min_le_left _ _)

#print axioms leftmost
#print axioms cap_intersection
end IU
