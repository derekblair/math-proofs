import LubellSlackTwo
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace IU.Lubell
open scoped BigOperators

def raw (n : Nat) (F : Family) : ℚ := ∑ A∈F, 1 / (n.choose A.card : ℚ)

theorem score_raw {F : Family} {n p q : Nat} (h : IsIU F n p q) :
    score n F = raw n F / ((n+1 : Nat) : ℚ) := by
  unfold score raw
  rw [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A a
  have l : A.card≤n := by simpa using Finset.card_le_card (h.1 A a)
  rw [score_normalized l]
  have q : 0 < (n.choose A.card : ℚ) := by exact_mod_cast Nat.choose_pos l
  field_simp

theorem proposed_valid {n t u : Nat} (h : t+u≤n) :
    IsIU (proposed n t u) n t u := by
  have c := cylinder_valid t u (n-(t+u))
  rw [Nat.add_sub_of_le h] at c
  rwa [proposed_eq h]

theorem raw_fails {n t u : Nat} (large : 2≤max t u) (bound : t+u+2≤n) :
    ∃ F : Family, IsIU F n t u ∧ raw n (proposed n t u)<raw n F := by
  obtain ⟨F,h,e⟩ := proposed_fails large bound
  rw [score_raw h,score_raw (proposed_valid (by omega))] at e
  refine ⟨F,h,?_⟩
  exact lt_of_not_ge fun L => (not_le_of_gt e) (div_le_div_of_nonneg_right L (by positivity))

theorem short_optimal {F : Family} {n t u : Nat} (lower : t+u≤n) (upper : n≤t+u+1)
    (V : IsIU F n t u) : score n F≤score n (proposed n t u) := by
  classical
  have B (A : Finset Nat) (a : A∈F) : t≤A.card ∧ A.card≤n-u := by
    simpa using V.2 A a A a
  have atMostT : (layer F t).card≤1 := Finset.card_le_one.mpr (by
    intro A a C c
    obtain ⟨af,ac⟩ := from_layer a
    obtain ⟨cf,cc⟩ := from_layer c
    have z := (V.2 A af C cf).1
    have E := Finset.eq_of_subset_of_card_le (show A∩C⊆A from Finset.inter_subset_left) (by omega)
    have s : A⊆C := E ▸ Finset.inter_subset_right
    exact Finset.eq_of_subset_of_card_le s (by omega))
  have atMostU : (layer F (n-u)).card≤1 := Finset.card_le_one.mpr (by
    intro A a C c
    obtain ⟨af,ac⟩ := from_layer a
    obtain ⟨cf,cc⟩ := from_layer c
    have z := (V.2 A af C cf).2
    have E := Finset.eq_of_subset_of_card_le (show A⊆A∪C from Finset.subset_union_left) (by omega)
    have s : C⊆A := E.symm ▸ Finset.subset_union_right
    exact (Finset.eq_of_subset_of_card_le s (by omega)).symm)
  have aux (k : Nat) :
      (∑ A∈layer F k, weight n A.card)=((layer F k).card : ℚ)*weight n k := by
    rw [←nsmul_eq_mul,←Finset.sum_const]
    exact Finset.sum_congr rfl (fun A h => by rw [(from_layer h).2])
  have mon {x : Nat} (e : x≤1) (k : Nat) :
      (x:ℚ) * weight n k ≤ weight n k := by
    have p : 0≤weight n k := by unfold weight; positivity
    simpa using mul_le_mul_of_nonneg_right (show (x:ℚ)≤1 by exact_mod_cast e) p
  rw [proposed_score lower]
  unfold score
  by_cases E : n=t+u
  · have F' : F=layer F t := by
      ext A
      constructor
      · intro a
        apply Finset.mem_filter.mpr
        exact ⟨a,by have := B A a; omega⟩
      · intro a
        exact (from_layer a).1
    rw [F',aux]
    exact E ▸ mon atMostT t
  · have E' : n=t+u+1 := by omega
    have R' : n-u=t+1 := by omega
    rw [R'] at atMostU
    have F' : F=layer F t∪layer F (t+1) := by
      ext A
      simp only [layer,Finset.mem_filter,Finset.mem_union]
      constructor
      · intro a
        have q := B A a
        rcases (show A.card=t ∨ A.card=t+1 by omega) with d|d
        · exact Or.inl ⟨a,d⟩
        · exact Or.inr ⟨a,d⟩
      · rintro (⟨a,_⟩|⟨a,_⟩) <;> exact a
    have dis : Disjoint (layer F t) (layer F (t+1)) := Finset.disjoint_left.mpr (by
      intro A ha hb
      have ab := (from_layer ha).2
      have bb := (from_layer hb).2
      omega)
    conv_lhs => rw [F']
    rw [Finset.sum_union dis,aux,aux]
    have H := add_le_add (mon atMostT t) (mon atMostU (t+1))
    have X := weight_extend (n:=t+u) (k:=t) (by omega)
    rw [←E'] at X
    exact H.trans_eq X

theorem proposed_optimal_iff_short {n t u : Nat} (room : t+u≤n) (large : 2≤max t u) :
    (∀ F : Family, IsIU F n t u → raw n F≤raw n (proposed n t u)) ↔ n≤t+u+1 := by
  constructor
  · intro H
    by_contra e
    obtain ⟨F,h,f⟩ := raw_fails (n:=n) (t:=t) (u:=u) large (by omega)
    exact (not_le_of_gt f) (H F h)
  · intro short F h
    have e := short_optimal room short h
    rw [score_raw h,score_raw (proposed_valid room)] at e
    exact (div_le_div_iff_of_pos_right (by positivity)).mp e

theorem slack_two_exact_raw (t u : Nat) (le : t≤u) (big : 2≤u) :
    IsIU (star t u) (t+u+2) t u ∧
       ∀ F : Family, IsIU F (t+u+2) t u → raw (t+u+2) F≤raw (t+u+2) (star t u) := by
  refine ⟨star_valid t u,?_⟩
  intro F h
  have L := slack_two_upper le big h
  rw [score_raw h,score_raw (star_valid t u)] at L
  exact (div_le_div_iff_of_pos_right (by positivity)).mp L

theorem opp_raw {F : Family} {n t u : Nat} (V : IsIU F n t u) (un : u≤n) :
    raw n (opposite F n) = raw n F := by
  have c := opp_score V
  rw [score_raw V,score_raw (opp_valid V un)] at c
  exact (div_left_inj' (by positivity)).mp c

theorem sharp_slack_two (t u : Nat) (large : 2≤max t u) :
    ∃ H : Family, IsIU H (t+u+2) t u ∧
      ∀ F : Family, IsIU F (t+u+2) t u → raw (t+u+2) F≤raw (t+u+2) H := by
  by_cases le : t≤u
  · exact ⟨star t u,(slack_two_exact_raw t u le (by omega)).1,
      (slack_two_exact_raw t u le (by omega)).2⟩
  · have z := slack_two_exact_raw u t (by omega) (by omega)
    rw [show u+t+2=t+u+2 by omega] at z
    refine ⟨opposite (star u t) (t+u+2),opp_valid z.1 (by omega),?_⟩
    intro F vf
    have c := z.2 (opposite F (t+u+2)) (opp_valid vf (by omega))
    rw [opp_raw vf (by omega)] at c
    rwa [opp_raw z.1 (by omega)]

#print axioms proposed_optimal_iff_short
#print axioms slack_two_exact_raw
#print axioms sharp_slack_two
end IU.Lubell
