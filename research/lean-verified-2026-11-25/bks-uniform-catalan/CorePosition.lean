import ToPack
import CoreBallot
import Mathlib.Order.Hom.Set

namespace FussCover
open Finset

variable {z h j : ℕ} (hj : 0<j) (hz : 0<z)
variable (r : Equiv.Perm (Fin (n z h j))) (P : packed r)

def aI (i : Fin j) : Fin (j+1) := i.rev.castSucc
def bI (i : Fin j) : Fin (j+1) := i.rev.succ

lemma allA (t : Fin (j+1)) : t=Fin.last j ∨ ∃ i : Fin j, t=aI i := by
  by_cases e : t.val=j
  · exact Or.inl (Fin.ext e)
  · let s : Fin j := ⟨t.val,by have := t.isLt; omega⟩
    exact Or.inr ⟨s.rev,by simp [aI]; exact Fin.ext rfl⟩

lemma allB (t : Fin (j+1)) : t=0 ∨ ∃ i : Fin j, t=bI i := by
  by_cases e : t.val=0
  · exact Or.inl (Fin.ext e)
  · let s : Fin j := ⟨t.val-1,by have := t.isLt; omega⟩
    refine Or.inr ⟨s.rev,?_⟩
    apply Fin.ext
    simp only [bI,Fin.rev_rev,Fin.val_succ]
    change t.val=t.val-1+1
    omega

lemma aI_lt (i : Fin j) : aI i < Fin.last j := i.rev.isLt
lemma bI_pos (i : Fin j) : 0 < bI i := by change 0 < i.rev.val + 1; omega

lemma aI_anti : StrictAnti (@aI j) := by
  intro a b h
  exact Fin.castSucc_lt_castSucc_iff.mpr (Fin.rev_lt_rev.mpr h)
lemma bI_anti : StrictAnti (@bI j) := by
  intro a b h
  exact Fin.succ_lt_succ_iff.mpr (Fin.rev_lt_rev.mpr h)

def prefixV (i : Fin (hN z h j+1)) : Fin (n z h j) :=
    if hv : i.val<hN z h j then hAt hj hz ⟨i.val,hv⟩ else A hj (Fin.last j)

include P
lemma prefix_mono : StrictMono (fun i => r (prefixV hj hz i)) := by
  intro a b e
  change a.val < b.val at e
  have t := b.isLt
  unfold prefixV
  dsimp only
  split_ifs with h₁ h₂ h₂
  · exact packed_head_mono hj hz r P (show (⟨a.val,h₁⟩ : Fin (hN z h j)) < ⟨b.val,h₂⟩ from e)
  · exact packed_H_before_A hj hz r P _ _
  · omega
  · omega

def prefRanks : Finset (Fin (n z h j)) :=
    univ.image (fun i => r (prefixV hj hz i))

omit P in
lemma in_pref {x : Fin (n z h j)} :
    x ∈ prefRanks hj hz r ↔ ∃ i : Fin (hN z h j+1), r (prefixV hj hz i)=x := by
  simp only [prefRanks,mem_image,mem_univ,true_and]

lemma pref_card : (prefRanks hj hz r).card=hN z h j+1 := by
  unfold prefRanks
  rw [card_image_of_injective _ (prefix_mono hj hz r P).injective]
  exact Fintype.card_fin _

lemma core_a_above_prefix (i : Fin (hN z h j+1)) (t : Fin j) :
    r (prefixV hj hz i) < r (A hj (aI t)) := by
  unfold prefixV
  split_ifs
  · exact packed_H_before_A hj hz r P _ _
  · exact (packed_A_anti hj r P) (aI_lt t)

lemma core_B_above_prefix (i : Fin (hN z h j+1)) (t : Fin (j+1)) :
    r (prefixV hj hz i) < r (B hj t) := by
  unfold prefixV
  split_ifs
  · exact packed_H_before_B hj hz r P _ _
  · exact packed_Amin_before_B hj r P _

lemma pref_lt_outside {x y : Fin (n z h j)} (hx : x ∈ prefRanks hj hz r)
    (hy : y ∉ prefRanks hj hz r) : x<y := by
  obtain ⟨i,hi⟩ := (in_pref hj hz r).mp hx
  rw [←hi]
  let e := posEquiv (z:=z) (h:=h) hj hz
  obtain ⟨v,hv⟩ := e.surjective (r.symm y)
  have Y : r (e v)=y := by rw [hv,r.apply_symm_apply]
  cases v with
  | inl u =>
    have E : r (prefixV hj hz ⟨u.val,by have := u.isLt; omega⟩)=y := by
      have H : prefixV hj hz ⟨u.val,by have := u.isLt; omega⟩=hAt hj hz u := by
        unfold prefixV
        simp only [dite_eq_left u.isLt]
      rw [H]; exact Y
    exact (hy ((in_pref hj hz r).mpr ⟨_,E⟩)).elim
  | inr AB =>
    cases AB with
    | inl t =>
      have V : r (A hj t)=y := Y
      rcases allA t with ee|⟨s,es⟩
      · have E : r (prefixV hj hz ⟨hN z h j,by omega⟩)=y := by
          unfold prefixV
          simp only [dite_eq_right (Nat.lt_irrefl _)]
          rw [←ee]
          exact V
        exact (hy ((in_pref hj hz r).mpr ⟨_,E⟩)).elim
      · rw [←V,es]; exact core_a_above_prefix hj hz r P i s
    | inr t =>
      have V : r (B hj t)=y := Y
      rw [←V]; exact core_B_above_prefix hj hz r P i t

lemma pref_exact {x : Fin (n z h j)} :
    x ∈ prefRanks hj hz r ↔ x.val<hN z h j+1 := by
  classical
  have d (a b : Fin (n z h j)) (l : b≤a) (ha : a∈prefRanks hj hz r) : b∈prefRanks hj hz r := by
    by_contra hn
    exact (not_lt_of_ge l) (pref_lt_outside hj hz r P ha hn)
  have h := @Fin.lt_card_filter_univ_iff_apply_of_imp _ x (fun t => t∈prefRanks hj hz r) _ d
  have f : univ.filter (fun t => t∈prefRanks hj hz r) = prefRanks hj hz r := by ext; simp
  rw [f,pref_card hj hz r P] at h
  exact h.symm

lemma prefix_value (i : Fin (hN z h j+1)) :
    (r (prefixV hj hz i)).val=i.val := by
  have le : hN z h j+1 ≤ n z h j := by rw [n_eq_head_core hj]; omega
  let E : Fin (hN z h j+1)→Fin (n z h j) := Fin.castLE le
  have eq : Set.range (fun i => r (prefixV hj hz i))=Set.range E := by
    ext x
    constructor
    · rintro ⟨a,ha⟩
      have lx := (pref_exact hj hz r P).mp ((in_pref hj hz r).mpr ⟨a,ha⟩)
      exact ⟨⟨x.val,lx⟩,Fin.ext rfl⟩
    · rintro ⟨a,ha⟩
      have hv : x.val = a.val := (congrArg Fin.val ha).symm
      exact (in_pref hj hz r).mp ((pref_exact hj hz r P).mpr (by rw [hv]; exact a.isLt))
  have m : StrictMono E := fun a b h => h
  have hh := (prefix_mono hj hz r P).eq_of_range_eq m eq
  exact congrArg Fin.val (congrFun hh i)

lemma head_rank (i : Fin (hN z h j)) : (r (hAt hj hz i)).val=i.val := by
  have e := prefix_value hj hz r P (⟨i.val,by have := i.isLt; omega⟩ : Fin (hN z h j+1))
  unfold prefixV at e
  simpa only [Fin.val_mk,dite_eq_left i.isLt] using e

include hz in
lemma A_last_rank : (r (A hj (Fin.last j))).val=hN z h j := by
  have e := prefix_value hj hz r P (⟨hN z h j,by omega⟩ : Fin (hN z h j+1))
  unfold prefixV at e
  simpa only [dite_eq_right (Nat.lt_irrefl _)] using e

include hz in
lemma B_first_rank : (r (B hj 0)).val=hN z h j+2*j+1 := by
  have e := n_eq_head_core (z:=z) (h:=h) hj
  have rle : (r (B hj 0)).val ≤ hN z h j+2*j+1 := by have := (r (B hj 0)).isLt; omega
  let max : Fin (n z h j) := ⟨hN z h j+2*j+1,by omega⟩
  let E := posEquiv (z:=z) (h:=h) hj hz
  obtain ⟨v,hv⟩ := E.surjective (r.symm max)
  have Y : r (E v)=max := by rw [hv,r.apply_symm_apply]
  cases v with
  | inl u =>
    have Y' : r (hAt hj hz u)=max := Y
    have k := packed_H_before_B hj hz r P u 0
    rw [Y'] at k
    exact (not_lt_of_ge rle k).elim
  | inr l =>
    cases l with
    | inl t =>
      have Y' : r (A hj t)=max := Y
      have k := packed_A_before_Bmax hj r P t
      rw [Y'] at k
      exact (not_lt_of_ge rle k).elim
    | inr t =>
      have Y' : r (B hj t)=max := Y
      by_cases h : t=(0 : Fin (j+1))
      · subst t; exact congrArg Fin.val Y'
      · have ht : (0 : Fin (j+1)) < t := lt_of_le_of_ne (Fin.zero_le _) (Ne.symm h)
        have k := (packed_B_anti hj r P) ht
        change r (B hj t)<r (B hj 0) at k
        rw [Y'] at k
        exact (not_lt_of_ge rle k).elim

end FussCover
