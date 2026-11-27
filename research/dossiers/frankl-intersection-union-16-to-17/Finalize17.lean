import Rows17Sound
import Exact11
import AnchorBlocks17

namespace IU.IU17
open IU.Eliminate
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def outer (a : Nat) : Prop := rank a 8 ≤ 4 ∨ 4 ≤ rank a 17 - rank a 9

def pivot17 (k : Nat) : Nat :=
  match k with
  | 2 => 3
  | 3 => 7
  | 4 => 15
  | 5 => 271
  | 6 => 783
  | 7 => 1807
  | 8 => 3855
  | 9 => 7711
  | 10 => 7743
  | 11 => 7807
  | 12 => 7935
  | 13 => 8191
  | 14 => 16383
  | 15 => 32767
  | _ => 0

def PivotOK (k : Nat) : Prop :=
    rank (pivot17 k) 17 = k ∧
    (∀ t ∈ List.range 18, rank (pivot17 k) t =
      if k≤8 then envelope k 8 4 t else envelope k 9 (k-4) t) ∧
    (∃ s∈List.range 3, ∃ r∈bank s k, r.a=pivot17 k)

instance (k : Nat) : Decidable (PivotOK k) := by unfold PivotOK; infer_instance

theorem pivot_facts (k : Nat) (lo : 2≤k) (hi : k≤15) : PivotOK k := by
  have h : ∀ j : Fin 16, 2≤j.val → PivotOK j.val := by
    intro j
    fin_cases j
    · intro e; change 2≤0 at e; omega
    · intro e; change 2≤1 at e; omega
    all_goals intro _; decide +kernel
  exact h ⟨k,by omega⟩ lo

theorem outsider_drops {a : Nat} (alo : 2≤rank a 17) (ahi : rank a 17≤15)
    (o : outer a) : coarse a<3 := by
  let k := rank a 17
  obtain ⟨kn,P,s,sl,r,rm,rr⟩ := pivot_facts k alo ahi
  have cap := (outsider_cap (n:=17) (a:=a) (l:=4) (r:=4) (k:=k) rfl (by decide)).mp o
  have D : Dominates 17 (pivot17 k) a := by
    by_cases s : k≤8
    · exact cap_domination rfl (by simpa [s] using cap) kn (fun j jm => by simpa [s] using P j jm)
    · exact cap_domination rfl (by simpa [s] using cap) kn (fun j jm => by simpa [s] using P j jm)
  exact has_stage ⟨s,List.mem_range.mp sl,r,rm,by simpa [rr] using D⟩

theorem prefix_cap17 (F : Finset Nat)
    (v : ∀ a∈F, a∈admissible 17 2 2)
    (edgeF : ∀ a∈F, ∀ b∈F, a≠b → edge 17 2 2 a b=true) : F.card≤17298 := by
  apply clique_cap_of_elimination (n:=17) (p:=2) (q:=2) (m:=17298) (r:=6) colors fine F
  · intro i; exact root.at_good rootGood i.val
  · intro a ha
    obtain ⟨i,hi,h⟩ := root.mask_cover rootValid (paint_cover (v a ha))
    exact ⟨⟨i,hi⟩,h⟩
  · exact edgeF
  · intro a _ small
    exact miss_of_stage full_rows (outside_stage_of_phased small)
  · refine ⟨IU17Anchor.anchorFamily,by rw [IU17Anchor.anchor_size],?_⟩
    intro a ha high
    obtain ⟨l,hv⟩ := List.mem_filter.mp (v a ha)
    have bound : a<131072 := List.mem_range.mp l
    have w := of_decide_eq_true ((Bool.and_eq_true_iff.mp hv).1)
    have c : ¬ outer a := by
      intro O
      have S := outsider_drops w.1 w.2 O
      change outsideStage 17 3 bank a < 3 at S
      change 6 ≤ phased 17 3 bank a at high
      unfold phased at high
      split at high <;> omega
    unfold outer at c
    exact IU17Anchor.into_anchor bound (by omega) (by omega)

theorem upper17 (F : Sys) (ok : IsIU F 17 2 2) : F.card≤17298 := cap_of_prefix ok prefix_cap17
theorem upper16 (F : Sys) (ok : IsIU F 16 2 2) : F.card≤8649 :=
  upper_with_free (by decide) F ok upper17
theorem exact16 : Exact 16 8649 :=
  ⟨upper16,attained (l:=8) (r:=8) (by decide) (by decide) (by decide) IU17Anchor.product_len16⟩
theorem exact17 : Exact 17 17298 :=
  ⟨upper17,attained (l:=8) (r:=8) (by decide) (by decide) (by decide) IU17Anchor.product_len17⟩

#print axioms exact16
#print axioms exact17
end IU.IU17
