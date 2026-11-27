import LubellSlackThreeCounts
import LubellCompare

namespace IU.Lubell
open Finset
open scoped BigOperators

def base3 (t u : Nat) : ℚ :=
  (t.factorial:ℚ)*(u.factorial:ℚ) / ((t+u+3+1).factorial:ℚ)

def scoreLo3 (t u : Nat) : ℚ :=
  weight (t+u+3) t + ((u:ℚ)+3)*weight (t+u+3) (t+1) +
    ((u:ℚ)+2)*weight (t+u+3) (t+2)
def scoreHi3 (t u : Nat) : ℚ :=
  ((t:ℚ)+2)*weight (t+u+3) (t+1) + ((t:ℚ)+3)*weight (t+u+3) (t+2) +
    weight (t+u+3) (t+3)
def scoreCyl3 (t u : Nat) : ℚ :=
  weight (t+u+3) t + 3*weight (t+u+3) (t+1) +
    3*weight (t+u+3) (t+2) + weight (t+u+3) (t+3)

private theorem weight0 (t u : Nat) :
    weight (t+u+3) t=base3 t u*((u:ℚ)+1)*((u:ℚ)+2)*((u:ℚ)+3) := by
  unfold weight base3
  rw [show t+u+3-t=u+3 by omega, Nat.factorial_succ (u+2),Nat.factorial_succ (u+1),Nat.factorial_succ u]
  push_cast
  ring

private theorem weight1 (t u : Nat) :
    weight (t+u+3) (t+1)=base3 t u*((t:ℚ)+1)*((u:ℚ)+1)*((u:ℚ)+2) := by
  unfold weight base3
  rw [show t+u+3-(t+1)=u+2 by omega, Nat.factorial_succ (u+1),Nat.factorial_succ u,Nat.factorial_succ t]
  push_cast
  ring

private theorem weight2 (t u : Nat) :
    weight (t+u+3) (t+2)=base3 t u*((t:ℚ)+1)*((t:ℚ)+2)*((u:ℚ)+1) := by
  unfold weight base3
  rw [show t+u+3-(t+2)=u+1 by omega, Nat.factorial_succ (t+1),Nat.factorial_succ t,Nat.factorial_succ u]
  push_cast
  ring

private theorem weight3 (t u : Nat) :
    weight (t+u+3) (t+3)=base3 t u*((t:ℚ)+1)*((t:ℚ)+2)*((t:ℚ)+3) := by
  unfold weight base3
  rw [show t+u+3-(t+3)=u by omega, Nat.factorial_succ (t+2),Nat.factorial_succ (t+1),Nat.factorial_succ t]
  push_cast
  ring

theorem score_lo_factor (t u : Nat) :
  scoreLo3 t u=base3 t u*((t:ℚ)+2)*((u:ℚ)+1)*((u:ℚ)+2)*((t:ℚ)+(u:ℚ)+4) := by
  unfold scoreLo3
  rw [weight0,weight1,weight2]
  ring

theorem score_hi_factor (t u : Nat) :
  scoreHi3 t u=base3 t u*((t:ℚ)+1)*((t:ℚ)+2)*((u:ℚ)+2)*((t:ℚ)+(u:ℚ)+4) := by
  unfold scoreHi3
  rw [weight1,weight2,weight3]
  ring

theorem score_cyl_factor (t u : Nat) :
  scoreCyl3 t u=base3 t u*((t:ℚ)+(u:ℚ)+2)*((t:ℚ)+(u:ℚ)+3)*((t:ℚ)+(u:ℚ)+4) := by
  unfold scoreCyl3
  rw [weight0,weight1,weight2,weight3]
  ring

private theorem pos_base (t u : Nat) : 0<base3 t u := by
  unfold base3
  positivity

theorem score_hi_le_lo {t u : Nat} (h : t≤u) : scoreHi3 t u≤scoreLo3 t u := by
  rw [score_lo_factor,score_hi_factor]
  have h' : ((t:ℚ)+1)≤((u:ℚ)+1) := by
    have hz : (t:ℚ)≤(u:ℚ) := by exact_mod_cast h
    linarith
  have hb := pos_base t u
  have H := mul_le_mul_of_nonneg_left h' (by
      apply le_of_lt (pos_base t u))
  calc
    _ = (base3 t u*((t:ℚ)+1))*(((t:ℚ)+2)*((u:ℚ)+2)*((t:ℚ)+(u:ℚ)+4)) := by ring
    _ ≤ (base3 t u*((u:ℚ)+1))*(((t:ℚ)+2)*((u:ℚ)+2)*((t:ℚ)+(u:ℚ)+4)) :=
      mul_le_mul_of_nonneg_right H (by positivity)
    _ = _ := by ring

theorem score_cyl_lt_lo {t u : Nat} (ht : 1≤t) (le : t≤u) (hu : 2≤u) :
    scoreCyl3 t u<scoreLo3 t u := by
  rw [score_lo_factor,score_cyl_factor]
  have z := LubellSlackThree.low_gt_cylinder ((t:ℤ)+1) ((u:ℤ)+1)
    (by omega) (by omega) (by omega)
  have z' : (((t:ℚ)+1)+((u:ℚ)+1))*(((t:ℚ)+1)+((u:ℚ)+1)+1) <
      (((t:ℚ)+1)+1)*((u:ℚ)+1)*(((u:ℚ)+1)+1) := by exact_mod_cast z
  have pp1 : 0<base3 t u := pos_base t u
  have pp : 0<base3 t u*((t:ℚ)+(u:ℚ)+4) := by positivity
  calc
    _ = (base3 t u*((t:ℚ)+(u:ℚ)+4)) *
       ((((t:ℚ)+1)+((u:ℚ)+1))*(((t:ℚ)+1)+((u:ℚ)+1)+1)) := by ring
    _ < (base3 t u*((t:ℚ)+(u:ℚ)+4)) * ((((t:ℚ)+1)+1)*((u:ℚ)+1)*(((u:ℚ)+1)+1)) :=
      mul_lt_mul_of_pos_left z' pp
    _ = _ := by ring

theorem expand_score_three {F : Family} {t u : Nat} (V : IsIU F (t+u+3) t u) :
    score (t+u+3) F = ((layer F t).card : ℚ)*weight (t+u+3) t +
      ((layer F (t+1)).card : ℚ)*weight (t+u+3) (t+1) +
      ((layer F (t+2)).card : ℚ)*weight (t+u+3) (t+2) +
      ((layer F (t+3)).card : ℚ)*weight (t+u+3) (t+3) := by
  classical
  have eq : F=layer F t ∪ layer F (t+1) ∪ layer F (t+2) ∪ layer F (t+3) := by
    ext A
    simp only [layer,Finset.mem_union,Finset.mem_filter]
    constructor
    · intro a
      have K := V.2 A a A a
      simp only [Finset.inter_self,Finset.union_self] at K
      rcases (show A.card=t ∨ A.card=t+1 ∨ A.card=t+2 ∨ A.card=t+3 by omega) with b|b|b|b
      · exact Or.inl (Or.inl (Or.inl ⟨a,b⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨a,b⟩))
      · exact Or.inl (Or.inr ⟨a,b⟩)
      · exact Or.inr ⟨a,b⟩
    · rintro (((⟨a,_⟩|⟨a,_⟩)|⟨a,_⟩)|⟨a,_⟩) <;> exact a
  have dis (k j : Nat) (h : k≠j) : Disjoint (layer F k) (layer F j) :=
    Finset.disjoint_left.mpr (fun A ak aj => h ((from_layer ak).2.symm.trans (from_layer aj).2))
  have ul := dis t (t+1) (by omega)
  have ur : Disjoint (layer F t ∪ layer F (t+1)) (layer F (t+2)) :=
    Finset.disjoint_left.mpr (by
      intro A a b
      have f := (from_layer b).2
      rcases Finset.mem_union.mp a with p|p <;> have e := (from_layer p).2 <;> omega)
  have ur2 : Disjoint (layer F t ∪ layer F (t+1) ∪ layer F (t+2)) (layer F (t+3)) :=
    Finset.disjoint_left.mpr (by
      intro A a b
      have f := (from_layer b).2
      rcases Finset.mem_union.mp a with a'|p
      · rcases Finset.mem_union.mp a' with p|p <;> have e := (from_layer p).2 <;> omega
      · have e := (from_layer p).2; omega)
  have layerSum (k : Nat) :
      (∑ A∈layer F k, weight (t+u+3) A.card) =
        ((layer F k).card : ℚ)*weight (t+u+3) k := by
    rw [←nsmul_eq_mul,←Finset.sum_const]
    exact Finset.sum_congr rfl (fun A h => by rw [(from_layer h).2])
  unfold score
  conv_lhs => rw [eq]
  rw [Finset.sum_union ur2,Finset.sum_union ur,Finset.sum_union ul,layerSum,layerSum,layerSum,layerSum]

theorem slack_three_upper {F : Family} {t u : Nat} (ht : 1≤t) (le : t≤u) (hu : 2≤u)
    (h : IsIU F (t+u+3) t u) : score (t+u+3) F≤scoreLo3 t u := by
  have pos (k : Nat) : 0≤weight (t+u+3) k := by unfold weight; positivity
  have mult {a b k : Nat} (hle : a≤b) :
      (a:ℚ)*weight (t+u+3) k ≤ (b:ℚ)*weight (t+u+3) k :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (pos k)
  rw [expand_score_three h]
  rcases slack_three_count_cases ht le h with ⟨a,b,c,d⟩|⟨a,b,c,d⟩|⟨a,b,c,d⟩
  · have a' := mult (k:=t) a
    have b' := mult (k:=t+1) b
    have c' := mult (k:=t+2) c
    have d' := mult (k:=t+3) d
    have E := score_cyl_lt_lo ht le hu
    unfold scoreCyl3 at E
    push_cast at a' b' c' d'
    linarith
  · have a' := mult (k:=t) a
    have b' := mult (k:=t+1) b
    have c' := mult (k:=t+2) c
    rw [d]
    unfold scoreLo3
    push_cast at a' b' c' ⊢
    linarith
  · have b' := mult (k:=t+1) b
    have c' := mult (k:=t+2) c
    have d' := mult (k:=t+3) d
    have E := score_hi_le_lo le
    rw [a]
    unfold scoreHi3 at E
    push_cast at b' c' d' ⊢
    linarith

#print axioms slack_three_upper
end IU.Lubell
