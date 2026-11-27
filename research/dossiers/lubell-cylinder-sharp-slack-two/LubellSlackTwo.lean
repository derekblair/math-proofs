import LubellJohnson
import LubellSymmetry

namespace IU.Lubell
open scoped BigOperators

def layer (F : Family) (k : Nat) : Family := F.filter (fun A => A.card=k)

theorem from_layer {F : Family} {k : Nat} {A : Finset Nat} (h : A∈layer F k) :
    A∈F ∧ A.card=k :=
  Finset.mem_filter.mp h

theorem middle_counts {F : Family} {t u : Nat} (le : t≤u)
    (V : IsIU F (t+u+2) t u) :
    let L := (layer F t).card
    let M := (layer F (t+1)).card
    let H := (layer F (t+2)).card
    (L≤1 ∧ M≤2 ∧ H≤1) ∨ (L≤1 ∧ M≤u+2 ∧ H=0) ∨ (L=0 ∧ M≤t+2 ∧ H≤1) := by
  dsimp
  have down {T A : Finset Nat} (T0 : T∈layer F t) (a : A∈F) : T⊆A := by
    have tc := from_layer T0
    have P := V.2 T tc.1 A a
    have e := Finset.eq_of_subset_of_card_le (show T∩A ⊆ T from Finset.inter_subset_left) (by omega)
    exact e ▸ Finset.inter_subset_right
  have up {U A : Finset Nat} (U0 : U∈layer F (t+2)) (a : A∈F) : A⊆U := by
    have uc := from_layer U0
    have P := V.2 A a U uc.1
    have e := Finset.eq_of_subset_of_card_le (show U ⊆ A∪U from Finset.subset_union_right) (by omega)
    exact e.symm ▸ Finset.subset_union_left
  have lc : (layer F t).card≤1 := Finset.card_le_one.mpr (fun a A b B =>
    Finset.Subset.antisymm (down A (from_layer B).1) (down B (from_layer A).1))
  have hc : (layer F (t+2)).card≤1 := Finset.card_le_one.mpr (fun a A b B =>
    Finset.Subset.antisymm (up B (from_layer A).1) (up A (from_layer B).1))
  let Q := layer F (t+1)
  have size (A : Finset Nat) (a : A∈Q) : A.card=t+1 := (from_layer a).2
  by_cases bl : (layer F t).Nonempty
  · obtain ⟨T,tF⟩ := bl
    by_cases bh : (layer F (t+2)).Nonempty
    · obtain ⟨U,uF⟩ := bh
      have s := down tF (from_layer uF).1
      have b := count_above (T:=T) (U:=U) (F:=Q) (from_layer tF).2 size
        (fun A a => down tF (from_layer a).1) (fun A a => up uF (from_layer a).1)
      rw [Finset.card_sdiff_of_subset s,(from_layer uF).2,(from_layer tF).2] at b
      exact Or.inl ⟨lc,by simpa [Q] using b,hc⟩
    · have high0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp bh)
      have b := count_above (T:=T) (U:=Finset.range (t+u+2)) (F:=Q) (from_layer tF).2 size
        (fun A a => down tF (from_layer a).1) (fun A a => V.1 A (from_layer a).1)
      rw [Finset.card_sdiff_of_subset (V.1 T (from_layer tF).1),Finset.card_range,(from_layer tF).2] at b
      exact Or.inr (Or.inl ⟨lc,by simpa [Q,show t+u+2-t=u+2 by omega] using b,high0⟩)
  · have low0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp bl)
    by_cases bh : (layer F (t+2)).Nonempty
    · obtain ⟨U,uF⟩ := bh
      have b := count_below (U:=U) (F:=Q) (from_layer uF).2 size
        (fun A a => up uF (from_layer a).1)
      exact Or.inr (Or.inr ⟨low0,b,hc⟩)
    · have high0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp bh)
      have b : Q.card≤u+2 := by
        by_cases big : 1<Q.card
        · rcases johnson_star_top size
            (fun A a B b => (V.2 A (from_layer a).1 B (from_layer b).1).1) big with
             ⟨T,tc,st⟩|⟨U,uc,uS⟩
          · obtain ⟨A,aF⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
            have tR := (st A aF).trans (V.1 A (from_layer aF).1)
            have N := count_above (T:=T) (U:=Finset.range (t+u+2)) tc size st
              (fun A a => V.1 A (from_layer a).1)
            rwa [Finset.card_sdiff_of_subset tR,Finset.card_range,tc,show t+u+2-t=u+2 by omega] at N
          · exact (count_below uc size uS).trans (by omega)
        · omega
      exact Or.inr (Or.inl ⟨lc,b,high0⟩)

theorem expand_score {F : Family} {t u : Nat} (V : IsIU F (t+u+2) t u) :
    score (t+u+2) F = ((layer F t).card : ℚ)*weight (t+u+2) t +
      ((layer F (t+1)).card : ℚ)*weight (t+u+2) (t+1) +
      ((layer F (t+2)).card : ℚ)*weight (t+u+2) (t+2) := by
  classical
  have eq : F=layer F t ∪ layer F (t+1) ∪ layer F (t+2) := by
    ext A
    simp only [layer,Finset.mem_union,Finset.mem_filter]
    constructor
    · intro a
      have K := V.2 A a A a
      simp only [Finset.inter_self,Finset.union_self] at K
      rcases (show A.card=t ∨ A.card=t+1 ∨ A.card=t+2 by omega) with b|b|b
      · exact Or.inl (Or.inl ⟨a,b⟩)
      · exact Or.inl (Or.inr ⟨a,b⟩)
      · exact Or.inr ⟨a,b⟩
    · rintro ((⟨a,_⟩|⟨a,_⟩)|⟨a,_⟩) <;> exact a
  have ul : Disjoint (layer F t) (layer F (t+1)) := Finset.disjoint_left.mpr (by
    intro A a b
    have e := (from_layer a).2
    have f := (from_layer b).2
    omega)
  have ur : Disjoint (layer F t ∪ layer F (t+1)) (layer F (t+2)) := Finset.disjoint_left.mpr (by
    intro A a b
    have f := (from_layer b).2
    rcases Finset.mem_union.mp a with p|p <;>
      have e := (from_layer p).2 <;> omega)
  have layerSum (k : Nat) :
      (∑ A∈layer F k, weight (t+u+2) A.card) =
        ((layer F k).card : ℚ)*weight (t+u+2) k := by
    rw [←nsmul_eq_mul,←Finset.sum_const]
    exact Finset.sum_congr rfl (fun A h => by rw [(from_layer h).2])
  unfold score
  conv_lhs => rw [eq]
  rw [Finset.sum_union ur,Finset.sum_union ul,layerSum,layerSum,layerSum]

theorem layer_order (t u : Nat) (le : t≤u) :
    weight (t+u+2) (t+2) ≤ weight (t+u+2) t := by
  unfold weight
  rw [show t+u+2-(t+2)=u by omega,show t+u+2-t=u+2 by omega]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Nat.factorial_succ (t+1),Nat.factorial_succ t,
    Nat.factorial_succ (u+1),Nat.factorial_succ u]
  push_cast
  have H : ((t:ℚ)+2)*((t:ℚ)+1) ≤ ((u:ℚ)+2)*((u:ℚ)+1) := by
    have L : (t:ℚ)≤(u:ℚ) := by exact_mod_cast le
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  calc
    ((t:ℚ)+1+1)*(((t:ℚ)+1)*(t.factorial:ℚ))*(u.factorial:ℚ)
       = ((t:ℚ)+2)*((t:ℚ)+1)*((t.factorial:ℚ)*(u.factorial:ℚ)) := by ring
    _ ≤ ((u:ℚ)+2)*((u:ℚ)+1)*((t.factorial:ℚ)*(u.factorial:ℚ)) :=
      mul_le_mul_of_nonneg_right H (by positivity)
    _ = (t.factorial:ℚ)*(((u:ℚ)+1+1)*(((u:ℚ)+1)*(u.factorial:ℚ))) := by ring

theorem slack_two_upper {F : Family} {t u : Nat} (le : t≤u) (big : 2≤u)
    (h : IsIU F (t+u+2) t u) : score (t+u+2) F ≤ score (t+u+2) (star t u) := by
  have pos (k : Nat) : 0≤weight (t+u+2) k := by unfold weight; positivity
  have mult {a b k : Nat} (h : a≤b) :
      (a:ℚ)*weight (t+u+2) k ≤ (b:ℚ)*weight (t+u+2) k :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h) (pos k)
  have beat := star_beats t u le big
  rw [cylinder_at_slack_two,star_score] at beat
  rw [expand_score h,star_score]
  rcases middle_counts le h with ⟨A,B,C⟩ | ⟨A,B,C⟩ | ⟨A,B,C⟩
  · have l := mult (k:=t) A
    have m := mult (k:=t+1) B
    have r := mult (k:=t+2) C
    simp only [Nat.cast_one,Nat.cast_ofNat,one_mul] at l m r
    linarith
  · have l := mult (k:=t) A
    have m := mult (k:=t+1) B
    rw [C]
    push_cast at l m ⊢
    linarith
  · have m := mult (k:=t+1) (B.trans (show t+2≤u+2 by omega))
    have r := mult (k:=t+2) C
    have O := layer_order t u le
    rw [A]
    push_cast at m r ⊢
    linarith

theorem slack_two_exact (t u : Nat) (le : t≤u) (big : 2≤u) :
    IsIU (star t u) (t+u+2) t u ∧
      ∀ F : Family, IsIU F (t+u+2) t u → score (t+u+2) F≤score (t+u+2) (star t u) :=
  ⟨star_valid t u,fun _ => slack_two_upper le big⟩

#print axioms slack_two_exact
end IU.Lubell
