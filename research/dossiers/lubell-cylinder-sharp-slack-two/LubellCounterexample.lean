import LubellWeights

namespace IU.Lubell
open Nat
open scoped BigOperators

abbrev Family := Finset (Finset Nat)

def cylinder (t u : Nat) : Nat → Family
  | 0 => {Finset.range t}
  | d+1 => double (cylinder t u d) (t+u+d)

theorem cylinder_valid (t u d : Nat) : IsIU (cylinder t u d) (t+u+d) t u := by
  induction d with
  | zero =>
    refine ⟨?_,?_⟩
    · intro A hA i hi
      have eq : A=Finset.range t := by simpa [cylinder] using hA
      rw [eq] at hi
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)
    · intro A hA B hB
      have a : A=Finset.range t := by simpa [cylinder] using hA
      have b : B=Finset.range t := by simpa [cylinder] using hB
      rw [a,b,Finset.inter_self,Finset.union_self,Finset.card_range]
      omega
  | succ d ih =>
    exact (lift_double _ ih (by omega)).1

theorem cylinder_score (t u d : Nat) :
    score (t+u+d) (cylinder t u d)=weight (t+u) t := by
  induction d with
  | zero => simp [cylinder,score]
  | succ d ih =>
    exact (score_extend (cylinder_valid t u d)).trans ih

def star (t u : Nat) : Family :=
  insert (Finset.range t) ((Finset.range (u+2)).image (fun j => insert (t+j) (Finset.range t)))

theorem star_shape {t u : Nat} {A : Finset Nat} (h : A∈star t u) :
    ∃ X : Finset Nat, X⊆Finset.range (t+u+2) ∧ X.card≤1 ∧ A=Finset.range t∪X := by
  rcases Finset.mem_insert.mp h with e|h'
  · exact ⟨∅,Finset.empty_subset _,by simp,by simpa⟩
  · obtain ⟨j,jb,rfl⟩ := Finset.mem_image.mp h'
    have hi := Finset.mem_range.mp jb
    refine ⟨{t+j},?_,by simp,?_⟩
    · exact Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr (by omega))
    · simp [Finset.union_singleton]

theorem star_valid (t u : Nat) : IsIU (star t u) (t+u+2) t u := by
  have T : Finset.range t⊆Finset.range (t+u+2) :=
    fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
  refine ⟨?_,?_⟩
  · intro A ha
    obtain ⟨X,xN,_,rfl⟩ := star_shape ha
    exact Finset.union_subset T xN
  · intro A ha B hb
    obtain ⟨X,_,xc,rfl⟩ := star_shape ha
    obtain ⟨Y,_,yc,rfl⟩ := star_shape hb
    have it := Finset.card_le_card (show Finset.range t⊆(Finset.range t∪X)∩(Finset.range t∪Y) from
      fun a ha => Finset.mem_inter.mpr ⟨Finset.mem_union_left _ ha,Finset.mem_union_left _ ha⟩)
    rw [Finset.card_range] at it
    have eq : (Finset.range t∪X) ∪ (Finset.range t∪Y)=Finset.range t∪(X∪Y) := by
      ext a
      simp only [Finset.mem_union]
      tauto
    rw [eq]
    have H := Finset.card_union_le (Finset.range t) (X∪Y)
    rw [Finset.card_range] at H
    have J := Finset.card_union_le X Y
    exact ⟨it,by omega⟩

theorem star_score (t u : Nat) :
    score (t+u+2) (star t u) = weight (t+u+2) t + (u+2 : ℚ) * weight (t+u+2) (t+1) := by
  classical
  have notin (j : Nat) : t+j∉Finset.range t :=
    fun H => (show ¬t+j<t by omega) (Finset.mem_range.mp H)
  have no : Finset.range t ∉ (Finset.range (u+2)).image (fun j => insert (t+j) (Finset.range t)) := by
    intro z
    obtain ⟨j,h,eq⟩ := Finset.mem_image.mp z
    exact notin j (eq ▸ Finset.mem_insert_self _ _)
  have inj : Set.InjOn (fun j => insert (t+j) (Finset.range t)) (↑(Finset.range (u+2)) : Set Nat) := by
    intro a _ b _ eq
    change insert (t+a) (Finset.range t) = insert (t+b) (Finset.range t) at eq
    have h : t+a ∈ insert (t+b) (Finset.range t) := eq ▸ Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp h with e|H
    · omega
    · exact False.elim (notin a H)
  unfold star score
  rw [Finset.sum_insert no,Finset.card_range,Finset.sum_image inj]
  simp only [Finset.card_insert_of_notMem (notin _),Finset.card_range,Finset.sum_const,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]

theorem cylinder_at_slack_two (t u : Nat) :
    weight (t+u) t = weight (t+u+2) t + 2 * weight (t+u+2) (t+1) + weight (t+u+2) (t+2) := by
  have a := weight_extend (n:=t+u) (k:=t) (by omega)
  have b := weight_extend (n:=t+u+1) (k:=t) (by omega)
  have c := weight_extend (n:=t+u+1) (k:=t+1) (by omega)
  linarith

theorem weight_difference (t u : Nat) :
    (u:ℚ) * weight (t+u+2) (t+1) - weight (t+u+2) (t+2) =
       ((t+1).factorial : ℚ) * (u.factorial : ℚ) / ((t+u+2+1).factorial : ℚ) *
       ((u:ℚ)*((u:ℚ)+1)-((t:ℚ)+2)) := by
  unfold weight
  rw [show t+u+2-(t+1)=u+1 by omega,show t+u+2-(t+2)=u by omega]
  rw [Nat.factorial_succ u,Nat.factorial_succ (t+1)]
  push_cast
  ring

theorem star_beats (t u : Nat) (le : t≤u) (ut : 2≤u) :
    weight (t+u) t < score (t+u+2) (star t u) := by
  rw [star_score,cylinder_at_slack_two]
  have h : 0 < (u:ℚ)*((u:ℚ)+1)-((t:ℚ)+2) := by
    have T : (t:ℚ)≤(u:ℚ) := by exact_mod_cast le
    have U : (2:ℚ)≤(u:ℚ) := by exact_mod_cast ut
    nlinarith
  have factPos (v : Nat) : 0 < (v.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos v
  have W := mul_pos
    (div_pos (mul_pos (factPos (t+1)) (factPos u)) (factPos (t+u+2+1))) h
  rw [←weight_difference] at W
  linarith

def extendedStar (t u : Nat) : Nat → Family
  | 0 => star t u
  | d+1 => double (extendedStar t u d) (t+u+2+d)

theorem extended_is_valid (t u d : Nat) :
    IsIU (extendedStar t u d) (t+u+2+d) t u := by
  induction d with
  | zero => exact star_valid t u
  | succ d ih => exact (lift_double _ ih (by omega)).1

theorem extended_score (t u d : Nat) :
    score (t+u+2+d) (extendedStar t u d)=score (t+u+2) (star t u) := by
  induction d with
  | zero => rfl
  | succ d ih => exact (score_extend (extended_is_valid t u d)).trans ih

theorem eventual_counterexample (t u n : Nat) (le : t≤u) (ut : 2≤u) (hn : t+u+2≤n) :
    ∃ F : Family, IsIU F n t u ∧ score n (cylinder t u (n-(t+u))) < score n F := by
  let d := n-(t+u+2)
  have E : t+u+2+d=n := Nat.add_sub_of_le hn
  refine ⟨extendedStar t u d,E ▸ extended_is_valid t u d,?_⟩
  rw [← E,extended_score]
  have E' : t+u+(t+u+2+d-(t+u))=t+u+2+d := by omega
  have H := cylinder_score t u (t+u+2+d-(t+u))
  rw [E'] at H
  rw [H]
  exact star_beats t u le ut

#print axioms eventual_counterexample
end IU.Lubell
