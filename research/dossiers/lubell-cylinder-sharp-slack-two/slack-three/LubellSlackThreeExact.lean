import LubellSlackThreeWeights
import LubellClassification

namespace IU.Lubell
open Finset
open scoped BigOperators

def insertedRange (m n : Nat) : Family :=
  ((range n) \ range m).image (fun e => insert e (range m))

private theorem insert_range_shape (m n : Nat) (hmn : m≤n)
    (A : Finset Nat) (a : A∈insertedRange m n) :
    A⊆range n ∧ range m⊆A ∧ A.card=m+1 := by
  obtain ⟨z,hz,rfl⟩ := mem_image.mp a
  obtain ⟨h1,h2⟩ := mem_sdiff.mp hz
  refine ⟨insert_subset h1 (range_mono hmn),subset_insert _ _,?_⟩
  rw [card_insert_of_notMem h2,card_range]

private theorem insert_range_count (m n : Nat) (h : m≤n) :
    (insertedRange m n).card=n-m := by
  unfold insertedRange
  rw [card_image_of_injOn,card_sdiff_of_subset (range_mono h),card_range,card_range]
  intro a ha b hb e
  have he : insert a (range m)=insert b (range m) := e
  have m : a ∈ insert b (range m) := by rw [←he]; exact mem_insert_self _ _
  rcases mem_insert.mp m with h|h
  · exact h
  · exact False.elim ((mem_sdiff.mp ha).2 h)

def lowThree (t u : Nat) : Family :=
  {range t} ∪ insertedRange t (t+u+3) ∪ insertedRange (t+1) (t+u+3)

theorem low_three_valid (t u : Nat) : IsIU (lowThree t u) (t+u+3) t u := by
  have shape (A : Finset Nat) (h : A∈lowThree t u) :
      A⊆range (t+u+3) ∧ range t⊆A ∧ (A.card≤t+1 ∨ (range (t+1)⊆A ∧ A.card=t+2)) := by
    rcases mem_union.mp h with h|h
    · rcases mem_union.mp h with h|h
      · have eq : A=range t := mem_singleton.mp h
        subst A
        exact ⟨range_mono (by omega),Subset.rfl,Or.inl (by simp)⟩
      · obtain ⟨s1,s2,s3⟩ := insert_range_shape t (t+u+3) (by omega) A h
        exact ⟨s1,s2,Or.inl (by omega)⟩
    · obtain ⟨s1,s2,s3⟩ := insert_range_shape (t+1) (t+u+3) (by omega) A h
      exact ⟨s1,(range_mono (by omega)).trans s2,Or.inr ⟨s2,by omega⟩⟩
  refine ⟨fun A a => (shape A a).1,?_⟩
  intro A a B b
  have as := shape A a
  have bs := shape B b
  have i := card_le_card (subset_inter as.2.1 bs.2.1)
  rw [card_range] at i
  refine ⟨i,?_⟩
  have c := card_union_add_card_inter A B
  rcases as.2.2 with aa|aa <;> rcases bs.2.2 with bb|bb
  · omega
  · omega
  · omega
  · have hi := card_le_card (subset_inter aa.1 bb.1)
    rw [card_range] at hi
    omega

private theorem range_layer_sum (m n : Nat) (h : m≤n) :
    (∑ A∈insertedRange m n, weight n A.card)=((n-m:Nat):ℚ)*weight n (m+1) := by
  rw [←insert_range_count m n h,←nsmul_eq_mul,←Finset.sum_const]
  exact Finset.sum_congr rfl (fun A a => by
    rw [(insert_range_shape m n h A a).2.2])

theorem low_three_score (t u : Nat) :
    score (t+u+3) (lowThree t u)=scoreLo3 t u := by
  have dis : Disjoint ({range t}:Family) (insertedRange t (t+u+3)) :=
    Finset.disjoint_left.mpr (by
      intro A a b
      have e := mem_singleton.mp a
      have h := (insert_range_shape t (t+u+3) (by omega) A b).2.2
      rw [e,card_range] at h
      omega)
  have dis2 :
      Disjoint (({range t}:Family) ∪ insertedRange t (t+u+3))
        (insertedRange (t+1) (t+u+3)) :=
    Finset.disjoint_left.mpr (by
      intro A a b
      have h := (insert_range_shape (t+1) (t+u+3) (by omega) A b).2.2
      rcases mem_union.mp a with a|a
      · rw [mem_singleton.mp a,card_range] at h
        omega
      · have j := (insert_range_shape t (t+u+3) (by omega) A a).2.2
        omega)
  unfold score lowThree scoreLo3
  rw [sum_union dis2,sum_union dis,sum_singleton,card_range,range_layer_sum _ _ (by omega),
    range_layer_sum _ _ (by omega),show t+u+3-t=u+3 by omega,
    show t+u+3-(t+1)=u+2 by omega,show t+1+1=t+2 by omega]
  push_cast
  rfl

theorem slack_three_exact_ordered (t u : Nat) (ht : 1≤t) (le : t≤u) (hu : 2≤u) :
   IsIU (lowThree t u) (t+u+3) t u ∧
     score (t+u+3) (lowThree t u)=scoreLo3 t u ∧
     ∀ F:Family, IsIU F (t+u+3) t u → score (t+u+3) F≤scoreLo3 t u :=
  ⟨low_three_valid t u, low_three_score t u,fun _ h => slack_three_upper ht le hu h⟩

private theorem raw_eq {F : Family} {n t u : Nat} (h : IsIU F n t u) :
    raw n F=((n:ℚ)+1)*score n F := by
  have nz : (((n+1:Nat):ℚ))≠0 := by positivity
  have e := (eq_div_iff nz).mp (score_raw h)
  rw [Nat.cast_add,Nat.cast_one] at e
  exact e.symm.trans (mul_comm _ _)

/-- Symmetric statement directly for the raw, not normalized, Lubell sum. -/
theorem sharp_slack_three (t u : Nat) (ht : 1≤t) (hu : 1≤u) (big : 2≤max t u) :
    let n := t+u+3
    let best := ((n:ℚ)+1)*scoreLo3 (min t u) (max t u)
    (∃ W : Family, IsIU W n t u ∧ raw n W=best) ∧
      ∀ F : Family, IsIU F n t u → raw n F≤best := by
  dsimp
  by_cases h : t≤u
  · rw [min_eq_left h,max_eq_right h] at *
    obtain ⟨vw,es,up⟩ := slack_three_exact_ordered t u ht h big
    constructor
    · refine ⟨lowThree t u,vw,?_⟩
      rw [raw_eq vw,es]
    · intro F v
      rw [raw_eq v]
      exact mul_le_mul_of_nonneg_left (up F v) (by positivity)
  · have h' : u≤t := by omega
    rw [min_eq_right h',max_eq_left h'] at *
    have nEq : u+t+3=t+u+3 := by omega
    obtain ⟨vw,es,up⟩ := slack_three_exact_ordered u t hu h' big
    rw [nEq] at vw es up
    constructor
    · have v := opp_valid vw (by omega)
      refine ⟨opposite (lowThree u t) (t+u+3),v,?_⟩
      rw [raw_eq v,opp_score vw,es]
    · intro F v
      rw [raw_eq v,←opp_score v]
      exact mul_le_mul_of_nonneg_left (up _ (opp_valid v (by omega))) (by positivity)

#print axioms slack_three_exact_ordered
#print axioms sharp_slack_three
end IU.Lubell
