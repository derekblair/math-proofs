import HubTriplePool
import Mathlib.Tactic.Tauto

namespace Erdos151H13
noncomputable section
open Classical
open Erdős151 Erdos151H12
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

def outerCandidates (x w y : V) : Finset V :=
  ((neighbors G x ∪ neighbors G y) \ insert w (neighbors G w)).filter
    (fun a => ¬ Lone G x a ∧ ¬ Lone G y a)

def outerCoreSide (x w : V) : Finset V :=
  neighbors C x \ insert w (neighbors G w)

theorem outer_core_side_size
    (sub : ∀ a b, C a b → G a b) (x w : V) :
    (neighbors C x).card ≤ (outerCoreSide G C x w).card +
      (neighbors G x ∩ neighbors G w).card + 1 := by
  let S := neighbors G x∩neighbors G w
  have h := Finset.card_sdiff_add_card_inter (neighbors C x) (insert w (neighbors G w))
  change (outerCoreSide G C x w).card + _ = _ at h
  have hs : (neighbors C x ∩ insert w (neighbors G w)) ⊆ insert w S := by
    intro a ha
    obtain ⟨hc,hw⟩ := Finset.mem_inter.mp ha
    rcases Finset.mem_insert.mp hw with rfl|h'
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr
        ⟨(mem_neighbors G).mpr (sub x a ((mem_neighbors C).mp hc)),h'⟩)
  have he := Finset.card_le_card hs
  have hh := Finset.card_insert_le w S
  change _ ≤ _ + S.card + 1
  omega

/-- The two core-side incidences can be combined without a two-for-one
loss at any shared outer vertex. This is the exact overlap saving. -/
theorem outer_candidates_size
    (sub : ∀ a b, C a b → G a b)
    (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x w y : V) :
    (neighbors C x).card + (neighbors C y).card ≤
      (outerCandidates G x w y).card +
      ((neighbors G x ∩ neighbors G y) \ insert w (neighbors G w)).card +
      (neighbors G x ∩ neighbors G w).card + (neighbors G y ∩ neighbors G w).card + 2 := by
  let P := outerCoreSide G C x w
  let Q := outerCoreSide G C y w
  let S := (neighbors G x ∩ neighbors G y) \ insert w (neighbors G w)
  let E := outerCandidates G x w y
  have side (u a : V) (h : a ∈ outerCoreSide G C u w) :
      G u a ∧ ¬ Lone G u a ∧ a ∉ insert w (neighbors G w) := by
    have hf := Finset.mem_sdiff.mp h
    have hc := (mem_neighbors C).mp hf.1
    exact ⟨sub u a hc,coreNonlone u a hc,hf.2⟩
  have share : P ∩ Q ⊆ S := by
    intro a ha
    obtain ⟨p,q⟩ := Finset.mem_inter.mp ha
    obtain ⟨hx,_,ho⟩ := side x a p
    obtain ⟨hy,_,_⟩ := side y a q
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr
      ⟨(mem_neighbors G).mpr hx,(mem_neighbors G).mpr hy⟩,ho⟩
  have see (a : V) (p : G x a ∨ G y a)
      (nx : ¬Lone G x a) (ny : ¬Lone G y a)
      (ho : a ∉ insert w (neighbors G w)) : a ∈ E := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr ?_,ho⟩,nx,ny⟩
    exact p.elim (fun h => Or.inl ((mem_neighbors G).mpr h))
      (fun h => Or.inr ((mem_neighbors G).mpr h))
  have keep2 : P ∩ Q ⊆ E := by
    intro a ha
    obtain ⟨p,q⟩ := Finset.mem_inter.mp ha
    obtain ⟨hx,nx,ho⟩ := side x a p
    exact see a (Or.inl hx) nx (side y a q).2.1 ho
  have keep1 : (P ∪ Q) \ S ⊆ E := by
    intro a ha
    obtain ⟨hp,hn⟩ := Finset.mem_sdiff.mp ha
    rcases Finset.mem_union.mp hp with p|q
    · obtain ⟨hx,nx,ho⟩ := side x a p
      apply see a (Or.inl hx) nx _ ho
      intro h
      exact hn (Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr hx,(mem_neighbors G).mpr h.1⟩,ho⟩)
    · obtain ⟨hy,ny,ho⟩ := side y a q
      apply see a (Or.inr hy) _ ny ho
      intro h
      exact hn (Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr h.1,(mem_neighbors G).mpr hy⟩,ho⟩)
  have h := outer_retention_count P Q S E share keep2 keep1
  have c1 := outer_core_side_size G C sub x w
  have c2 := outer_core_side_size G C sub y w
  change P.card+Q.card ≤ _ at h
  change _ ≤ P.card + (neighbors G x ∩ neighbors G w).card + 1 at c1
  change _ ≤ Q.card + (neighbors G y ∩ neighbors G w).card + 1 at c2
  unfold E S at h
  omega

def centerCandidates (x w y : V) : Finset V :=
  neighbors C w \ (((neighbors G x ∩ neighbors G w) ∪
    (neighbors G y ∩ neighbors G w)) ∪ ({x,y} : Finset V))

theorem center_candidates_size (x w y : V) :
    (neighbors C w).card +
      ((neighbors G x ∩ neighbors G w) ∩ (neighbors G y ∩ neighbors G w)).card ≤
    (centerCandidates G C x w y).card +
      (neighbors G x ∩ neighbors G w).card + (neighbors G y ∩ neighbors G w).card + 2 := by
  let P := neighbors G x∩neighbors G w
  let Q := neighbors G y∩neighbors G w
  let H : Finset V := {x,y}
  have d := Finset.card_sdiff_add_card_inter (neighbors C w) ((P ∪ Q) ∪ H)
  have u := Finset.card_union_add_card_inter (P ∪ Q) H
  have t := Finset.card_union_add_card_inter P Q
  have hle : H.card ≤ 2 := by
    exact (Finset.card_insert_le x ({y} : Finset V)).trans (by simp)
  have htop : (neighbors C w ∩ ((P∪Q)∪H)).card ≤ ((P∪Q)∪H).card :=
    Finset.card_le_card (by intro v hv; exact (Finset.mem_inter.mp hv).2)
  change _ + (P ∩ Q).card ≤ (centerCandidates G C x w y).card + P.card + Q.card + 2
  change (centerCandidates G C x w y).card + _ = _ at d
  omega

theorem center_candidates_eligible
    (sub : ∀ a b, C a b → G a b)
    (coreNonlone : ∀ a b, C a b → ¬ Lone G a b) (x w y : V) :
    ∀ a ∈ centerCandidates G C x w y, CenterEligible G x w y a := by
  intro a ha
  obtain ⟨hc,hout⟩ := Finset.mem_sdiff.mp ha
  have hc := (mem_neighbors C).mp hc
  have hw := sub w a hc
  refine ⟨hw,coreNonlone w a hc,?_,?_⟩
  · intro hx
    exact hout (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr hx,(mem_neighbors G).mpr hw⟩)))
  · intro hy
    exact hout (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr hy,(mem_neighbors G).mpr hw⟩)))

theorem outer_candidates_eligible (x w y : V) :
    ∀ a ∈ outerCandidates G x w y, OuterEligible G x w y a := by
  intro a ha
  have h := Finset.mem_filter.mp ha
  have he := Finset.mem_sdiff.mp h.1
  exact ⟨fun e => he.2 (Finset.mem_insert_of_mem ((mem_neighbors G).mpr e)),h.2⟩

theorem candidate_pools_disjoint (sub : ∀ a b, C a b → G a b) (x w y : V) :
    Disjoint (centerCandidates G C x w y) (outerCandidates G x w y) := by
  apply Finset.disjoint_left.mpr
  intro a ca oa
  have hw := sub w a ((mem_neighbors C).mp (Finset.mem_sdiff.mp ca).1)
  exact (outer_candidates_eligible G x w y a oa).1 hw

theorem candidate_pools_inside
    (sub : ∀ a b, C a b → G a b) (irr : ∀ a, ¬ G a a)
    (x w y : V) (wx : G w x) (wy : G w y) :
    centerCandidates G C x w y ∪ outerCandidates G x w y ⊆
      ((neighbors G x ∪ neighbors G y) ∪ neighbors G w) \ ({x,w,y} : Finset V) := by
  intro a ha
  apply Finset.mem_sdiff.mpr
  rcases Finset.mem_union.mp ha with ca|oa
  · obtain ⟨hc,hn⟩ := Finset.mem_sdiff.mp ca
    have hw := sub w a ((mem_neighbors C).mp hc)
    refine ⟨Finset.mem_union_right _ ((mem_neighbors G).mpr hw),?_⟩
    intro hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl|rfl|rfl
    · exact hn (Finset.mem_union_right _ (by simp))
    · exact irr _ hw
    · exact hn (Finset.mem_union_right _ (by simp))
  · obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp (Finset.mem_filter.mp oa).1
    refine ⟨Finset.mem_union_left _ hm,?_⟩
    intro hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl|rfl|rfl
    · exact hn (Finset.mem_insert_of_mem ((mem_neighbors G).mpr wx))
    · exact hn (Finset.mem_insert_self _ _)
    · exact hn (Finset.mem_insert_of_mem ((mem_neighbors G).mpr wy))

#print axioms candidate_pools_inside
#print axioms candidate_pools_disjoint
#print axioms center_candidates_size
#print axioms center_candidates_eligible
#print axioms outer_core_side_size
#print axioms outer_candidates_size
end
end Erdos151H13
