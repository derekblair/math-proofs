import OuterExclusive
import RetentionRecipe
import OneShared

namespace Erdos151H13
open Erdős151 Erdos151H12 Erdos151Ramsey
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem outer_swap (x w y : V) :
    outerCandidates G x w y = outerCandidates G y w x := by
  classical
  ext a
  simp only [outerCandidates,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union]
  tauto

theorem conflict_symm (sym : ∀ {a b}, G a b → G b a) (x y : V) :
    ∀ {a b}, pairConflict G x y a b → pairConflict G x y b a :=
  fun e => ⟨sym e.1,e.2.elim (fun h => Or.inl ⟨h.2,h.1⟩) (fun h => Or.inr ⟨h.2,h.1⟩)⟩

theorem conflict_irr (irr : ∀ a, ¬ G a a) (x y a : V) :
    ¬ pairConflict G x y a a := fun e => irr a e.1

theorem independent_from_exclusive
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G)
    (sub : ∀ a b, C a b → G a b) (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x w y : V) (m n : ℕ)
    (mx : m ≤ (exclusiveCoreSide G C x w y).card)
    (my : n ≤ (exclusiveCoreSide G C y w x).card) :
    ∃ B ⊆ outerCandidates G x w y,
      alphaFloor m+alphaFloor n ≤ B.card ∧ Independent (pairConflict G x y) B := by
  classical
  let A := exclusiveCoreSide G C x w y
  let B := exclusiveCoreSide G C y w x
  let P := pairConflict G x y
  obtain ⟨S,ss,sc,si⟩ := choose_alpha_floor P A m mx (conflict_symm G sym x y)
    (conflict_irr G irr x y) (pairConflict_triangleFree G x y link)
  obtain ⟨T,ts,tc,ti⟩ := choose_alpha_floor P B n my (conflict_symm G sym x y)
    (conflict_irr G irr x y) (pairConflict_triangleFree G x y link)
  have Sside (a : V) (h : a ∈ S) := exclusive_core_side_mem G C sub coreNonlone x w y a (ss h)
  have Tside (a : V) (h : a ∈ T) := exclusive_core_side_mem G C sub coreNonlone y w x a (ts h)
  have dis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Tside a hb).2.2 (Sside a ha).2.1
  refine ⟨S∪T,?_,?_,?_⟩
  · intro a h
    rcases Finset.mem_union.mp h with h|h
    · exact (Sside a h).1
    · rw [outer_swap G x w y]
      exact (Tside a h).1
  · rw [Finset.card_union_of_disjoint dis]
    omega
  · intro a ha b hb e
    rcases Finset.mem_union.mp ha with hal|har <;>
      rcases Finset.mem_union.mp hb with hbl|hbr
    · exact si a hal b hbl e
    · rcases e.2 with f|f
      · exact (Tside b hbr).2.2 f.2
      · exact (Sside a hal).2.2 f.1
    · rcases e.2 with f|f
      · exact (Tside a har).2.2 f.1
      · exact (Sside b hbl).2.2 f.2
    · exact ti a har b hbr e

/-- Exact shared-one exception: either one side loses no candidates,
or there is a retained common point and two exclusive points per side. -/
theorem shared_one_outer_three
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G)
    (sub : ∀ a b, C a b → G a b) (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x w y : V)
    (mx : 3 ≤ (outerCoreSide G C x w).card) (my : 3 ≤ (outerCoreSide G C y w).card)
    (ex : 2 ≤ (exclusiveCoreSide G C x w y).card)
    (ey : 2 ≤ (exclusiveCoreSide G C y w x).card)
    (he : ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card = 1) :
    ∃ B ⊆ outerCandidates G x w y, 3 ≤ B.card ∧ Independent (pairConflict G x y) B := by
  classical
  let Q := (neighbors G x∩neighbors G y)\insert w (neighbors G w)
  let A := exclusiveCoreSide G C x w y
  let B := exclusiveCoreSide G C y w x
  let P := pairConflict G x y
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp he
  change Q = {p} at hp
  have side_mem (a i j : V) (h : a ∈ outerCoreSide G C i w) :
      G i a ∧ ¬ Lone G i a ∧ a ∉ insert w (neighbors G w) := by
    obtain ⟨hl,hr⟩ := Finset.mem_sdiff.mp h
    have hc := (mem_neighbors C).mp hl
    exact ⟨sub i a hc,coreNonlone i a hc,hr⟩
  by_cases hx : p ∈ outerCoreSide G C x w
  · by_cases hy : p ∈ outerCoreSide G C y w
    · have xp := side_mem p x y hx
      have yp := side_mem p y x hy
      have pa : p ∉ A := fun h => (Finset.mem_sdiff.mp h).2 ((mem_neighbors G).mpr yp.1)
      have pb : p ∉ B := fun h => (Finset.mem_sdiff.mp h).2 ((mem_neighbors G).mpr xp.1)
      have pin : p ∈ outerCandidates G x w y :=
        Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_left _ ((mem_neighbors G).mpr xp.1),xp.2.2⟩,xp.2.1,yp.2.1⟩
      have xa := exclusive_core_side_mem G C sub coreNonlone x w y
      have yb := exclusive_core_side_mem G C sub coreNonlone y w x
      have dis : Disjoint A B := Finset.disjoint_left.mpr (fun a ha hb => (yb a hb).2.2 (xa a ha).2.1)
      have cross : ∀ a ∈ A, ∀ b ∈ B, ¬ P a b := by
        intro a ha b hb h
        rcases h.2 with e|e
        · exact (yb b hb).2.2 e.2
        · exact (xa a ha).2.2 e.1
      obtain ⟨T,ts,tc,ti⟩ := independent_three_one_shared P (conflict_symm G sym x y)
        (conflict_irr G irr x y) (pairConflict_triangleFree G x y link)
        A B p ex ey pa pb dis cross
      refine ⟨T,?_,tc,ti⟩
      intro a ha
      rcases Finset.mem_insert.mp (ts ha) with rfl|h
      · exact pin
      · rcases Finset.mem_union.mp h with hl|hr
        · exact (xa a hl).1
        · rw [outer_swap G x w y]
          exact (yb a hr).1
    · have E : outerCoreSide G C y w ⊆ B := by
        intro v hv
        have z := side_mem v y x hv
        refine Finset.mem_sdiff.mpr ⟨hv,?_⟩
        intro nx
        have q : v∈Q := Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨nx,(mem_neighbors G).mpr z.1⟩,z.2.2⟩
        have vp : v=p := by simpa [hp] using q
        exact hy (vp ▸ hv)
      have b3 := my.trans (Finset.card_le_card E)
      obtain ⟨T,hs,hc,hi⟩ := independent_from_exclusive G C sym irr link sub coreNonlone x w y 2 3 ex b3
      exact ⟨T,hs,by simpa [alphaFloor] using hc,hi⟩
  · have E : outerCoreSide G C x w ⊆ A := by
      intro v hv
      have z := side_mem v x y hv
      refine Finset.mem_sdiff.mpr ⟨hv,?_⟩
      intro ny
      have q : v∈Q := Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr z.1,ny⟩,z.2.2⟩
      have vp : v=p := by simpa [hp] using q
      exact hx (vp ▸ hv)
    have a3 := mx.trans (Finset.card_le_card E)
    obtain ⟨T,hs,hc,hi⟩ := independent_from_exclusive G C sym irr link sub coreNonlone x w y 3 2 a3 ey
    exact ⟨T,hs,by simpa [alphaFloor] using hc,hi⟩

#print axioms independent_from_exclusive
#print axioms shared_one_outer_three
end Erdos151H13
