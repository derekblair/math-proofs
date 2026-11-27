import StabilityMatching
import Mathlib.Data.Finset.Max

open scoped BigOperators

namespace SparseHalfStability

variable {V : Type*} [Fintype V] [DecidableEq V]

def Covers (D : Finset V) (F : Finset (Edge (V := V))) : Prop :=
  ∀ e ∈ F, e.1 ∈ D ∨ e.2 ∈ D

theorem ends_eq (M : Finset (Edge (V := V))) :
    Ends M = M.image Prod.fst ∪ M.image Prod.snd := by
  apply Finset.ext
  intro v
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · intro H
    obtain ⟨e,he,h⟩ := (Finset.mem_filter.mp H).2
    rcases h with h | h
    · exact Or.inl ⟨e,he,h.symm⟩
    · exact Or.inr ⟨e,he,h.symm⟩
  · rintro (⟨e,he,h⟩|⟨e,he,h⟩)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,he,Or.inl h.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,he,Or.inr h.symm⟩

theorem card_ends (M : Finset (Edge (V := V))) :
    (Ends M).card ≤ 2*M.card := by
  rw [ends_eq, two_mul]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

theorem matching_le_cover (F M : Finset (Edge (V := V))) (D : Finset V)
    (hM : M ⊆ F) (hm : IsMatching M) (hD : Covers D F) :
    M.card ≤ D.card := by
  let f (e : Edge (V := V)) := if e.1 ∈ D then e.1 else e.2
  have hOn (e : Edge (V := V)) : OnEdge (f e) e := by
    unfold f OnEdge
    split <;> simp
  apply Finset.card_le_card_of_injOn f
  · intro e he
    unfold f
    split
    · assumption
    · exact Or.resolve_left (hD e (hM he)) (by assumption)
  · intro e he t ht h
    have hh := hOn t
    rw [← h] at hh
    exact hm e he t ht _ (hOn e) hh

theorem exists_matching_cover (F : Finset (Edge (V := V))) :
    ∃ M ⊆ F, IsMatching M ∧ Covers (Ends M) F := by
  classical
  let options := F.powerset.filter IsMatching
  have hn : options.Nonempty := ⟨∅, by simp [options,IsMatching]⟩
  obtain ⟨M,hM,hmax⟩ := Finset.exists_max_image options Finset.card hn
  have hMf := Finset.mem_filter.mp hM
  have hsub := Finset.mem_powerset.mp hMf.1
  refine ⟨M,hsub,hMf.2,?_⟩
  intro e he
  by_contra! hnE
  have neM : e ∉ M := by
    intro h
    exact hnE.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,h,Or.inl rfl⟩)
  have hnew : IsMatching (insert e M) := by
    intro a ha b hb v hva hvb
    have A := Finset.mem_insert.mp ha
    have B := Finset.mem_insert.mp hb
    rcases A with A | A <;> rcases B with B | B
    · exact A.trans B.symm
    · subst a
      rcases hva with rfl | rfl
      · exact False.elim (hnE.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,B,hvb⟩))
      · exact False.elim (hnE.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,B,hvb⟩))
    · subst b
      rcases hvb with rfl | rfl
      · exact False.elim (hnE.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,A,hva⟩))
      · exact False.elim (hnE.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,A,hva⟩))
    · exact hMf.2 a A b B v hva hvb
  have hh := hmax (insert e M) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨he,hsub⟩),hnew⟩)
  rw [Finset.card_insert_of_notMem neM] at hh
  omega

theorem cover_degree_count (F : Finset (Edge (V := V))) (D : Finset V)
    (hc : Covers D F) (degree : ∀ v ∈ D, ((F.filter (OnEdge v)).card : ℝ) ≤ d) :
    (F.card : ℝ) ≤ D.card*d := by
  let pick (e : Edge (V := V)) : Sigma (fun _ : V => Edge (V := V)) :=
    ⟨if e.1 ∈ D then e.1 else e.2, e⟩
  have H := Finset.card_le_card_of_injOn (s := F)
      (t := D.sigma fun v => F.filter (OnEdge v)) pick (by
        intro e he
        change pick e ∈ D.sigma (fun v => F.filter (OnEdge v))
        rw [Finset.mem_sigma]
        dsimp [pick]
        split
        · exact ⟨by assumption, Finset.mem_filter.mpr ⟨he,Or.inl rfl⟩⟩
        · exact ⟨Or.resolve_left (hc e he) (by assumption),
            Finset.mem_filter.mpr ⟨he,Or.inr rfl⟩⟩)
      (by
        intro a _ b _ h
        exact congrArg (fun s : Sigma (fun _ : V => Edge (V := V)) => s.2) h)
  have H' : (F.card : ℝ) ≤ ∑ v ∈ D, ((F.filter (OnEdge v)).card : ℝ) := by
    rw [Finset.card_sigma] at H
    exact_mod_cast H
  exact H'.trans (by simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum degree)

theorem matching_lower (B G : V → V → Bool) (M : Finset (Edge (V := V)))
    (hm : IsMatching M) (plus : ∀ e ∈ M, G e.1 e.2 = true)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (common_lower : ∀ e ∈ M, c ≤ ((common B e).card : ℝ)) :
    (M.card : ℝ)*(c-2*M.card) ≤ (crossMissing B G M).card := by
  have h := matching_missing B G M hm plus tf
  rw [Finset.card_sigma] at h
  have h' : (∑ e ∈ M, ((exposed B M e).card : ℝ)) ≤ (crossMissing B G M).card := by
    exact_mod_cast h
  refine le_trans ?_ h'
  have lower (e : Edge (V := V)) (he : e ∈ M) :
      c-2*M.card ≤ ((exposed B M e).card : ℝ) := by
    have H : ((common B e).card : ℝ) ≤ (exposed B M e).card + (Ends M).card := by
      exact_mod_cast exposed_subtraction B M e
    have H2 : ((Ends M).card : ℝ) ≤ 2*M.card := by exact_mod_cast card_ends M
    linarith [common_lower e he]
  simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum lower

#print axioms matching_lower
#print axioms exists_matching_cover
#print axioms cover_degree_count
end SparseHalfStability
