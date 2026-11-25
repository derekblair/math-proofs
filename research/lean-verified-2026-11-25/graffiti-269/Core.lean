import KeepTree

namespace Wow268
variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V}

open scoped BigOperators

lemma selected_degree [DecidableRel T.Adj] {S : Finset V}
    (h : TotalDominating T S) : Fintype.card V ≤ ∑ u ∈ S, T.degree u := by
  classical
  let D : Finset T.Dart := Finset.univ.filter (fun d => d.fst ∈ S)
  choose f hf hfa using h
  let F : V → D := fun v =>
    ⟨⟨(f v,v),(hfa v).symm⟩, by simp [D, hf]⟩
  have hFi : Function.Injective F := by
    intro a b hab
    exact congrArg (fun d : D => d.val.snd) hab
  have hcount := Fintype.card_le_of_injective F hFi
  rw [Fintype.card_coe] at hcount
  refine hcount.trans_eq ?_
  rw [Finset.card_eq_sum_card_fiberwise (f := fun d : T.Dart => d.toProd.1) (t := S)
    (show Set.MapsTo (fun d : T.Dart => d.toProd.1) ↑D ↑S by intro d hd; simpa [D] using hd)]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← T.dart_fst_fiber_card_eq_degree]
  congr 1
  ext d
  simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨And.right, fun he => ⟨he.symm ▸ hu, he⟩⟩

lemma card_small_core [DecidableRel T.Adj] (hT : T.IsTree)
    {S : Finset V} (h : TotalDominating T S) :
    (S ∪ Finset.univ.filter (fun v => 2 ≤ T.degree v)).card ≤ 2 * S.card - 2 := by
  classical
  let H : Finset V := Sᶜ.filter (fun v => 2 ≤ T.degree v)
  have hTsum := T.sum_degrees_eq_twice_card_edges
  have hE := hT.card_edgeFinset
  have hSel := selected_degree h
  have hPart : (∑ v ∈ S, T.degree v) + ∑ v ∈ Sᶜ, T.degree v = ∑ v, T.degree v := by
    have hh := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset V)
      (fun v => v ∈ S) (fun v => T.degree v)
    have h₁ : Finset.univ.filter (fun v => v ∈ S) = S := by ext v; simp
    have h₂ : Finset.univ.filter (fun v => v ∉ S) = Sᶜ := by ext v; simp
    rwa [h₁,h₂] at hh
  have hdeg : Sᶜ.card + H.card ≤ ∑ v ∈ Sᶜ, T.degree v := by
    calc
      _ = ∑ v ∈ Sᶜ, (1 + if 2 ≤ T.degree v then 1 else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [H]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        have hPos := (T.degree_pos_iff_exists_adj v).mpr (by
          obtain ⟨w,_,hw⟩ := h v
          exact ⟨w,hw⟩)
        split <;> omega
  have hC := Finset.card_compl S
  have hDisj : Disjoint S H := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv hH
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp hH).1) hv
  have hU : S ∪ Finset.univ.filter (fun v => 2 ≤ T.degree v) = S ∪ H := by
    ext v
    by_cases hv : v ∈ S <;> simp [H,hv]
  rw [hU, Finset.card_union_of_disjoint hDisj]
  omega

end Wow268
