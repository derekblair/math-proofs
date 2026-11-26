import BK73Main1
import BK73Graph4

open SimpleGraph Finset

namespace BK73

/-- core: every bridgeless graph on 7 vertices with ≥ 11 edges has an orientation of
diameter ≤ 4, given the kernel-checked enumeration `htop`. -/
theorem main4_of (htop : allL chk4 21 10 [] = true) (G : SimpleGraph (Fin 7)) (hG : Bridgeless G)
    (hE : 11 ≤ G.edgeSet.ncard) : HasOrientDiamLE G 4 := by
  classical
  have hdeg : ∀ v, 2 ≤ G.degree v := by
    intro v; by_contra h; rw [not_le] at h
    refine not_bridgeless_of_degree_le_one G v (if v = 0 then 1 else 0) ?_ (by omega) hG
    split_ifs with hv
    · subst hv; decide
    · exact hv
  set σ : Equiv.Perm (Fin 7) := Tuple.sort (fun v => G.degree v) with hσ
  have hmono : Monotone ((fun v => G.degree v) ∘ σ) := Tuple.monotone_sort _
  set G' := G.comap σ with hG'
  set m := ofBits (codeList G') with hm
  have e : ∀ i : Fin 7, deg m i.val = G.degree (σ i) := fun i => by
    rw [hm, deg_code]; exact degree_comap G σ i
  have hsum : ∑ i, G'.degree i = 2 * G.edgeSet.ncard := by
    rw [show ∑ i, G'.degree i = ∑ i, G.degree (σ i) from
      Finset.sum_congr rfl (fun i _ => degree_comap G σ i)]
    rw [Equiv.sum_comp σ (fun i => G.degree i), sum_degrees_eq_twice_card_edges,
      ← coe_edgeFinset, Set.ncard_coe_finset]
  have hct := handshake_code G'
  have hcnt : (codeList G').count false ≤ 10 := by
    have := count_true_add_false (codeList G'); rw [codeList_length] at this; omega
  have hchk := allL_sound chk4 21 10 [] htop (codeList G').reverse
    (by simp [codeList_length]) (by simpa using hcnt)
  rw [List.reverse_reverse, List.append_nil] at hchk
  have h0 : ¬ deg m 0 ≤ 1 := by
    have := e 0; have := hdeg (σ 0); simp only [Fin.val_zero] at *; omega
  have hle : ∀ i j : Fin 7, i ≤ j → deg m i.val ≤ deg m j.val := fun i j hij => by
    rw [e, e]; exact hmono hij
  have hs : sorted m = true := by
    have h01 := hle 0 1 (by decide); have h12 := hle 1 2 (by decide)
    have h23 := hle 2 3 (by decide); have h34 := hle 3 4 (by decide)
    have h45 := hle 4 5 (by decide); have h56 := hle 5 6 (by decide)
    simp only [sorted, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨h01, h12⟩, h23⟩, h34⟩, h45⟩, h56⟩
  unfold chk4 at hchk
  rw [← hm, if_neg h0, if_neg (by simp [hs])] at hchk
  obtain ⟨t, -, ht⟩ := List.any_eq_true.mp hchk
  obtain ⟨O', hO'⟩ := good4_hasOrient G' t ht
  refine ⟨{ arc := fun x y => O'.arc (σ.symm x) (σ.symm y),
            arc_adj := fun x y h => by simpa [hG', comap_adj] using O'.arc_adj _ _ h,
            total := fun x y h => O'.total _ _ (by simpa [hG', comap_adj] using h),
            anti := fun x y h => O'.anti _ _ h }, ?_⟩
  intro x y
  obtain ⟨k, hk, hr⟩ := hO' (σ.symm x) (σ.symm y)
  exact ⟨k, hk, by simpa using dreach_map O'.arc σ hr⟩

end BK73
