import H12Eligible

namespace Erdos151H12
open Erdős151
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem all_ambient_common_core_left
    (mono : ∀ {a b}, C a b → G a b) (t : TwoTriangles C)
    (u v : V) (hr : 8 ≤ (neighbors C u).card)
    (hc : ambientCodeg G u v = 5) (he : (eligible G u v).card ≤ 2) :
    neighbors G u ∩ neighbors G v ⊆ neighbors C u := by
  let X := neighbors G u ∩ neighbors G v
  let Y := neighbors C u ∩ neighbors G v
  have hY : Y ⊆ X := by
    intro a ha
    obtain ⟨hca,hva⟩ := Finset.mem_inter.mp ha
    exact Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr (mono ((mem_neighbors C).mp hca)),hva⟩
  have hsub : neighbors C u ⊆ insert v (Y ∪ eligible G u v) := by
    intro a ha
    by_cases hae : a = v
    · subst a; exact Finset.mem_insert_self _ _
    by_cases hv : G v a
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨ha,(mem_neighbors G).mpr hv⟩))
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      have hca := (mem_neighbors C).mp ha
      obtain ⟨x,_,_,hux,hax,_,_⟩ := t u a hca
      exact (mem_eligible G).mpr ⟨mono hca,hv,hae,fun hl => hl.2 x ⟨mono hux,mono hax⟩⟩
  have h := Finset.card_le_card hsub
  have h' := Finset.card_insert_le (a := v) (s := Y ∪ eligible G u v)
  have h'' := Finset.card_union_le (s := Y) (t := eligible G u v)
  change X.card = 5 at hc
  have hEq := Finset.eq_of_subset_of_card_le hY (show X.card ≤ Y.card by omega)
  change X ⊆ neighbors C u
  rw [←hEq]
  exact fun a ha => (Finset.mem_inter.mp ha).1

theorem eligible_independent_pair
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFreeLinks G) (u v : V) (hm : 3 ≤ (eligible G u v).card) :
    ∃ A ⊆ eligible G u v, 2 ≤ A.card ∧ Erdos151Ramsey.Independent G A := by
  let R (a b : V) : Prop := G u a ∧ G u b ∧ G a b
  letI : DecidableRel R := fun a b => inferInstanceAs (Decidable (G u a ∧ G u b ∧ G a b))
  have rt : Erdos151Ramsey.TriangleFree R :=
    fun a b c hab hbc hac => tf u a b c hab.1 hab.2.1 hbc.2.1 hab.2.2 hbc.2.2 hac.2.2
  have rs : ∀ {a b}, R a b → R b a := fun h => ⟨h.2.1,h.1,sym h.2.2⟩
  have ri : ∀ a, ¬ R a a := fun a h => irr a h.2.2
  obtain ⟨A,hA,hk,hi⟩ := Erdos151Ramsey.independent_two_of_three R rs ri rt _ hm
  refine ⟨A,hA,hk,?_⟩
  intro a ha b hb hab
  exact hi a ha b hb ⟨((mem_eligible G).mp (hA ha)).1,((mem_eligible G).mp (hA hb)).1,hab⟩

theorem eligible_singleton
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFreeLinks G) (mono : ∀ {a b}, C a b → G a b) (t : TwoTriangles C)
    (u v : V) (huv : C u v) :
    ∃ A ⊆ eligible G u v, 1 ≤ A.card ∧ Erdos151Ramsey.Independent G A := by
  obtain ⟨x,hx⟩ := eligible_nonempty G C sym tf mono t u v huv
  refine ⟨{x},Finset.singleton_subset_iff.mpr hx,by simp,?_⟩
  intro a ha b hb
  simp only [Finset.mem_singleton] at ha hb
  simpa [ha,hb] using irr x

/-- A core edge with ambient codegree five and budget seven must retain
all five common vertices in the core at each endpoint. -/
theorem tight_five_core_codegree
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (symC : ∀ {a b}, C a b → C b a) (tf : TriangleFreeLinks G)
    (mono : ∀ {a b}, C a b → G a b) (t : TwoTriangles C)
    (lower : ∀ R : Finset V, 41 ≤ R.card →
      ∃ P ⊆ R, 10 ≤ P.card ∧ Free (Forbidden G) (P : Set V))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (u v : V) (huv : C u v) (hu8 : 8 ≤ (neighbors C u).card) (hv8 : 8 ≤ (neighbors C v).card)
    (hfive : ambientCodeg G u v = 5)
    (budget : 40 + (neighbors G u).card + (neighbors G v).card ≤ Fintype.card V + 7) :
    ambientCodeg C u v = 5 := by
  have huv' : C v u := symC huv
  have hfive' : ambientCodeg G v u = 5 := by simpa [ambientCodeg, Finset.inter_comm] using hfive
  have nl (x y : V) (hh : C x y) : ¬ Lone G x y := by
    obtain ⟨z,_,_,hxz,hyz,_,_⟩ := t x y hh
    exact fun he => he.2 z ⟨mono hxz,mono hyz⟩
  have he (x y : V) (hxy : C x y) (hyx : C y x)
      (hfv : ambientCodeg G x y = 5)
      (hb : 40 + (neighbors G x).card + (neighbors G y).card ≤ Fintype.card V + 7) :
      (eligible G x y).card ≤ 2 := by
    by_contra! hn
    obtain ⟨A,hA,hAc,hAi⟩ := eligible_independent_pair G sym irr tf x y (by omega)
    obtain ⟨B,hB,hBc,hBi⟩ := eligible_singleton G C sym irr tf mono t y x hyx
    have pw : 41 + (neighbors G x).card + (neighbors G y).card ≤
         Fintype.card V + ((neighbors G x) ∩ (neighbors G y)).card + A.card + B.card := by
      unfold ambientCodeg at hfv
      omega
    obtain ⟨P,hPc,hf⟩ := adjacent_two_hub_price G sym irr x y (mono hxy) (nl x y hxy) A B
      (fun x hx => (mem_eligible G).mp (hA hx)) (fun x hx => (mem_eligible G).mp (hB hx))
      hAi hBi lower pw
    have := upper P hf
    omega
  have hL := all_ambient_common_core_left G C mono t u v hu8 hfive (he u v huv huv' hfive budget)
  have hb' : 40 + (neighbors G v).card + (neighbors G u).card ≤ Fintype.card V + 7 := by omega
  have hR := all_ambient_common_core_left G C mono t v u hv8 hfive' (he v u huv' huv hfive' hb')
  have hEq : neighbors G u ∩ neighbors G v = neighbors C u ∩ neighbors C v := by
    ext a
    constructor
    · intro h
      exact Finset.mem_inter.mpr ⟨hL h,hR (by simpa [Finset.inter_comm] using h)⟩
    · intro h
      obtain ⟨hu,hv⟩ := Finset.mem_inter.mp h
      exact Finset.mem_inter.mpr
        ⟨(mem_neighbors G).mpr (mono ((mem_neighbors C).mp hu)),(mem_neighbors G).mpr (mono ((mem_neighbors C).mp hv))⟩
  unfold ambientCodeg at hfive ⊢
  rwa [←hEq]

#print axioms tight_five_core_codegree
end Erdos151H12
