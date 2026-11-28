import H12AdjacentPrice
import H12TwoHubArithmetic
import RamseyExactNine

namespace Erdos151H12
open Erdős151

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

def TwoTriangles (C : V → V → Prop) : Prop :=
  ∀ u v, C u v → ∃ a b, a ≠ b ∧ C u a ∧ C v a ∧ C u b ∧ C v b

noncomputable def eligible (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun a => G u a ∧ ¬ G v a ∧ a ≠ v ∧ ¬ Lone G u a

theorem mem_eligible {u v a : V} :
    a ∈ eligible G u v ↔ G u a ∧ ¬ G v a ∧ a ≠ v ∧ ¬ Lone G u a := by
  classical
  simp [eligible]

def ambientCodeg (u v : V) : Nat := ((neighbors G u) ∩ (neighbors G v)).card

theorem core_overlap_has_two (mono : ∀ {a b}, C a b → G a b) (t : TwoTriangles C) (u v : V)
    (huv : C u v) : 2 ≤ ambientCodeg G u v := by
  obtain ⟨a,b,hab,hua,hva,hub,hvb⟩ := t u v huv
  have he : ({a,b} : Finset V) ⊆ (neighbors G u) ∩ (neighbors G v) := by
    refine Finset.insert_subset_iff.mpr ⟨?_,Finset.singleton_subset_iff.mpr ?_⟩
    · exact Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr (mono hua),(mem_neighbors G).mpr (mono hva)⟩
    · exact Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr (mono hub),(mem_neighbors G).mpr (mono hvb)⟩
  have h := Finset.card_le_card he
  change ({a,b} : Finset V).card ≤ ambientCodeg G u v at h
  rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hab),
    Finset.card_singleton] at h
  exact h

theorem eligible_card
    (mono : ∀ {a b}, C a b → G a b) (t : TwoTriangles C) (u v : V) :
    (neighbors C u).card ≤ 1 + ambientCodeg G u v + (eligible G u v).card := by
  let X := (neighbors G u) ∩ (neighbors G v)
  have hsub : neighbors C u ⊆ insert v (X ∪ eligible G u v) := by
    intro a ha
    by_cases hae : a = v
    · subst a; exact Finset.mem_insert_self _ _
    by_cases hv : G v a
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨(mem_neighbors G).mpr (mono ((mem_neighbors C).mp ha)),(mem_neighbors G).mpr hv⟩)
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      have hca := (mem_neighbors C).mp ha
      obtain ⟨x,_,_,hux,hax,_,_⟩ := t u a hca
      exact (mem_eligible G).mpr ⟨mono hca,hv,hae,fun hl => hl.2 x ⟨mono hux,mono hax⟩⟩
  have h := Finset.card_le_card hsub
  have h' := Finset.card_insert_le (a := v) (s := X ∪ eligible G u v)
  have h'' := Finset.card_union_le (s := X) (t := eligible G u v)
  change (X ∪ eligible G u v).card ≤ ambientCodeg G u v + (eligible G u v).card at h''
  omega

theorem eligible_nonempty
    (sym : ∀ {a b}, G a b → G b a) (tf : TriangleFreeLinks G)
    (mono : ∀ {a b}, C a b → G a b) (t : TwoTriangles C)
    (u v : V) (huv : C u v) :
    (eligible G u v).Nonempty := by
  obtain ⟨a,_,_,hua,hva,_,_⟩ := t u v huv
  obtain ⟨x,y,hxy,hux,hax,huy,hay⟩ := t u a hua
  have sub (j : V) (huj : C u j) (haj : C a j) (hne : j ≠ v) : j ∈ eligible G u v := by
    apply (mem_eligible G).mpr
    refine ⟨mono huj, ?_, hne, fun hl => hl.2 a ⟨mono hua,sym (mono haj)⟩⟩
    intro hvj
    exact tf u a j v (mono hua) (mono huj) (mono huv) (mono haj) (sym hvj) (sym (mono hva))
  by_cases e : x = v
  · exact ⟨y, sub y huy hay (fun eq => hxy (e.trans eq.symm))⟩
  · exact ⟨x,sub x hux hax e⟩

variable {G C}

theorem exists_alpha_floor (R : V → V → Prop) [DecidableRel R]
    (sym : ∀ {a b}, R a b → R b a) (irr : ∀ a, ¬ R a a)
    (tf : Erdos151Ramsey.TriangleFree R) (S : Finset V) (m : Nat) (hm : m ≤ S.card)
    (hn : S.Nonempty) :
    ∃ A ⊆ S, max 1 (alphaFloor m) ≤ A.card ∧ Erdos151Ramsey.Independent R A := by
  unfold alphaFloor
  by_cases h9 : 9 ≤ m
  · rw [ite_eq_left h9]
    simpa using Erdos151Ramsey.independent_four_of_nine R sym irr tf S (h9.trans hm)
  rw [ite_eq_right h9]
  by_cases h6 : 6 ≤ m
  · rw [ite_eq_left h6]
    simpa using Erdos151Ramsey.independent_three_of_six R sym irr tf S (h6.trans hm)
  rw [ite_eq_right h6]
  by_cases h3 : 3 ≤ m
  · rw [ite_eq_left h3]
    simpa using Erdos151Ramsey.independent_two_of_three R sym irr tf S (h3.trans hm)
  rw [ite_eq_right h3]
  obtain ⟨a,ha⟩ := hn
  refine ⟨{a},Finset.singleton_subset_iff.mpr ha,?_,?_⟩
  · split <;> simp
  · intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    simpa [hx,hy] using irr a

theorem eligible_independent (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : TriangleFreeLinks G) (mono : ∀ {a b}, C a b → G a b)
    (t : TwoTriangles C) (u v : V) (huv : C u v) :
    ∃ A ⊆ eligible G u v, eligibleFloor (neighbors C u).card (ambientCodeg G u v) ≤ A.card ∧
        Erdos151Ramsey.Independent G A := by
  let R (a b : V) : Prop := G u a ∧ G u b ∧ G a b
  letI : DecidableRel R := fun a b => inferInstanceAs (Decidable (G u a ∧ G u b ∧ G a b))
  have rt : Erdos151Ramsey.TriangleFree R :=
    fun a b c hab hbc hac => tf u a b c hab.1 hab.2.1 hbc.2.1 hab.2.2 hbc.2.2 hac.2.2
  have rs : ∀ {a b}, R a b → R b a := fun h => ⟨h.2.1,h.1,sym h.2.2⟩
  have ri : ∀ a, ¬ R a a := fun a h => irr a h.2.2
  have hn := eligible_nonempty G C sym tf mono t u v huv
  have hd := eligible_card G C mono t u v
  obtain ⟨A,hA,hk,hi⟩ := exists_alpha_floor R rs ri rt (eligible G u v)
    ((neighbors C u).card-1-ambientCodeg G u v) (by omega) hn
  refine ⟨A,hA,hk,?_⟩
  intro a ha b hb hab
  exact hi a ha b hb ⟨((mem_eligible G).mp (hA ha)).1,((mem_eligible G).mp (hA hb)).1,hab⟩

theorem adjacent_core_necessary
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (symC : ∀ {a b}, C a b → C b a) (tf : TriangleFreeLinks G)
    (mono : ∀ {a b}, C a b → G a b) (t : TwoTriangles C)
    (lower : ∀ R : Finset V, 41 ≤ R.card →
      ∃ P ⊆ R, 10 ≤ P.card ∧ Free (Forbidden G) (P : Set V))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (u v : V) (huv : C u v) :
    Fintype.card V + twoHubFloor (neighbors C u).card (neighbors C v).card (ambientCodeg G u v)
      ≤ 40 + (neighbors G u).card + (neighbors G v).card := by
  have heq : ambientCodeg G u v = ambientCodeg G v u := by
    simp [ambientCodeg, Finset.inter_comm]
  obtain ⟨A,hA,hAc,hAi⟩ := eligible_independent (G := G) (C := C) sym irr tf mono t u v huv
  obtain ⟨B,hB,hBc,hBi⟩ := eligible_independent (G := G) (C := C) sym irr tf mono t v u (symC (a := u) (b := v) huv)
  rw [←heq] at hBc
  have notLone : ¬ Lone G u v := by
    obtain ⟨x,_,_,hux,hvx,_,_⟩ := t u v huv
    exact fun h => h.2 x ⟨mono hux,mono hvx⟩
  by_contra! hbad
  unfold twoHubFloor at hbad
  have pw : 41 + (neighbors G u).card + (neighbors G v).card ≤
       Fintype.card V + ((neighbors G u) ∩ (neighbors G v)).card + A.card + B.card := by
    unfold ambientCodeg at hbad hAc hBc
    omega
  obtain ⟨P,hp,hf⟩ := adjacent_two_hub_price G sym irr u v (mono huv) notLone A B
    (fun x hx => (mem_eligible G).mp (hA hx))
    (fun x hx => (mem_eligible G).mp (hB hx))
    hAi hBi lower pw
  have := upper P hf
  omega

#print axioms eligible_nonempty
#print axioms eligible_independent
#print axioms adjacent_core_necessary
end Erdos151H12
