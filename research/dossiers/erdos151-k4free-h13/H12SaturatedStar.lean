import H12PairInsert
import Mathlib.Data.Finset.Card

namespace Erdos151H12
open Erdős151

variable {V : Type*} [DecidableEq V]
variable (G : V → V → Prop)

theorem lone_neighbors_nonadjacent (hs : ∀ {a b}, G a b → G b a)
    {u a b : V} (ha : Lone G u a) (hb : G u b) : ¬ G a b :=
  fun e => ha.2 b ⟨hb,e⟩

/-- Ambient neighbors of a saturated hub are precisely the indicated neighbors. -/
theorem saturated_hub_neighbors [Fintype V] [DecidableRel G] (u : V) (F : Finset V)
    (hF : ∀ x ∈ F, G u x)
    (hd : (Finset.univ.filter (G u)).card ≤ F.card)
    (x : V) (hx : x ∉ F) : ¬ G u x := by
  have hsub : F ⊆ Finset.univ.filter (G u) :=
    fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hF x hx⟩
  have he := Finset.eq_of_subset_of_card_le hsub hd
  intro hh
  exact hx (he ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)

theorem free_adjoin_independent
    (hs : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (S A : Finset V) (hS : Free (Forbidden G) (S : Set V))
    (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b)
    (hcross : ∀ a ∈ A, ∀ b ∈ S, ¬ G a b) :
    Free (Forbidden G) ((A ∪ S : Finset V) : Set V) := by
  induction A using Finset.induction_on with
  | empty => simpa using hS
  | @insert a T ha ih =>
    have ha' : a ∈ insert a T := Finset.mem_insert_self _ _
    have hs' := ih
      (fun u hu v hv => hA u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv))
      (fun u hu v hv => hcross u (Finset.mem_insert_of_mem hu) v hv)
    rw [Finset.insert_union, Finset.coe_insert]
    apply safe_insert_one G hs irr _ a hs'
    · intro x hx hn
      have hx' : x ∈ T ∪ S := hx
      rcases Finset.mem_union.mp hx' with ht | hss
      · exact hA a ha' x (Finset.mem_insert_of_mem ht) hn.1
      · exact hcross a ha' x hss hn.1
    · intro x hx _ _ hax
      have hx' : x ∈ T ∪ S := hx
      rcases Finset.mem_union.mp hx' with ht | hss
      · exact False.elim (hA a ha' x (Finset.mem_insert_of_mem ht) hax)
      · exact False.elim (hcross a ha' x hss hax)

theorem same_layer_exchange
    (hs : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (S : Finset V) (hS : Free (Forbidden G) (S : Set V)) (h10 : S.card = 10)
    (s t u₀ u₁ D a b : V) (hsS : s ∈ S) (htS : t ∈ S) (hst : s ≠ t)
    (hu₁ : u₁ ∉ S) (hD : D ∉ S) (ha : a ∉ S) (hb : b ∉ S)
    (huD : u₁ ≠ D) (hua : u₁ ≠ a) (hub : u₁ ≠ b)
    (hDa : D ≠ a) (hDb : D ≠ b) (hab : a ≠ b)
    (huS : ∀ x ∈ S, ¬ G u₁ x) (huDn : ¬ G u₁ D) (huan : ¬ G u₁ a) (hubn : ¬ G u₁ b)
    (hDs : Lone G s D) (hDt : Lone G t D) (has : Lone G s a) (hbt : Lone G t b)
    (h0a : Lone G u₀ a) (h0b : Lone G u₀ b)
    (hDS : ∀ x ∈ S, G D x → x = s ∨ x = t)
    (haS : ∀ x ∈ S, G a x → x = s) (hbS : ∀ x ∈ S, G b x → x = t) :
    ∃ T : Finset V, T.card = 12 ∧ Free (Forbidden G) (T : Set V) := by
  let R := (S.erase s).erase t
  let A : Finset V := {u₁,D,a,b}
  have hRs : R ⊆ S := fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
  have hRs' : s ∉ R := fun h => (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
  have hRt' : t ∉ R := Finset.notMem_erase _ _
  have hR : Free (Forbidden G) (R : Set V) := fun Z hZ hZR => hS Z hZ (fun x hx => hRs (hZR hx))
  have hcR : R.card = 8 := by
    have h := Finset.card_erase_add_one hsS
    have h' := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hst.symm,htS⟩)
    change R.card+1 = (S.erase s).card at h'
    omega
  have hcA : A.card = 4 := by
    change (insert u₁ (insert D (insert a ({b} : Finset V)))).card = 4
    rw [Finset.card_insert_of_notMem (by simp [huD,hua,hub]),
      Finset.card_insert_of_notMem (by simp [hDa,hDb]),
      Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
  have hAdj : ∀ x ∈ A, ∀ y ∈ A, ¬ G x y := by
    have hDA := lone_neighbors_nonadjacent G hs hDs has.1
    have hDB := lone_neighbors_nonadjacent G hs hDt hbt.1
    have hAB := lone_neighbors_nonadjacent G hs h0a h0b.1
    intro x hx y hy
    change x ∈ ({u₁,D,a,b} : Finset V) at hx
    change y ∈ ({u₁,D,a,b} : Finset V) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl
    all_goals
      first
      | exact irr _
      | exact huDn
      | exact huan
      | exact hubn
      | exact hDA
      | exact hDB
      | exact hAB
      | exact fun h => huDn (hs h)
      | exact fun h => huan (hs h)
      | exact fun h => hubn (hs h)
      | exact fun h => hDA (hs h)
      | exact fun h => hDB (hs h)
      | exact fun h => hAB (hs h)
  have hCross : ∀ x ∈ A, ∀ y ∈ R, ¬ G x y := by
    intro x hx y hy hxy
    change x ∈ ({u₁,D,a,b} : Finset V) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact huS y (hRs hy) hxy
    · rcases hDS y (hRs hy) hxy with rfl|rfl
      · exact hRs' hy
      · exact hRt' hy
    · have h := haS y (hRs hy) hxy
      subst y
      exact hRs' hy
    · have h := hbS y (hRs hy) hxy
      subst y
      exact hRt' hy
  have hd : Disjoint A R := Finset.disjoint_left.mpr (by
    intro x hx hr
    change x ∈ ({u₁,D,a,b} : Finset V) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact hu₁ (hRs hr)
    · exact hD (hRs hr)
    · exact ha (hRs hr)
    · exact hb (hRs hr))
  exact ⟨A ∪ R, by rw [Finset.card_union_of_disjoint hd, hcA, hcR],
    free_adjoin_independent G hs irr R A hR hAdj hCross⟩

#print axioms saturated_hub_neighbors
#print axioms same_layer_exchange
end Erdos151H12
