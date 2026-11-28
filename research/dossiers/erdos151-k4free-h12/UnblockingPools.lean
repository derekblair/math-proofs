import UnblockingOwners
import Mathlib.Data.Finset.SDiff

namespace Erdős151

variable {V : Type*} [DecidableEq V]

def Independence (G : V → V → Prop) (X : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ¬ G x y

def FreeCap (G : V → V → Prop) (cap : ℕ) : Prop :=
  ∀ T : Finset V, Free (Forbidden G) (T : Set V) → T.card ≤ cap

theorem independent_extensions_count {G : V → V → Prop} {cap : ℕ}
    (sym : ∀ {a b}, G a b → G b a)
    (hcap : FreeCap G cap)
    (T X : Finset V) (dis : Disjoint T X) (hT : Free (Forbidden G) T)
    (ind : Independence G X) (hadd : ∀ x ∈ X, Free (Forbidden G) (insert x ↑T)) :
    T.card + X.card ≤ cap := by
  classical
  have hfree := free_add_independent (Forbidden G) G (T : Set V) (X : Set V)
    (fun A hA u hu v hv hn => forbidden_clique G sym A hA u v hu hv hn) hT ind hadd
  have h := hcap (T ∪ X) (by simpa only [Finset.coe_union] using hfree)
  rwa [Finset.card_union_of_disjoint dis] at h

theorem private_ext_card {G : V → V → Prop} {cap : ℕ}
    (sym : ∀ {a b}, G a b → G b a)
    (hcap : FreeCap G cap)
    (S X : Finset V) (dis : Disjoint S X) (hS : Free (Forbidden G) S)
    (ind : Independence G X) {u : V} (hu : u ∈ S)
    (hadd : ∀ x ∈ X, u ∈ ps (G := G) S x) :
    S.card - 1 + X.card ≤ cap := by
  classical
  have sub : S.erase u ⊆ S := Finset.erase_subset _ _
  have hd : Disjoint (S.erase u) X :=
    Finset.disjoint_left.mpr (fun _ ha hb => Finset.disjoint_left.mp dis (sub ha) hb)
  have hf : Free (Forbidden G) (↑(S.erase u) : Set V) :=
    fun A hA hs => hS A hA (fun v hv => sub (hs hv))
  have ha : ∀ x ∈ X, Free (Forbidden G) (insert x (↑(S.erase u) : Set V)) := by
    intro x hx
    simpa only [Finset.coe_erase] using
      ((mem_ps (G := G) S x).mp (hadd x hx)).2
  have h := independent_extensions_count (G := G) sym hcap (S.erase u) X hd hf ind ha
  rwa [Finset.card_erase_of_mem hu] at h

noncomputable def rowPrivate (G : V → V → Prop)
    (S E : Finset V) (u : V) : Finset V := by
  classical
  exact E.filter (fun x => u ∈ ps (G := G) S x)

noncomputable def rowPrivateLone (G : V → V → Prop)
    (S E : Finset V) (u : V) : Finset V := by
  classical
  exact E.filter (fun x => u ∈ qs (G := G) S x)

theorem rowPrivate_neighbor {G : V → V → Prop}
    (sym : ∀ {a b}, G a b → G b a)
    (S E : Finset V) (dis : Disjoint S E) (hS : Free (Forbidden G) S)
    (blocked : ∀ x ∈ E, ¬ Free (Forbidden G) (insert x ↑S)) {u x : V}
    (hu : u ∈ S) (hx : x ∈ rowPrivate G S E u) : G u x := by
  classical
  have hx' : x ∈ E ∧ u ∈ ps (G := G) S x := by
    exact Finset.mem_filter.mp hx
  have hne : x ≠ u := by
    intro he
    subst x
    exact Finset.disjoint_left.mp dis hu hx'.1
  have ha := private_adjacent_to_owner (Forbidden G) G (S : Set V) x u hne
    (fun A hA a ha b hb hn => forbidden_clique G sym A hA a b ha hb hn)
    hS ((mem_ps (G := G) S x).mp hx'.2).2 (blocked x hx'.1)
  exact sym ha

theorem rowPrivateLone_subset {G : V → V → Prop} (S E : Finset V) (u : V) :
    rowPrivateLone G S E u ⊆ rowPrivate G S E u := by
  classical
  intro x hx
  have hr : x ∈ E ∧ u ∈ qs (G := G) S x := Finset.mem_filter.mp hx
  have hp := (mem_qs (G := G) S x).mp hr.2
  exact Finset.mem_filter.mpr ⟨hr.1,(mem_ps (G := G) S x).mpr ⟨hp.1,hp.2.2⟩⟩

theorem rowPrivateLone_isolated {G : V → V → Prop}
    (sym : ∀ {a b}, G a b → G b a)
    (S E : Finset V) (dis : Disjoint S E) (hS : Free (Forbidden G) S)
    (blocked : ∀ x ∈ E, ¬ Free (Forbidden G) (insert x ↑S)) {u x y : V}
    (hu : u ∈ S) (hx : x ∈ rowPrivateLone G S E u)
    (hy : y ∈ rowPrivate G S E u) : ¬ G x y := by
  classical
  have hr : x ∈ E ∧ u ∈ qs (G := G) S x := Finset.mem_filter.mp hx
  have hp := (mem_qs (G := G) S x).mp hr.2
  exact private_lone_isolated (G := G) sym hp.2.1
    (sym (rowPrivate_neighbor (G := G) sym S E dis hS blocked hu hy))

#print axioms rowPrivate_neighbor
#print axioms rowPrivateLone_subset
#print axioms rowPrivateLone_isolated
#print axioms independent_extensions_count
#print axioms private_ext_card
end Erdős151
