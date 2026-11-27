import BracePort

namespace FolkmanB4.Tight
open Finset Critical
universe u
variable {L V : Type u} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

def Heawood (I : L → V → Prop) : Prop :=
  ∃ r : Fin 7 ≃ L, ∃ c : Fin 7 ≃ V, ∀ i j, I (r i) (c j) ↔ Fano.inc i j

def PSignable (I : L → V → Prop) : Prop :=
  ∃ base : V ≃ L, ∃ w : L → V → ℤˣ, ∃ z : ℤˣ,
    ∀ m : V ≃ L, (∀ i, I (m i) i) →
      Equiv.Perm.sign (m.trans base.symm) * (∏ v : V, w (m v) v) = z

/-- External input corresponding to the published Pfaffian brace square
dichotomy. This definition is a hypothesis, not an axiom declaration. -/
def BraceDichotomy : Prop :=
  ∀ (L V : Type u) [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]
    (I : L → V → Prop) [DecidableRel I],
    (∀ l, pts I l=3) → (∀ v, lns I v=3) → 3≤Fintype.card V → NoSmallCut I →
    PSignable I → Heawood I ∨ ∃ s t : Square I, Disjoint s.edges t.edges

theorem signable_of_constant (I : L → V → Prop) (k m : V ≃ L)
    (M : ∀ v, I (m v) v)
    (signs : ∀ s t : V ≃ L, (∀ i, I (s i) i) → (∀ i, I (t i) i) →
      pSign (s.trans k.symm)=pSign (t.trans k.symm)) :
    PSignable I := by
  refine ⟨k,fun _ _ => 1,Equiv.Perm.sign (m.trans k.symm),fun s S => ?_⟩
  simp only [prod_const_one,mul_one]
  have H := signs s m S M
  unfold pSign at H
  exact Units.ext (Int.cast_injective H)

theorem signable_of_port (I : L → V → Prop) (A : L → Bool) (B : V → Bool)
    (covered : Covered I) (tight : Tight I A B) (k : V ≃ L)
    (S : ∀ s t : V ≃ L, (∀ i, I (s i) i) → (∀ i, I (t i) i) →
      pSign (s.trans k.symm)=pSign (t.trans k.symm))
    (q : Option (In B) ≃ In A) :
    PSignable (pointsContraction I A B) := by
  obtain ⟨s,hs⟩ := port_signing I A B covered tight k S q
  refine ⟨q,fun l v => if v=none then s l else 1,1,fun m M => ?_⟩
  have e : (∏ v : Option (In B), if v=none then s (m v) else 1)=s (m none) := by
    apply prod_eq_single none
    · intro a _ h
      simp [h]
    · simp
  rw [e]
  exact hs m M

theorem heawood_oriented (I : L → V → Prop) (A : Finset L) (B : Finset V)
    [DecidableRel I] (ext : BraceDichotomy.{u})
    (row : ∀ l, pts I l=3) (col : ∀ v, lns I v=3)
    (H : Nontrivial A B)
    (tight : Tight I (fun l => decide (l∈A)) (fun v => decide (v∈B)))
    (direction : Inward I (fun l => decide (l∈A)) (fun v => decide (v∈B)))
    (minimal : ∀ a b, Nontrivial a b →
        Tight I (fun l => decide (l∈a)) (fun v => decide (v∈b)) →
        shore A B ≤ shore a b)
    (k : V ≃ L)
    (signs : ∀ s t : V ≃ L, (∀ i, I (s i) i) → (∀ i, I (t i) i) →
      pSign (s.trans k.symm)=pSign (t.trans k.symm)) :
    Heawood (pointsContraction I (fun l => decide (l∈A)) (fun v => decide (v∈B))) := by
  have m := regular_perfect_matching I (by decide : 0<3) row col
  have cover : Covered I := fun _ _ h => regular_covers I row col h
  have size := (contraction_size I A B H direction tight col m).2
  obtain ⟨d,r,c,_⟩ := cubic_contraction I A B H direction tight minimal row col m
  letI := d
  obtain ⟨f,hf⟩ := m
  obtain ⟨q,hq,_⟩ := project_original I _ _ direction tight f hf
  have small := minimal_contraction_no_cut I A B H direction tight minimal
  rcases ext _ _ _ r c size small (signable_of_port I _ _ cover tight k signs q) with e|e
  · exact e
  · exact False.elim (no_disjoint_quotient_squares I _ _ cover tight k signs small ⟨q,hq⟩
      (le_of_eq (c none)) e)

#print axioms signable_of_port
#print axioms heawood_oriented
end FolkmanB4.Tight
