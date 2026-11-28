import ActualLocalSplit

namespace Erdős151.H13
open Erdős151.H12 Erdős151.H12.Wagner

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev LinkDeletionConnected (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v : V, ∀ U : Finset (Lk G v), U.card ≤ 2 →
  ∀ a b : Lk G v, a ∉ U → b ∉ U →
    Relation.ReflTransGen (fun x y => G.Adj x.val y.val ∧ x ∉ U ∧ y ∉ U) a b

theorem actual_host_connected (G : SimpleGraph V) [DecidableRel G.Adj]
    (conn : ∀ a b : V, Relation.ReflTransGen G.Adj a b) :
    ∀ a b : V, Relation.ReflTransGen (hostRel (edgeRost G)) a b := by
  intro a b
  induction conn a b with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail ((host_iff_of_ne G h.ne).mpr h)

/-- Actual links connected after any two deletions yield host connectivity
after any three deletions. Link size and link isomorphism type may vary. -/
theorem actual_avoid_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (conn : ∀ a b : V, Relation.ReflTransGen G.Adj a b)
    (links : LinkDeletionConnected G) :
    ∀ S : Finset V, S.card ≤ 3 → ∀ a b : V, a ∉ S → b ∉ S →
      Relation.ReflTransGen (fun x y => hostRel (edgeRost G) x y ∧ x ∉ S ∧ y ∉ S) a b := by
  classical
  apply WagnerBypass.avoid_three (hostRel (edgeRost G)) (actual_host_connected G conn)
  intro v S hS x y hx hy hxs hys hxv hyv
  let a : Lk G v := ⟨x,((host_iff_of_ne G hxv).mp hx).symm⟩
  let b : Lk G v := ⟨y,(host_iff_of_ne G hyv.symm).mp hy⟩
  let U : Finset (Lk G v) := Finset.univ.filter (fun z=>z.val∈S)
  let emb : Lk G v ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have obs : U.card ≤ S.card := by
    rw [←Finset.card_map emb]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hz
    exact (Finset.mem_filter.mp hp).2
  have pl := links v U (obs.trans hS) a b (by simp [U,a,hxs]) (by simp [U,b,hys])
  have trans {a b : Lk G v} (pp : Relation.ReflTransGen
      (fun x y : Lk G v => G.Adj x.val y.val ∧ x∉U ∧ y∉U) a b) :
      Relation.ReflTransGen (WagnerBypass.restrict (hostRel (edgeRost G))
        (fun u => u ∉ S ∧ u ≠ v)) a.val b.val := by
    induction pp with
    | refl => exact .refl
    | @tail z t _ h ih =>
      have h1 := h.2.1
      have h2 := h.2.2
      simp only [U,Finset.mem_filter,Finset.mem_univ,true_and] at h1 h2
      exact .tail ih ⟨(host_iff_of_ne G h.1.ne).mpr h.1,
        ⟨h1,z.property.ne.symm⟩,
        ⟨h2,t.property.ne.symm⟩⟩
  exact trans pl

#print axioms actual_avoid_three
end Erdős151.H13
