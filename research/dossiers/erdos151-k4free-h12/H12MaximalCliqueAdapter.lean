import MaximalClique
import RamseyPullback
import CoreExtract
import Mathlib.Data.Fintype.EquivFin

namespace Erdos151H12
open Erdős151

variable {V : Type*} [Fintype V]

/-- H(n)≥k, expressed directly as the universal triangle-free independence
statement on the same finite vertex type. -/
def TriangleIndependentAtLeast (k : Nat) (V : Type*) [Fintype V] : Prop :=
  ∀ R : V → V → Prop, (∀ {a b}, R a b → R b a) → (∀ a, ¬ R a a) →
      Erdos151Ramsey.TriangleFree R →
      ∃ S : Finset V, k ≤ S.card ∧ Erdos151Ramsey.Independent R S

theorem free_of_not_ramsey (G : V → V → Prop) (k : Nat)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (h : TriangleIndependentAtLeast k V) (safe : ¬ BikovLocal.Ramsey G) :
    ∃ S : Finset V, k ≤ S.card ∧ Free (Forbidden G) (S : Set V) := by
  classical
  unfold BikovLocal.Ramsey at safe
  push Not at safe
  obtain ⟨c,cs,good⟩ := safe
  have va a b d (ab : G a b) (bd : G b d) (ad : G a d) :
      ¬ (c a b = c b d ∧ c a b = c a d) := by
    intro h
    exact good a b d ab bd (sym ad) ⟨h.1,h.1.symm.trans (h.2.trans (cs a d))⟩
  let R := RedPlus G c
  have rs {a b : V} (hab : R a b) : R b a := by
    refine ⟨sym hab.1, ?_⟩
    rcases hab.2 with h | h
    · exact Or.inl ((cs a b).symm.trans h)
    · exact Or.inr ⟨sym h.1, fun x hx => h.2 x ⟨hx.2,hx.1⟩⟩
  have ri a (ha : R a a) := irr a ha.1
  have rt : Erdos151Ramsey.TriangleFree R := redPlus_triangleFree G c sym va
  obtain ⟨T,ht,hind⟩ := h R rs ri rt
  exact ⟨T,ht,independent_redPlus_free G c va (T : Set V) hind⟩

theorem free_set_to_maximal_clique_transversal (G : V → V → Prop) (k : Nat)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G) (S : Finset V)
    (hS : k ≤ S.card) (hfree : Free (Forbidden G) (S : Set V)) :
    ∃ T : Finset V, T.card ≤ Fintype.card V - k ∧
      ∀ C, MaximalNontrivialClique G C → ∃ x ∈ C, x ∈ T := by
  classical
  let T := Finset.univ \ S
  refine ⟨T, ?_, ?_⟩
  · dsimp only [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  · have hit := (free_iff_complement_hits G sym irr link (S : Set V)).mp hfree
    intro C hc
    obtain ⟨x,hx,hnot⟩ := hit C hc
    exact ⟨x,hx,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnot⟩⟩

theorem triangle_independence_forces_large_of_witness (k m : Nat)
    (H : TriangleIndependentAtLeast k V)
    (wit : ∃ R : Fin m → Fin m → Prop,
      (∀ a b, R a b → R b a) ∧ (∀ a, ¬ R a a) ∧ Erdos151Ramsey.TriangleFree R ∧
      ∀ S : Finset (Fin m), Erdos151Ramsey.Independent R S → S.card < k) :
    m < Fintype.card V := by
  classical
  by_contra! hs
  obtain ⟨R,sym,irr,tf,cap⟩ := wit
  let f : V ↪ Fin m := (Fintype.equivFin V).toEmbedding.trans
    ⟨(fun i => ⟨i.val,i.isLt.trans_le hs⟩), fun _ _ h => Fin.ext (congrArg (fun j : Fin m => j.val) h)⟩
  obtain ⟨T,hT,hI⟩ := H (fun a b => R (f a) (f b))
    (fun {_ _} h => sym _ _ h) (fun a => irr (f a))
    (Erdos151Ramsey.pullback_triangleFree f R tf)
  have hI' : Erdos151Ramsey.Independent R (T.map f) := by
    intro a ha b hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hb
    exact hI x hx y hy
  have hh := cap _ hI'
  rw [Finset.card_map] at hh
  omega

theorem k4free_transversal_from_ramsey_case (G : V → V → Prop) (k : Nat)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G) (H : TriangleIndependentAtLeast k V)
    (ramseyCase : BikovLocal.Ramsey G →
      ∃ S : Finset V, k ≤ S.card ∧ Free (Forbidden G) (S : Set V)) :
    ∃ T : Finset V, T.card ≤ Fintype.card V - k ∧
      ∀ C, MaximalNontrivialClique G C → ∃ x ∈ C, x ∈ T := by
  have h : ∃ S : Finset V, k ≤ S.card ∧ Free (Forbidden G) (S : Set V) := by
    by_cases r : BikovLocal.Ramsey G
    · exact ramseyCase r
    · exact free_of_not_ramsey G k sym irr H r
  obtain ⟨S,hS,hFree⟩ := h
  exact free_set_to_maximal_clique_transversal G k sym irr link S hS hFree

#print axioms free_of_not_ramsey
#print axioms triangle_independence_forces_large_of_witness
#print axioms k4free_transversal_from_ramsey_case
end Erdos151H12
