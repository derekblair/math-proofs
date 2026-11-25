import Mathlib

/-! # Three-vertex rigidity and gap from global edge maximality in girth-5 graphs (G5-001) -/

open Finset

namespace Girth5Floor3v

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Girth5Graph (V : Type*) where
  adj : V → V → Prop
  decAdj : DecidableRel adj
  symm : ∀ x y, adj x y → adj y x
  irrefl : ∀ x, ¬ adj x x
  noTri : ∀ a b c, adj a b → adj b c → adj c a → False
  noC4 : ∀ a b c d, adj a b → adj b c → adj c d → adj d a → (a = c ∨ b = d)

instance (G : Girth5Graph V) : DecidableRel G.adj := G.decAdj

def N (G : Girth5Graph V) (x : V) : Finset V := Finset.univ.filter (G.adj x)

def W (G : Girth5Graph V) (u v w : V) : Finset V := ({u, v, w} : Finset V)ᶜ

def P (G : Girth5Graph V) (u v w : V) : Finset (V × V) :=
  letI : DecidablePred (fun p : V × V => G.adj p.1 p.2) := fun p => G.decAdj p.1 p.2
  ({(u, v), (u, w), (v, w)} : Finset (V × V)).filter fun p => G.adj p.1 p.2

def IsH3Clique (G : Girth5Graph V) (u v w : V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ G.adj x y ∧ ∀ z ∈ W G u v w, ¬ (G.adj x z ∧ G.adj z y)

structure IsFeasible (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V)) : Prop where
  attachA : A' ⊆ W G u v w
  attachB : B' ⊆ W G u v w
  attachC : C' ⊆ W G u v w
  cliqueA : IsH3Clique G u v w A'
  cliqueB : IsH3Clique G u v w B'
  cliqueC : IsH3Clique G u v w C'
  crossAB : (u, v) ∈ P' → ∀ x ∈ A', ∀ y ∈ B', ¬ G.adj x y
  crossAC : (u, w) ∈ P' → ∀ x ∈ A', ∀ y ∈ C', ¬ G.adj x y
  crossBC : (v, w) ∈ P' → ∀ x ∈ B', ∀ y ∈ C', ¬ G.adj x y
  interAB : (A' ∩ B').card ≤ 1
  interBC : (B' ∩ C').card ≤ 1
  interAC : (A' ∩ C').card ≤ 1
  disjointAB : (u, v) ∈ P' → A' ∩ B' = ∅
  disjointAC : (u, w) ∈ P' → A' ∩ C' = ∅
  disjointBC : (v, w) ∈ P' → B' ∩ C' = ∅
  internal : P' ⊆ {(u, v), (u, w), (v, w)}
  internalTriangle : ¬ ((u, v) ∈ P' ∧ (u, w) ∈ P' ∧ (v, w) ∈ P')
  pathAB : (u, w) ∈ P' → (v, w) ∈ P' → A' ∩ B' = ∅
  pathAC : (u, v) ∈ P' → (v, w) ∈ P' → A' ∩ C' = ∅
  pathBC : (u, v) ∈ P' → (u, w) ∈ P' → B' ∩ C' = ∅

def score (A' B' C' : Finset V) (P' : Finset (V × V)) : ℕ :=
  A'.card + B'.card + C'.card + P'.card

noncomputable instance feasDec (G : Girth5Graph V) (u v w : V) :
    DecidablePred (fun m : Finset V × Finset V × Finset V × Finset (V × V) =>
      IsFeasible G u v w m.1 m.2.1 m.2.2.1 m.2.2.2) :=
  fun m => Classical.propDecidable _

noncomputable def feasibleMoves (G : Girth5Graph V) (u v w : V) :
    Finset (Finset V × Finset V × Finset V × Finset (V × V)) :=
  Finset.univ.filter fun m => IsFeasible G u v w m.1 m.2.1 m.2.2.1 m.2.2.2

noncomputable def scores (G : Girth5Graph V) (u v w : V) : Finset ℕ :=
  (feasibleMoves G u v w).image fun m => score m.1 m.2.1 m.2.2.1 m.2.2.2

def D (G : Girth5Graph V) (u v w : V) : ℕ :=
  (N G u).card + (N G v).card + (N G w).card - (P G u v w).card

theorem scores_nonempty (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) : (scores G u v w).Nonempty := by
  sorry

def Girth5Graph.toSimpleGraph (G : Girth5Graph V) : SimpleGraph V where
  Adj := G.adj
  symm := ⟨fun _ _ h => G.symm _ _ h⟩
  loopless := ⟨G.irrefl⟩

noncomputable def edgeCount (G : Girth5Graph V) : ℕ := by
  classical
  exact G.toSimpleGraph.edgeFinset.card

def IsExtremal (G : Girth5Graph V) : Prop :=
  ∀ H : Girth5Graph V, edgeCount H ≤ edgeCount G

theorem score_le_D_of_extremal (G : Girth5Graph V) (u v w : V)
    (A' B' C' : Finset V) (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hG : IsExtremal G) (h : IsFeasible G u v w A' B' C' P') :
    score A' B' C' P' ≤ D G u v w := by
  sorry

theorem three_v_rigidity_of_extremal (G : Girth5Graph V) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hG : IsExtremal G) :
    (scores G u v w).max' (scores_nonempty G u v w huv huw hvw) = D G u v w := by
  sorry

theorem three_v_gap_of_extremal (G : Girth5Graph V) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hG : IsExtremal G) :
    ((scores G u v w).max' (scores_nonempty G u v w huv huw hvw) : ℤ) -
      (D G u v w : ℤ) - 1 = -1 := by
  sorry

end Girth5Floor3v
