import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

open scoped BigOperators

namespace QuorumMinimum

noncomputable def ec {V : Type} (G : SimpleGraph V) : Nat := Nat.card G.edgeSet

theorem ec_eq {V : Type} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    ec G = G.edgeFinset.card := by
  rw [ec, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]

theorem density_step (n e d q : Nat) (hn : 3 ≤ n) (h : 8*e < n*(n-1))
    (hd : 2*e ≤ n*d) (hed : q+d=e) :
    8*q < (n-1)*(n-2) := by
  have pos : 0 < n-2 := by omega
  have h1 := Nat.mul_lt_mul_of_pos_right h pos
  have h2 := Nat.mul_le_mul_left 8 hd
  have en := congrArg (fun x : Nat => 8*n*x) hed
  have eN := congrArg (fun x : Nat => 8*e*x) (show n-2+2=n by omega)
  have lt : n*(8*q)<n*((n-1)*(n-2)) := by nlinarith
  exact Nat.lt_of_mul_lt_mul_left lt

theorem exists_lower_density_delete {V : Type} [Fintype V]
    (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (below : 8*ec G < Fintype.card V*(Fintype.card V-1)) :
    ∃ x : V, 8*ec (G.induce (({x} : Set V)ᶜ)) <
      (Fintype.card V-1)*(Fintype.card V-2) := by
  classical
  have hnE : (Finset.univ : Finset V).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ]
    omega
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ (fun x => G.degree x) hnE
  have hd : 2*ec G ≤ Fintype.card V*G.degree x := by
    rw [ec_eq,←G.sum_degrees_eq_twice_card_edges]
    calc
      _ ≤ ∑ _ : V, G.degree x := Finset.sum_le_sum (fun w hw => hx w hw)
      _ = _ := by simp
  have hi : ec (G.induce (({x} : Set V)ᶜ)) = ec G-G.degree x := by
    simp only [ec_eq, G.card_edgeFinset_induce_compl_singleton,
      G.card_edgeFinset_deleteIncidenceSet]
  have de : G.degree x ≤ ec G := by
    rw [ec_eq, ←G.card_incidenceFinset_eq_degree]
    exact Finset.card_le_card (G.incidenceFinset_subset x)
  exact ⟨x,density_step _ _ _ _ hn below hd (by rw [hi]; omega)⟩

theorem density_lift {V : Type} (G : SimpleGraph V) (t : Nat) (ht : 2≤t)
    (hbase : ∀ (W : Type) [Fintype W] (e : W ↪ V), Fintype.card W=t →
      Fintype.card W*(Fintype.card W-1) ≤ 8*ec (G.comap e)) :
    ∀ (W : Type) [Fintype W] (e : W ↪ V), t≤Fintype.card W →
      Fintype.card W*(Fintype.card W-1) ≤ 8*ec (G.comap e) := by
  classical
  have aux : ∀ m : Nat, ∀ (W : Type) [Fintype W] (e : W ↪ V),
      Fintype.card W=m → t≤m →
      Fintype.card W*(Fintype.card W-1) ≤ 8*ec (G.comap e) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro W _ e wm le
      by_cases eq : m=t
      · exact hbase W e (wm.trans eq)
      by_contra! below
      obtain ⟨x,low⟩ := exists_lower_density_delete (G.comap (e : W → V)) (by omega) below
      let Y := (({x} : Set W)ᶜ : Set W)
      let inc : Y ↪ W := Function.Embedding.subtype _
      have cY : Fintype.card Y = Fintype.card W-1 := by
        dsimp [Y]
        rw [Fintype.card_compl_set]
        congr 1
      have strong := ih (Fintype.card Y) (by omega) Y (inc.trans e) rfl (by omega)
      change Fintype.card Y*(Fintype.card Y-1) ≤
        8*ec ((G.comap (e : W → V)).induce Y) at strong
      rw [cY, show Fintype.card W-1-1=Fintype.card W-2 by omega] at strong
      exact (not_lt_of_ge strong) low
  intro W _ e ne
  exact aux _ W e rfl ne

#print axioms density_lift
#print axioms density_step
#print axioms exists_lower_density_delete

end QuorumMinimum
