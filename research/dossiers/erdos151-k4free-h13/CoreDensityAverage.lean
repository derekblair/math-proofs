import CoreLinkDensity
import CoreAverage

open scoped BigOperators
namespace Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem actual_density_forces_twelve (G : SimpleGraph V) [DecidableRel G.Adj]
    (ramsey : BikovLocal.Ramsey G.Adj)
    (minimal : ∀ H : V→V→Prop, BikovLocal.Sub H G.Adj → BikovLocal.Sym H →
      ∀ a b, G.Adj a b → ¬H a b → ¬BikovLocal.Ramsey H)
    (sd : ∀ w, (Upper.nbr G.Adj w).Nonempty → 8 ≤ (Upper.nbr G.Adj w).card)
    (loc : ∀ w, (Upper.nbr G.Adj w).Nonempty →
      let d := (Upper.nbr G.Adj w).card
      let e := ((G.cliqueFinset 3).filter (fun t => w∈t)).card
      2*e ≤ 3*d ∧ (9≤d → 2*e < 3*d)) :
    ∀ w, (Upper.nbr G.Adj w).Nonempty →
      (Upper.nbr G.Adj w).card=8 ∧
        (∑ v∈Upper.nbr G.Adj w, ((Upper.nbr G.Adj w).filter (G.Adj v)).card)=24 := by
  classical
  let S := Finset.univ.filter (fun w => (Upper.nbr G.Adj w).Nonempty)
  let deg := fun w => (Upper.nbr G.Adj w).card
  let links := fun w => ((G.cliqueFinset 3).filter (fun t => w∈t)).card
  have sup (w : V) : w∈S ↔ (Upper.nbr G.Adj w).Nonempty := by simp [S]
  have outD (w : V) (hw : w∉S) : deg w = 0 := by
    by_contra h
    exact hw ((sup w).mpr (Finset.card_pos.mp (by dsimp [deg] at h; omega)))
  have outL (w : V) (hw : w∉S) : links w=0 := by
    have hz := outD w hw
    have he : Upper.nbr G.Adj w = ∅ := Finset.card_eq_zero.mp hz
    have hd := directed_link_sum G w
    rw [he,Finset.sum_empty] at hd
    change 0 = 2*links w at hd
    omega
  have dS : (∑ w ∈ S, deg w) = 2*(G.cliqueFinset 2).card := by
    rw [← handshake_clique_finset G]
    exact Finset.sum_subset (Finset.subset_univ _) (fun w _ hm => outD w hm)
  have lS : (∑ w ∈ S, links w) = 3*(G.cliqueFinset 3).card := by
    rw [←sum_vertex_triangle_counts G]
    exact Finset.sum_subset (Finset.subset_univ _) (fun w _ hm => outL w hm)
  have h := minimal_ramsey_triangle_density G ramsey minimal
  have dens : 3*(∑ w∈S,deg w) ≤ 2*(∑ w∈S,links w) := by rw [dS,lS]; omega
  intro w hw
  have memw := (sup w).mpr hw
  have pt (v : V) (hv : v∈S) : 2*links v ≤ 3*deg v := (loc v ((sup v).mp hv)).1
  have ee : 2*links w = 3*deg w := by
    by_contra he
    have lt : 2*links w < 3*deg w := lt_of_le_of_ne (pt w memw) he
    have total := Finset.sum_lt_sum pt ⟨w,memw,lt⟩
    rw [←Finset.mul_sum,←Finset.mul_sum] at total
    exact (not_lt_of_ge dens) total
  have d8 : deg w=8 := by
    have hd : 8≤deg w := sd w hw
    by_contra hne
    have h9 : 9≤deg w := by omega
    have ht := (loc w hw).2 h9
    change 2*links w < 3*deg w at ht
    omega
  have l12 : links w=12 := by omega
  refine ⟨d8,?_⟩
  rw [directed_link_sum G w, show ((G.cliqueFinset 3).filter (fun t => w∈t)).card=12 from l12]

#print axioms actual_density_forces_twelve
end Erdős151.H12
