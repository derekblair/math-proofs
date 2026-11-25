import Result
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Wow271

open Wow268
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def MaxDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Prop :=
  ∀ w : V, G.degree w ≤ G.degree v

lemma max_pair_dist_two (hc : G.Connected) {S : Finset V} (hS : TotalDominating G S)
    (hcard : S.card=2) {a b : V} (ha : MaxDegree G a) (hb : MaxDegree G b) :
    G.dist a b ≤ 2 := by
  classical
  obtain ⟨u,v,huv,hEq⟩ := Finset.card_eq_two.mp hcard
  have hCover : G.neighborFinset u ∪ G.neighborFinset v = Finset.univ := by
    ext w
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨z,hz,hwz⟩ := hS w
    rw [hEq,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl
    · exact Finset.mem_union_left _ ((G.mem_neighborFinset _ _).mpr hwz.symm)
    · exact Finset.mem_union_right _ ((G.mem_neighborFinset _ _).mpr hwz.symm)
  have hLarge := Finset.card_union_le (G.neighborFinset u) (G.neighborFinset v)
  rw [hCover, Finset.card_univ, G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hLarge
  by_contra! hf
  have hab : ¬G.Adj a b := fun e => by
    have h := SimpleGraph.dist_eq_one_iff_adj.mpr e
    omega
  have hDis : Disjoint (G.neighborFinset a) (G.neighborFinset b) := by
    apply Finset.disjoint_left.mpr
    intro z hza hzb
    have haz := SimpleGraph.dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp hza)
    have hzb' := SimpleGraph.dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp hzb).symm
    have ht := hc.dist_triangle (u:=a) (v:=z) (w:=b)
    omega
  have haNot : a ∉ G.neighborFinset a ∪ G.neighborFinset b := by
    simp only [Finset.mem_union, G.mem_neighborFinset, G.irrefl, false_or]
    exact fun e => hab e.symm
  have ht := Finset.card_le_card (Finset.subset_univ (insert a (G.neighborFinset a ∪ G.neighborFinset b)))
  rw [Finset.card_insert_of_notMem haNot, Finset.card_union_of_disjoint hDis,Finset.card_univ,
    G.card_neighborFinset_eq_degree,G.card_neighborFinset_eq_degree] at ht
  exact (by have hh := ha u; have hh' := hb v; omega : False).elim

lemma inside_dist_three (hc : G.Connected) {S : Finset V} (hS : TotalDominating G S)
    (hcard : S.card=3) {a b : V} (ha : a∈S) (hb : b∈S) : G.dist a b≤2 := by
  by_cases hEq : a=b
  · subst b
    simp
  by_cases hab : G.Adj a b
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab]
    decide
  obtain ⟨c,hcS,hac⟩ := hS a
  obtain ⟨d,hdS,hbd⟩ := hS b
  have hnac : a≠c := SimpleGraph.Adj.ne hac
  have hnbd : b≠d := SimpleGraph.Adj.ne hbd
  have hnad : a≠d := fun e => hab (e.symm ▸ hbd.symm)
  have hnbc : b≠c := fun e => hab (e.symm ▸ hac)
  have hcd : c=d := by
    by_contra! hh
    have hsub : ({a,b,c,d} : Finset V) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl|rfl <;> assumption
    have hfour : ({a,b,c,d} : Finset V).card=4 := by
      simp [hEq,hnac,hnbd,hnad,hnbc,hh]
    have h := Finset.card_le_card hsub
    omega
  subst d
  have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr hac
  have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr hbd.symm
  have h := hc.dist_triangle (u:=a) (v:=c) (w:=b)
  omega

lemma all_dist_four_of_card_three (hc : G.Connected) {S : Finset V}
    (h : TotalDominating G S) (hcard : S.card=3) (x y : V) :
    G.dist x y≤4 := by
  obtain ⟨a,ha,hxa⟩ := h x
  obtain ⟨b,hb,hyb⟩ := h y
  have ha1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxa
  have hb1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyb.symm
  have hmiddle := inside_dist_three hc h hcard ha hb
  have hr := hc.dist_triangle (u:=x) (v:=a) (w:=y)
  have hs := hc.dist_triangle (u:=a) (v:=b) (w:=y)
  omega

lemma dist_bound_by_two_card (hc : G.Connected) {S : Finset V} (h : TotalDominating G S)
    (a b : V) : G.dist a b≤2*S.card := by
  classical
  obtain ⟨T,hTG,hTree,hTd⟩ := spanning_keep_td hc h
  obtain ⟨c,_,_,hcT,_⟩ := adjacent_bound_tree hTree hTd
  have ha := hcT a
  have hb := hcT b
  have htri := hTree.connected.dist_triangle (u:=a) (v:=c) (w:=b)
  rw [SimpleGraph.dist_comm (G:=T) (u:=a) (v:=c)] at htri
  have hT : T.dist a b≤2*S.card := by omega
  obtain ⟨p,hp⟩ := hTree.connected.exists_walk_length_eq_dist a b
  have hG := SimpleGraph.dist_le (p.map (SimpleGraph.Hom.ofLE hTG))
  rw [SimpleGraph.Walk.length_map,hp] at hG
  exact hG.trans hT

theorem square_bound (hc : G.Connected) {S : Finset V} (h : TotalDominating G S)
    {a b : V} (ha : MaxDegree G a) (hb : MaxDegree G b) :
    2*G.dist a b≤S.card^2 := by
  haveI := hc.nonempty
  have hs := totalDominating_two_le h
  by_cases heq : S.card=2
  · have h2 := max_pair_dist_two hc h heq ha hb
    simpa [heq] using (show 2*G.dist a b≤4 by omega)
  by_cases heq' : S.card=3
  · have h3 := all_dist_four_of_card_three hc h heq' a b
    simpa [heq'] using (show 2*G.dist a b≤9 by omega)
  have h4 : 4≤S.card := by omega
  have hlarge := dist_bound_by_two_card hc h a b
  calc
    2*G.dist a b≤4*S.card := by omega
    _ ≤ S.card^2 := by simpa [pow_two] using Nat.mul_le_mul_right S.card h4

#print axioms square_bound
end Wow271
