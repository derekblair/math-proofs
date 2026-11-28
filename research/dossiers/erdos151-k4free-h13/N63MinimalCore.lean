import N63NeutralRouting
import N63HighCaps
import N63LowCubic
import H13Compose
import AmbientMark

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
open Erdős151 Erdos151H12 Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem no_bipartite_at_core_vertex
    (C : V → V → Prop) [DecidableRel C]
    (cs : BikovLocal.Sym C) (ci : BikovLocal.Loopless C)
    (cr : BikovLocal.Ramsey C)
    (minimal : ∀ H : V→V→Prop, BikovLocal.Sub H C → BikovLocal.Sym H →
      ∀ a b, C a b → ¬H a b → ¬BikovLocal.Ramsey H)
    (v : V) (nv : (neighbors C v).Nonempty) : ¬TwoChargedPivots.Bicuts C (neighbors C v) := by
  intro bi
  obtain ⟨f,_,h⟩ := ambient_core_link_marked C C (fun {_ _} h => h) cs ci cr minimal v nv
  let c (a b : V) : Bool := if ha : a∈neighbors C v then
    if hb : b∈neighbors C v then f ⟨a,ha⟩ ⟨b,hb⟩ else false
    else false
  obtain ⟨g,hg⟩ := bipartite_link_spokes_extend C _ bi c
  apply h
  refine ⟨fun a => g a.val,?_⟩
  intro a b e
  have p := hg a.val a.property b.val b.property e
  simpa [c,a.property,b.property] using p

theorem minimal_core_global_score
    (C : V→V→Prop) [DecidableRel C] (cs : BikovLocal.Sym C) (ci : BikovLocal.Loopless C)
    (cr : BikovLocal.Ramsey C)
    (minimal : ∀ H : V→V→Prop, BikovLocal.Sub H C → BikovLocal.Sym H →
      ∀ a b, C a b → ¬H a b → ¬BikovLocal.Ramsey H) :
    (0:ℤ) ≤ ∑ v : V, (((∑ a ∈ neighbors C v, deg C (neighbors C v) a : ℕ) : ℤ) -
      3*((neighbors C v).card:ℤ)) := by
  classical
  let J := Erdős151.H12.asSimple C (fun {_ _} h => cs h) ci
  let : DecidableRel J.Adj := by change DecidableRel C; infer_instance
  have density := minimal_ramsey_triangle_density J cr minimal
  have d := handshake_clique_finset J
  have t := sum_vertex_triangle_counts J
  have t2 : (∑ v : V, (∑ a ∈ neighbors C v, deg C (neighbors C v) a)) =
      2*(∑ v : V, ((J.cliqueFinset 3).filter (fun T => v∈T)).card) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => directed_link_sum J v)
  change (∑ v : V, (neighbors C v).card) = 2*(J.cliqueFinset 2).card at d
  have u : 3*(∑ v : V, (neighbors C v).card) ≤
      (∑ v : V, (∑ a ∈ neighbors C v, deg C (neighbors C v) a)) := by
    rw [d,t2,t]
    omega
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Nat.cast_sum,←Nat.cast_sum]
  omega

#print axioms no_bipartite_at_core_vertex
#print axioms minimal_core_global_score
end Erdos151H13
