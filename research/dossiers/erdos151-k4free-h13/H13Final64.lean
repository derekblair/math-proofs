import H13Compose
import H13HighRows
import H13LowAmbientRows
import LargePoolEleven

open scoped BigOperators
namespace Erdős151.H13
open Erdos151H12 Erdos151H13 Erdos151CoreHigh Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem high_rows_from_R50 (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R50 : ∀ n, 50 ≤ n → TriangleIndependentEleven (Fin n))
    (n64 : 64 ≤ Fintype.card V)
    (bad : ¬ ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V)) :
    HighCoreStrict G := by
  classical
  have upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 12 := by
    intro P h
    by_contra hn
    exact bad ⟨P,by omega,h⟩
  have deg (w : V) : (neighbors G w).card ≤ 12 := by
    apply upper
    have eq : (↑(neighbors G w) : Set V) = {u | G w u} := by
      ext u
      simp [neighbors]
    rw [eq]
    exact neighborhood_free G sym link w
  intro C dc sub cs ci two mC w hr
  have mn (u : V) (hu : u ∈ neighbors C w) : 8 ≤ (neighbors C u).card :=
    mC u w (cs ((mem_neighbors C).mp hu))
  change (∑ v ∈ neighbors C w, Upper.row C (neighbors C w) v) < 3*(neighbors C w).card
  by_cases hd : (neighbors G w).card ≤ 10
  · have he := low_ambient_rows_at_least64_h13 G C sym irr (fun {_ _} h=>cs h) link
      (fun {_ _} h=>sub h) two deg (large_pool_free_eleven (G:=G) sym irr link R50)
      upper n64 w hd hr mn
    rw [he]
    omega
  · let J := H12.asSimple C (fun {_ _} h=>cs h) ci
    let dj : DecidableRel J.Adj := dc
    have raw := @H12.directed_link_sum V _ _ J dj w
    have he : ∃ e : ℕ, (∑ v ∈ neighbors C w, Upper.row C (neighbors C w) v) = 2*e := by
      change (∑ v ∈ neighbors C w, Upper.row C (neighbors C w) v) = _ at raw
      exact ⟨_,raw⟩
    obtain ⟨e,he⟩ := he
    rw [he]
    exact high_rows_at_least64_h13 G C sym irr link (fun {_ _} h=>sub h) two deg
      upper n64 w (by omega) hr mn e he

/-- K4-free H(n)=13 case of Erdős–Gallai–Tuza at n≥64.
The only external theorem inputs are the indicated published Ramsey bounds. -/
theorem erdos151_k4free_H13_at_least64
    (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → H10.TriangleIndependentTen (Fin n))
    (R50 : ∀ n, 50 ≤ n → TriangleIndependentEleven (Fin n))
    (n64 : 64 ≤ Fintype.card V) (H : TriangleIndependentAtLeast 13 V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-13 ∧
      ∀ C, MaximalNontrivialClique G C → ∃ x ∈ C, x∈T :=
  k4free_transversal_from_ramsey_case G 13 sym irr link H
    (ramsey_free13_of_high_core_strict G sym irr link R41 n64
      · (high_rows_from_R50 G sym irr link R50 n64))

#print axioms erdos151_k4free_H13_at_least64
end Erdős151.H13
