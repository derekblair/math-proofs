import H12DegreeTenBound
import H12DegreeElevenBound
import H12EdgePolicies

namespace Erdos151H12
open Erdős151 Erdős151.Upper
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V] (G C : V → V → Prop)
variable [DecidableRel G] [DecidableRel C]

theorem row_core_codeg (u v : V) :
    row C (neighbors C u) v = ambientCodeg C u v := by
  unfold row ambientCodeg
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_inter,mem_neighbors]

/-- Unified n≥53 local contribution bound. Assumes only the marked r8 atlas bounds. No separate cycle extension,
n54/n55 computation or r9 figure-eight premise. -/
theorem unified_vertex_contribution
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (tf : TriangleFreeLinks G)
    (symC : ∀ {a b}, C a b → C b a)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (deg : ∀ v, (neighbors G v).card ≤ 11)
    (minC : ∀ {a b}, C a b → 8 ≤ (neighbors C a).card)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (lower : ∀ R : Finset V, 41 ≤ R.card →
      ∃ P ⊆ R, 10 ≤ P.card ∧ Free (Forbidden G) (P : Set V))
    (cap8 : ∀ u v, C u v → (neighbors C u).card = 8 → ambientCodeg C u v ≤ 4)
    (n53 : 53 ≤ Fintype.card V)
    (w : V) (hcore : 8 ≤ (neighbors C w).card)
    (e : Nat) (he : ∑ u∈neighbors C w,row C (neighbors C w) u = 2*e)
    (atlas8 : (neighbors C w).card = 8 → 10 ≤ e ∧ e ≤ 12) :
    2*e ≤ 3*(neighbors C w).card ∧ (9 ≤ (neighbors C w).card → 2*e < 3*(neighbors C w).card) := by
  let d := (neighbors G w).card
  let r := (neighbors C w).card
  have hd : d ≤ 11 := deg w
  have hrd : r ≤ d := Finset.card_le_card
    (fun v hv => (mem_neighbors G).mpr (sub ((mem_neighbors C).mp hv)))
  have hmin (v : V) (hv : v∈neighbors C w) : 8 ≤ (neighbors C v).card :=
    minC (symC (a:=w) (b:=v) ((mem_neighbors C).mp hv))
  have book (v : V) (hv : v∈neighbors C w) :=
    core_edge_budgets G C sym irr symC tf sub two lower upper cap8 w v
      ((mem_neighbors C).mp hv) hcore (hmin v hv)
  have notLow : ¬ d ≤ 8 := by
    intro hLow
    have h2 (v : V) (hv : v∈neighbors C w) : row C (neighbors C w) v = 2 := by
      rw [row_core_codeg]
      have h := (book v hv).2.1
      change (40+d+(neighbors G v).card ≤ Fintype.card V+6) → _ at h
      exact (h (by have := deg v; omega)).2.2
    have hh : (∑ v∈neighbors C w,row C (neighbors C w) v) = ∑ _v∈neighbors C w,(2:Nat) :=
      Finset.sum_congr rfl h2
    rw [hh] at he
    have hs : (∑ _v∈neighbors C w,(2:Nat)) = 2*r := by simp [r,Nat.mul_comm]
    rw [hs] at he
    have h8 : r = 8 := by change 8 ≤ r at hcore; omega
    have hMin := (atlas8 h8).1
    omega
  change 2*e ≤ 3*r ∧ (9≤r → 2*e < 3*r)
  by_cases h8 : r=8
  · have h := (atlas8 h8).2
    omega
  by_cases h9 : d=9
  · have h3 (v : V) (hv : v∈neighbors C w) : row C (neighbors C w) v ≤ 3 := by
      rw [row_core_codeg]
      have h := (book v hv).2.2.1
      change (40+d+(neighbors G v).card ≤ Fintype.card V+7) → _ at h
      exact h (by have := deg v; omega)
    have hsum := Finset.sum_le_sum (g:=fun _v => (3:Nat)) h3
    have hR : r = 9 := by change 8 ≤ r at hcore; omega
    rw [he] at hsum
    have h3r : (∑ _v∈neighbors C w,(3:Nat)) = 3*r := by simp [r,Nat.mul_comm]
    rw [h3r] at hsum
    omega
  by_cases h10 : d=10
  · have hten := degreeTen_at_least53 G C sym irr tf sub two deg upper n53 w h10 hmin e he
    change (r=9 → e≤13) ∧ (r=10 → e≤14) at hten
    change 8 ≤ r at hcore
    by_cases hr9 : r=9
    · have := hten.1 hr9
      omega
    · have := hten.2 (by omega)
      omega
  have h11 : d=11 := by omega
  have helev := degreeEleven_at_least53 G C sym irr tf sub two deg upper n53 w h11 hmin e he
  change (r=9 → e≤13) ∧ (r=10 → e≤11) ∧ (r=11 → e≤10) at helev
  change 8≤r at hcore
  by_cases hr9 : r=9
  · have := helev.1 hr9
    omega
  by_cases hr10 : r=10
  · have := helev.2.1 hr10
    omega
  have := helev.2.2 (by omega)
  omega

#print axioms unified_vertex_contribution
end Erdos151H12
