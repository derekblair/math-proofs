-- R129 (2026-10-07): Lean formalization of R119's 3v Floor Theorem [PROVED*].
--
-- R119 §A: in any girth-≥5 graph, every triple (u,v,w) has 3v-gap ≥ −1, because
-- the identity re-attachment (each triple vertex keeps its old neighbours
-- outside the triple; P = internal edges) is always feasible and scores D.
--
-- What is formalized here (pure combinatorics, no ES machinery):
--   * the H3-clique property of old neighbourhoods (condition (1)),
--   * the conditional cross-nonedge (condition (2')),
--   * the intersection bound |A∩B| ≤ 1, empty when the internal edge is present (3'),
--   * P triangle-free (condition (4)),
--   * the identity move is feasible,
--   * its score equals R98's D = d_u+d_v+d_w − e_in (degree bookkeeping),
--   * the floor: max achievable 3v score ≥ D, i.e. 3v-gap ≥ −1,
--   * conditional 3v rigidity: no improving move ⟹ gap = −1 (R119 §A corollary).
--
-- Framework-external inputs (explicit hypotheses, never sorry-faked):
--   * the girth-≥5 graph itself (noC3/noC4 as structure fields),
--   * D as R98's removed-edge count (the identity emits exactly G — R98 semantics).
-- R119 §B.1 (cross edges harmless in the emitted graph when uv ∉ P) IS
-- formalized here (R133): the emitted-graph re-attachment model `emitAdj` plus
-- `cross_edge_no_triangle` (no C3 uses a cross edge — needs only (1)) and
-- `cross_edge_no_c4` (no C4 uses a cross edge — needs (1) + the P'-conditional
-- (2') on all three channels + (u,v) ∉ P'). R133's dossier documents a repair:
-- R119's §B.1 proof sketch hand-waves the s=v / s=w C4 cases with incorrect
-- one-liners; the complete case analysis shows the (2') hypotheses on the
-- *other* two channels are genuinely needed (e.g. x–y–v–w–x is a real C4
-- unless the B–C channel of (2') fires).
--
-- Note: every declaration takes its parameters as explicit binders. (In this
-- Mathlib version, `variable`-declared section variables are only usable in a
-- declaration whose statement mentions them, so section variables are not
-- relied upon here at all.)

import Mathlib

open Finset

namespace Girth5Floor3v

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite simple graph of girth at least 5: no triangle and no 4-cycle.
    `noC4` (every closed 4-walk collapses to a chord or a repeated vertex) is
    equivalent to C4-freeness for simple graphs. -/
structure Girth5Graph (V : Type*) where
  adj : V → V → Prop
  decAdj : DecidableRel adj
  symm : ∀ x y, adj x y → adj y x
  irrefl : ∀ x, ¬ adj x x
  noTri : ∀ a b c, adj a b → adj b c → adj c a → False
  noC4 : ∀ a b c d, adj a b → adj b c → adj c d → adj d a → (a = c ∨ b = d)

instance (G : Girth5Graph V) : DecidableRel G.adj := G.decAdj

/-- Neighbourhood of a vertex, as a finset. -/
def N (G : Girth5Graph V) (x : V) : Finset V := Finset.univ.filter (G.adj x)

@[simp] theorem mem_N (G : Girth5Graph V) (x y : V) :
    x ∈ N G y ↔ G.adj y x := by simp [N]

/-- The rest of the vertex set after removing the triple. -/
def W (G : Girth5Graph V) (u v w : V) : Finset V := ({u, v, w} : Finset V)ᶜ

/-- Identity re-attachment sets (R119 §A): each triple vertex keeps exactly its
    old neighbours outside the triple. -/
def A (G : Girth5Graph V) (u v w : V) : Finset V := N G u \ {v, w}
def B (G : Girth5Graph V) (u v w : V) : Finset V := N G v \ {u, w}
def C (G : Girth5Graph V) (u v w : V) : Finset V := N G w \ {u, v}

/-- Internal edges of the triple present in G (R119's P = E_in).
    The `DecidablePred` instance is given explicitly (via `G.decAdj`) so that
    later `Finset.card_filter` computations use the same instance as the
    indicator `if`s in the statements. -/
def P (G : Girth5Graph V) (u v w : V) : Finset (V × V) :=
  letI : DecidablePred (fun p : V × V => G.adj p.1 p.2) := fun p => G.decAdj p.1 p.2
  ({(u, v), (u, w), (v, w)} : Finset (V × V)).filter fun p => G.adj p.1 p.2

theorem mem_A (G : Girth5Graph V) (u v w x : V) :
    x ∈ A G u v w ↔ G.adj u x ∧ x ≠ v ∧ x ≠ w := by
  show x ∈ N G u \ ({v, w} : Finset V) ↔ _
  rw [Finset.mem_sdiff, mem_N G x u]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ne_eq]

theorem mem_B (G : Girth5Graph V) (u v w x : V) :
    x ∈ B G u v w ↔ G.adj v x ∧ x ≠ u ∧ x ≠ w := by
  show x ∈ N G v \ ({u, w} : Finset V) ↔ _
  rw [Finset.mem_sdiff, mem_N G x v]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ne_eq]

theorem mem_C (G : Girth5Graph V) (u v w x : V) :
    x ∈ C G u v w ↔ G.adj w x ∧ x ≠ u ∧ x ≠ v := by
  show x ∈ N G w \ ({u, v} : Finset V) ↔ _
  rw [Finset.mem_sdiff, mem_N G x w]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ne_eq]

theorem mem_W (G : Girth5Graph V) (u v w x : V) :
    x ∈ W G u v w ↔ x ≠ u ∧ x ≠ v ∧ x ≠ w := by
  show x ∈ (({u, v, w} : Finset V))ᶜ ↔ _
  rw [Finset.mem_compl]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ne_eq]

/-- H3-compatibility clique (R119 condition (1)): members pairwise non-adjacent
    with no common neighbour in W. -/
def IsH3Clique (G : Girth5Graph V) (u v w : V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ G.adj x y ∧ ∀ z ∈ W G u v w, ¬ (G.adj x z ∧ G.adj z y)

/-- Condition (1) for A: two distinct old neighbours of u are non-adjacent
    (else triangle u–x–y–u) and share no common neighbour in W
    (else C4 u–x–z–y–u). -/
theorem h3_A (G : Girth5Graph V) (u v w : V) : IsH3Clique G u v w (A G u v w) := by
  intro x hx y hy hxy
  rw [mem_A G u v w x] at hx
  rw [mem_A G u v w y] at hy
  obtain ⟨hux, -, -⟩ := hx
  obtain ⟨huy, -, -⟩ := hy
  refine ⟨fun hadj => G.noTri u x y hux hadj (G.symm u y huy), fun z hz h => ?_⟩
  obtain ⟨hxz, hzy⟩ := h
  rw [mem_W G u v w z] at hz
  obtain ⟨hzu, -, -⟩ := hz
  rcases G.noC4 u x z y hux hxz hzy (G.symm u y huy) with h | h
  · exact absurd h.symm hzu
  · exact absurd h hxy

/-- Condition (1) for B. -/
theorem h3_B (G : Girth5Graph V) (u v w : V) : IsH3Clique G u v w (B G u v w) := by
  intro x hx y hy hxy
  rw [mem_B G u v w x] at hx
  rw [mem_B G u v w y] at hy
  obtain ⟨hvx, -, -⟩ := hx
  obtain ⟨hvy, -, -⟩ := hy
  refine ⟨fun hadj => G.noTri v x y hvx hadj (G.symm v y hvy), fun z hz h => ?_⟩
  obtain ⟨hxz, hzy⟩ := h
  rw [mem_W G u v w z] at hz
  obtain ⟨-, hzv, -⟩ := hz
  rcases G.noC4 v x z y hvx hxz hzy (G.symm v y hvy) with h | h
  · exact absurd h.symm hzv
  · exact absurd h hxy

/-- Condition (1) for C. -/
theorem h3_C (G : Girth5Graph V) (u v w : V) : IsH3Clique G u v w (C G u v w) := by
  intro x hx y hy hxy
  rw [mem_C G u v w x] at hx
  rw [mem_C G u v w y] at hy
  obtain ⟨hwx, -, -⟩ := hx
  obtain ⟨hwy, -, -⟩ := hy
  refine ⟨fun hadj => G.noTri w x y hwx hadj (G.symm w y hwy), fun z hz h => ?_⟩
  obtain ⟨hxz, hzy⟩ := h
  rw [mem_W G u v w z] at hz
  obtain ⟨-, -, hzw⟩ := hz
  rcases G.noC4 w x z y hwx hxz hzy (G.symm w y hwy) with h | h
  · exact absurd h.symm hzw
  · exact absurd h hxy

/-- Condition (2') for A–B: with uv present, a cross edge x–y would close the
    C4 x–u–v–y–x. -/
theorem cross_AB (G : Girth5Graph V) (u v w : V) (huvE : G.adj u v) :
    ∀ x ∈ A G u v w, ∀ y ∈ B G u v w, ¬ G.adj x y := by
  intro x hx y hy hadj
  rw [mem_A G u v w x] at hx
  rw [mem_B G u v w y] at hy
  obtain ⟨hux, hxv, -⟩ := hx
  obtain ⟨hvy, hyu, -⟩ := hy
  rcases G.noC4 x u v y (G.symm u x hux) huvE hvy (G.symm x y hadj) with h | h
  · exact absurd h hxv
  · exact absurd h.symm hyu

/-- Condition (2') for A–C. -/
theorem cross_AC (G : Girth5Graph V) (u v w : V) (huwE : G.adj u w) :
    ∀ x ∈ A G u v w, ∀ z ∈ C G u v w, ¬ G.adj x z := by
  intro x hx z hz hadj
  rw [mem_A G u v w x] at hx
  rw [mem_C G u v w z] at hz
  obtain ⟨hux, -, hxw⟩ := hx
  obtain ⟨hwz, hzu, -⟩ := hz
  rcases G.noC4 x u w z (G.symm u x hux) huwE hwz (G.symm x z hadj) with h | h
  · exact absurd h hxw
  · exact absurd h.symm hzu

/-- Condition (2') for B–C. -/
theorem cross_BC (G : Girth5Graph V) (u v w : V) (hvwE : G.adj v w) :
    ∀ y ∈ B G u v w, ∀ z ∈ C G u v w, ¬ G.adj y z := by
  intro y hy z hz hadj
  rw [mem_B G u v w y] at hy
  rw [mem_C G u v w z] at hz
  obtain ⟨hvy, -, hyw⟩ := hy
  obtain ⟨hwz, -, hzv⟩ := hz
  rcases G.noC4 y v w z (G.symm v y hvy) hvwE hwz (G.symm y z hadj) with h | h
  · exact absurd h hyw
  · exact absurd h.symm hzv

/-- Condition (3'): A ∩ B is a subsingleton (C4 u–a–v–b–u). -/
theorem inter_AB_subsingleton (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) :
    ∀ a ∈ A G u v w ∩ B G u v w, ∀ b ∈ A G u v w ∩ B G u v w, a = b := by
  intro a ha b hb
  rw [Finset.mem_inter, mem_A G u v w a, mem_B G u v w a] at ha
  rw [Finset.mem_inter, mem_A G u v w b, mem_B G u v w b] at hb
  obtain ⟨⟨hua, -, -⟩, ⟨hva, -, -⟩⟩ := ha
  obtain ⟨⟨hub, -, -⟩, ⟨hvb, -, -⟩⟩ := hb
  rcases G.noC4 u a v b hua (G.symm v a hva) hvb (G.symm u b hub) with h | h
  · exact absurd h huv
  · exact h

theorem inter_AB_le_one (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) :
    (A G u v w ∩ B G u v w).card ≤ 1 :=
  Finset.card_le_one.mpr (inter_AB_subsingleton G u v w huv)

/-- Condition (3'): B ∩ C is a subsingleton. -/
theorem inter_BC_subsingleton (G : Girth5Graph V) (u v w : V) (hvw : v ≠ w) :
    ∀ a ∈ B G u v w ∩ C G u v w, ∀ b ∈ B G u v w ∩ C G u v w, a = b := by
  intro a ha b hb
  rw [Finset.mem_inter, mem_B G u v w a, mem_C G u v w a] at ha
  rw [Finset.mem_inter, mem_B G u v w b, mem_C G u v w b] at hb
  obtain ⟨⟨hva, -, -⟩, ⟨hwa, -, -⟩⟩ := ha
  obtain ⟨⟨hvb, -, -⟩, ⟨hwb, -, -⟩⟩ := hb
  rcases G.noC4 v a w b hva (G.symm w a hwa) hwb (G.symm v b hvb) with h | h
  · exact absurd h hvw
  · exact h

theorem inter_BC_le_one (G : Girth5Graph V) (u v w : V) (hvw : v ≠ w) :
    (B G u v w ∩ C G u v w).card ≤ 1 :=
  Finset.card_le_one.mpr (inter_BC_subsingleton G u v w hvw)

/-- Condition (3'): A ∩ C is a subsingleton. -/
theorem inter_AC_subsingleton (G : Girth5Graph V) (u v w : V) (huw : u ≠ w) :
    ∀ a ∈ A G u v w ∩ C G u v w, ∀ b ∈ A G u v w ∩ C G u v w, a = b := by
  intro a ha b hb
  rw [Finset.mem_inter, mem_A G u v w a, mem_C G u v w a] at ha
  rw [Finset.mem_inter, mem_A G u v w b, mem_C G u v w b] at hb
  obtain ⟨⟨hua, -, -⟩, ⟨hwa, -, -⟩⟩ := ha
  obtain ⟨⟨hub, -, -⟩, ⟨hwb, -, -⟩⟩ := hb
  rcases G.noC4 u a w b hua (G.symm w a hwa) hwb (G.symm u b hub) with h | h
  · exact absurd h huw
  · exact h

theorem inter_AC_le_one (G : Girth5Graph V) (u v w : V) (huw : u ≠ w) :
    (A G u v w ∩ C G u v w).card ≤ 1 :=
  Finset.card_le_one.mpr (inter_AC_subsingleton G u v w huw)

/-- Condition (3'): with uv present, A ∩ B is empty (triangle-free). -/
theorem inter_AB_empty (G : Girth5Graph V) (u v w : V) (huvE : G.adj u v) :
    A G u v w ∩ B G u v w = ∅ := by
  rw [← Finset.subset_empty]
  intro z hz
  rw [Finset.mem_inter, mem_A G u v w z, mem_B G u v w z] at hz
  obtain ⟨⟨huz, -, -⟩, ⟨hvz, -, -⟩⟩ := hz
  exact False.elim (G.noTri u v z huvE hvz (G.symm u z huz))

/-- Condition (3'): with uw present, A ∩ C is empty. -/
theorem inter_AC_empty (G : Girth5Graph V) (u v w : V) (huwE : G.adj u w) :
    A G u v w ∩ C G u v w = ∅ := by
  rw [← Finset.subset_empty]
  intro z hz
  rw [Finset.mem_inter, mem_A G u v w z, mem_C G u v w z] at hz
  obtain ⟨⟨huz, -, -⟩, ⟨hwz, -, -⟩⟩ := hz
  exact False.elim (G.noTri u w z huwE hwz (G.symm u z huz))

/-- Condition (3'): with vw present, B ∩ C is empty. -/
theorem inter_BC_empty (G : Girth5Graph V) (u v w : V) (hvwE : G.adj v w) :
    B G u v w ∩ C G u v w = ∅ := by
  rw [← Finset.subset_empty]
  intro z hz
  rw [Finset.mem_inter, mem_B G u v w z, mem_C G u v w z] at hz
  obtain ⟨⟨hvz, -, -⟩, ⟨hwz, -, -⟩⟩ := hz
  exact False.elim (G.noTri v w z hvwE hwz (G.symm v z hvz))

theorem P_subset (G : Girth5Graph V) (u v w : V) :
    P G u v w ⊆ {(u, v), (u, w), (v, w)} := Finset.filter_subset _ _

/-- Condition (4): P = E_in is triangle-free (else G would contain a triangle). -/
theorem P_not_all_three (G : Girth5Graph V) (u v w : V) :
    ¬ ((u, v) ∈ P G u v w ∧ (u, w) ∈ P G u v w ∧ (v, w) ∈ P G u v w) := by
  rintro ⟨h1, h2, h3⟩
  have e1 : G.adj u v := (Finset.mem_filter.mp h1).2
  have e2 : G.adj u w := (Finset.mem_filter.mp h2).2
  have e3 : G.adj v w := (Finset.mem_filter.mp h3).2
  exact G.noTri u v w e1 e3 (G.symm u w e2)

/-- Corrected 3v feasibility (R119 §A): conditions (1), (2'), (3'), (4).
    Note (2') is conditional on the internal edge — R119 §B's correction of
    R98's unconditional (2). -/
def IsFeasible (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V)) : Prop :=
  IsH3Clique G u v w A' ∧ IsH3Clique G u v w B' ∧ IsH3Clique G u v w C' ∧
  (G.adj u v → ∀ x ∈ A', ∀ y ∈ B', ¬ G.adj x y) ∧
  (G.adj u w → ∀ x ∈ A', ∀ y ∈ C', ¬ G.adj x y) ∧
  (G.adj v w → ∀ x ∈ B', ∀ y ∈ C', ¬ G.adj x y) ∧
  (A' ∩ B').card ≤ 1 ∧ (B' ∩ C').card ≤ 1 ∧ (A' ∩ C').card ≤ 1 ∧
  (G.adj u v → A' ∩ B' = ∅) ∧ (G.adj u w → A' ∩ C' = ∅) ∧ (G.adj v w → B' ∩ C' = ∅) ∧
  P' ⊆ {(u, v), (u, w), (v, w)} ∧ ¬ ((u, v) ∈ P' ∧ (u, w) ∈ P' ∧ (v, w) ∈ P')

/-- The identity re-attachment satisfies the corrected feasibility conditions. -/
theorem identity_feasible (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) :
    IsFeasible G u v w (A G u v w) (B G u v w) (C G u v w) (P G u v w) :=
  ⟨h3_A G u v w, h3_B G u v w, h3_C G u v w,
    cross_AB G u v w, cross_AC G u v w, cross_BC G u v w,
    inter_AB_le_one G u v w huv, inter_BC_le_one G u v w hvw, inter_AC_le_one G u v w huw,
    inter_AB_empty G u v w, inter_AC_empty G u v w, inter_BC_empty G u v w,
    P_subset G u v w, P_not_all_three G u v w⟩

/-- 3v score of a move (R98 semantics): |A| + |B| + |C| + |P|. -/
def score (A' B' C' : Finset V) (P' : Finset (V × V)) : ℕ :=
  A'.card + B'.card + C'.card + P'.card

/-- Decidability of corrected feasibility: every condition is a bounded
    quantification over finsets. -/
noncomputable instance feasDec (G : Girth5Graph V) (u v w : V) :
    DecidablePred (fun m : Finset V × Finset V × Finset V × Finset (V × V) =>
      IsFeasible G u v w m.1 m.2.1 m.2.2.1 m.2.2.2) :=
  fun m => Classical.propDecidable _

/-- The set of all feasible 3v moves (finite, since V is). -/
noncomputable def feasibleMoves (G : Girth5Graph V) (u v w : V) :
    Finset (Finset V × Finset V × Finset V × Finset (V × V)) :=
  Finset.univ.filter fun m => IsFeasible G u v w m.1 m.2.1 m.2.2.1 m.2.2.2

/-- Achievable 3v scores. -/
noncomputable def scores (G : Girth5Graph V) (u v w : V) : Finset ℕ :=
  (feasibleMoves G u v w).image fun m => score m.1 m.2.1 m.2.2.1 m.2.2.2

/-- R98's removed-edge count D = d_u + d_v + d_w − e_in. -/
def D (G : Girth5Graph V) (u v w : V) : ℕ :=
  (N G u).card + (N G v).card + (N G w).card - (P G u v w).card

/-- Indicator symmetry: adjacency is symmetric, so the indicators agree. -/
theorem if_adj_symm (G : Girth5Graph V) (x y : V) :
    (if G.adj x y then (1 : ℕ) else 0) = (if G.adj y x then 1 else 0) := by
  by_cases h1 : G.adj x y
  · have h2 : G.adj y x := G.symm x y h1
    simp only [h1, h2, if_true]
  · have h2 : ¬ G.adj y x := fun h => h1 (G.symm y x h)
    simp only [h1, h2, if_false]

theorem inter_card_u (G : Girth5Graph V) (u v w : V) (hvw : v ≠ w) :
    (N G u ∩ {v, w}).card = (if G.adj u v then 1 else 0) + (if G.adj u w then 1 else 0) := by
  have hfilter : N G u ∩ {v, w} = ({v, w} : Finset V).filter (· ∈ N G u) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter]
    tauto
  rw [hfilter, Finset.card_filter,
    Finset.sum_insert (by rw [Finset.mem_singleton]; exact hvw), Finset.sum_singleton]
  simp only [mem_N G]

theorem inter_card_v (G : Girth5Graph V) (u v w : V) (huw : u ≠ w) :
    (N G v ∩ {u, w}).card = (if G.adj v u then 1 else 0) + (if G.adj v w then 1 else 0) := by
  have hfilter : N G v ∩ {u, w} = ({u, w} : Finset V).filter (· ∈ N G v) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter]
    tauto
  rw [hfilter, Finset.card_filter,
    Finset.sum_insert (by rw [Finset.mem_singleton]; exact huw), Finset.sum_singleton]
  simp only [mem_N G]

theorem inter_card_w (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) :
    (N G w ∩ {u, v}).card = (if G.adj w u then 1 else 0) + (if G.adj w v then 1 else 0) := by
  have hfilter : N G w ∩ {u, v} = ({u, v} : Finset V).filter (· ∈ N G w) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter]
    tauto
  rw [hfilter, Finset.card_filter,
    Finset.sum_insert (by rw [Finset.mem_singleton]; exact huv), Finset.sum_singleton]
  simp only [mem_N G]

theorem P_card (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (P G u v w).card
      = (if G.adj u v then 1 else 0) + (if G.adj u w then 1 else 0)
        + (if G.adj v w then 1 else 0) := by
  have hfilter :
      P G u v w = ({(u, v), (u, w), (v, w)} : Finset (V × V)).filter fun p => G.adj p.1 p.2 :=
    rfl
  have h1 : (u, v) ∉ ({(u, w), (v, w)} : Finset (V × V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
    exact ⟨fun h => hvw h.2, fun h => huv h.1⟩
  have h2 : (u, w) ∉ ({(v, w)} : Finset (V × V)) := by
    rw [Finset.mem_singleton, Prod.mk.injEq]
    rintro ⟨hh, -⟩
    exact huv hh
  rw [hfilter, Finset.card_filter, Finset.sum_insert h1, Finset.sum_insert h2,
    Finset.sum_singleton]
  rw [if_congr (Iff.rfl : G.adj (u, v).1 (u, v).2 ↔ G.adj u v) rfl rfl,
    if_congr (Iff.rfl : G.adj (u, w).1 (u, w).2 ↔ G.adj u w) rfl rfl,
    if_congr (Iff.rfl : G.adj (v, w).1 (v, w).2 ↔ G.adj v w) rfl rfl]
  omega

/-- The identity re-attachment scores exactly D (R98's "emits exactly G"). -/
theorem score_identity (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) :
    score (A G u v w) (B G u v w) (C G u v w) (P G u v w) = D G u v w := by
  have eA : (A G u v w).card
      = (N G u).card - ((if G.adj u v then 1 else 0) + (if G.adj u w then 1 else 0)) := by
    have hA : A G u v w = N G u \ {v, w} := rfl
    rw [hA, Finset.card_sdiff, Finset.inter_comm, inter_card_u G u v w hvw]
  have eB : (B G u v w).card
      = (N G v).card - ((if G.adj u v then 1 else 0) + (if G.adj v w then 1 else 0)) := by
    have hB : B G u v w = N G v \ {u, w} := rfl
    rw [hB, Finset.card_sdiff, Finset.inter_comm, inter_card_v G u v w huw,
      if_adj_symm G v u]
  have eC : (C G u v w).card
      = (N G w).card - ((if G.adj u w then 1 else 0) + (if G.adj v w then 1 else 0)) := by
    have hC : C G u v w = N G w \ {u, v} := rfl
    rw [hC, Finset.card_sdiff, Finset.inter_comm, inter_card_w G u v w huv,
      if_adj_symm G w u, if_adj_symm G w v]
  have hle_u : (N G u ∩ {v, w}).card ≤ (N G u).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hle_v : (N G v ∩ {u, w}).card ≤ (N G v).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hle_w : (N G w ∩ {u, v}).card ≤ (N G w).card :=
    Finset.card_le_card Finset.inter_subset_left
  rw [inter_card_u G u v w hvw] at hle_u
  rw [inter_card_v G u v w huw, if_adj_symm G v u] at hle_v
  rw [inter_card_w G u v w huv, if_adj_symm G w u, if_adj_symm G w v] at hle_w
  unfold score D
  rw [eA, eB, eC, P_card G u v w huv huw hvw]
  omega

/-- The identity's score D is achievable. -/
theorem identity_mem_scores (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) : D G u v w ∈ scores G u v w := by
  rw [← score_identity G u v w huv huw hvw]
  unfold scores
  rw [Finset.mem_image]
  refine ⟨(A G u v w, B G u v w, C G u v w, P G u v w), ?_, rfl⟩
  show _ ∈ feasibleMoves G u v w
  unfold feasibleMoves
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, identity_feasible G u v w huv huw hvw⟩

theorem scores_nonempty (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) : (scores G u v w).Nonempty :=
  ⟨D G u v w, identity_mem_scores G u v w huv huw hvw⟩

/-- R119's 3v Floor Theorem: every triple in a girth-≥5 graph has 3v-gap ≥ −1.
    The identity re-attachment is always feasible and scores D, so the maximum
    achievable 3v score is at least D. -/
theorem three_v_floor (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) :
    ((scores G u v w).max' (scores_nonempty G u v w huv huw hvw) : ℤ)
      - (D G u v w : ℤ) - 1 ≥ -1 := by
  have hle : D G u v w ≤ (scores G u v w).max' (scores_nonempty G u v w huv huw hvw) :=
    Finset.le_max' _ _ (identity_mem_scores G u v w huv huw hvw)
  have hle' : (D G u v w : ℤ)
      ≤ (((scores G u v w).max' (scores_nonempty G u v w huv huw hvw) : ℕ) : ℤ) := by
    exact_mod_cast hle
  omega

/-- Conditional 3v rigidity (R119 §A corollary): if no improving 3v move exists
    (the ceiling), then the 3v-gap is exactly −1 at this triple — the identity
    is score-optimal. -/
theorem three_v_rigidity (G : Girth5Graph V) (u v w : V) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) (hall : ∀ s ∈ scores G u v w, s ≤ D G u v w) :
    (scores G u v w).max' (scores_nonempty G u v w huv huw hvw) = D G u v w := by
  apply le_antisymm
  · exact Finset.max'_le _ _ _ hall
  · exact Finset.le_max' _ _ (identity_mem_scores G u v w huv huw hvw)

/-- The emitted graph G' after a 3v re-attachment move (R119 §B). The three new
    vertices reuse the labels u, v, w; their neighbourhoods are exactly the
    attachment sets A', B', C' (all ⊆ W) plus the internal edges P'. Every other
    adjacency is inherited from G. The disjunction is stated symmetrically so
    that `emitAdj_symm` holds by permuting disjuncts. -/
def emitAdj (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V)) (x y : V) : Prop :=
  (x = u ∧ (y ∈ A' ∨ (y = v ∧ (u, v) ∈ P') ∨ (y = w ∧ (u, w) ∈ P'))) ∨
  (y = u ∧ (x ∈ A' ∨ (x = v ∧ (u, v) ∈ P') ∨ (x = w ∧ (u, w) ∈ P'))) ∨
  (x = v ∧ (y ∈ B' ∨ (y = u ∧ (u, v) ∈ P') ∨ (y = w ∧ (v, w) ∈ P'))) ∨
  (y = v ∧ (x ∈ B' ∨ (x = u ∧ (u, v) ∈ P') ∨ (x = w ∧ (v, w) ∈ P'))) ∨
  (x = w ∧ (y ∈ C' ∨ (y = u ∧ (u, w) ∈ P') ∨ (y = v ∧ (v, w) ∈ P'))) ∨
  (y = w ∧ (x ∈ C' ∨ (x = u ∧ (u, w) ∈ P') ∨ (x = v ∧ (v, w) ∈ P'))) ∨
  (x ≠ u ∧ x ≠ v ∧ x ≠ w ∧ y ≠ u ∧ y ≠ v ∧ y ≠ w ∧ G.adj x y)

theorem emitAdj_symm (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V)) (x y : V)
    (h : emitAdj G u v w A' B' C' P' x y) :
    emitAdj G u v w A' B' C' P' y x := by
  unfold emitAdj at h ⊢
  rcases h with h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h4, h5, h6, h1, h2, h3, G.symm x y h7⟩))))))

/-- Attachment sets lie in W, so none of the new vertices lies in any
    attachment set. -/
theorem not_mem_attach_of_mem_tri (G : Girth5Graph V) (u v w : V) (S : Finset V)
    (hSW : S ⊆ W G u v w) : u ∉ S ∧ v ∉ S ∧ w ∉ S := by
  refine ⟨?_, ?_, ?_⟩ <;> intro hmem <;> have hW := hSW hmem <;> rw [mem_W] at hW
  · exact hW.1 rfl
  · exact hW.2.1 rfl
  · exact hW.2.2 rfl

/-- Inversion for emitted edges out of a W-vertex: either an old edge into W,
    or an attachment edge to one of the new vertices. -/
theorem emit_left_new (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V)) (p q : V)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (h : emitAdj G u v w A' B' C' P' p q) :
    (q ≠ u ∧ q ≠ v ∧ q ≠ w ∧ G.adj p q) ∨ (q = u ∧ p ∈ A') ∨
      (q = v ∧ p ∈ B') ∨ (q = w ∧ p ∈ C') := by
  unfold emitAdj at h
  rcases h with ⟨hpu', -⟩ | ⟨rfl, h⟩ | ⟨hpv', -⟩ | ⟨rfl, h⟩ | ⟨hpw', -⟩ | ⟨rfl, h⟩ | h
  · exact absurd hpu' hpu
  · rcases h with h | ⟨hpv', -⟩ | ⟨hpw', -⟩
    · exact Or.inr (Or.inl ⟨rfl, h⟩)
    · exact absurd hpv' hpv
    · exact absurd hpw' hpw
  · exact absurd hpv' hpv
  · rcases h with h | ⟨hpu', -⟩ | ⟨hpw', -⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
    · exact absurd hpu' hpu
    · exact absurd hpw' hpw
  · exact absurd hpw' hpw
  · rcases h with h | ⟨hpu', -⟩ | ⟨hpv', -⟩
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
    · exact absurd hpu' hpu
    · exact absurd hpv' hpv
  · obtain ⟨-, -, -, hqu, hqv, hqw, hadj⟩ := h
    exact Or.inl ⟨hqu, hqv, hqw, hadj⟩

theorem emitAdj_irrefl (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hA'W : A' ⊆ W G u v w) (hB'W : B' ⊆ W G u v w) (hC'W : C' ⊆ W G u v w)
    (x : V) : ¬ emitAdj G u v w A' B' C' P' x x := by
  obtain ⟨huA, -, -⟩ := not_mem_attach_of_mem_tri G u v w A' hA'W
  obtain ⟨-, hvB, -⟩ := not_mem_attach_of_mem_tri G u v w B' hB'W
  obtain ⟨-, -, hwC⟩ := not_mem_attach_of_mem_tri G u v w C' hC'W
  intro h
  unfold emitAdj at h
  rcases h with ⟨hxu, h⟩ | ⟨hxu, h⟩ | ⟨hxv, h⟩ | ⟨hxv, h⟩ | ⟨hxw, h⟩ | ⟨hxw, h⟩ |
    ⟨-, -, -, -, -, -, hadj⟩
  · subst hxu
    rcases h with h | ⟨huv', -⟩ | ⟨huw', -⟩
    · exact huA h
    · exact huv huv'
    · exact huw huw'
  · subst hxu
    rcases h with h | ⟨huv', -⟩ | ⟨huw', -⟩
    · exact huA h
    · exact huv huv'
    · exact huw huw'
  · subst hxv
    rcases h with h | ⟨hvu, -⟩ | ⟨hvw', -⟩
    · exact hvB h
    · exact huv.symm hvu
    · exact hvw hvw'
  · subst hxv
    rcases h with h | ⟨hvu, -⟩ | ⟨hvw', -⟩
    · exact hvB h
    · exact huv.symm hvu
    · exact hvw hvw'
  · subst hxw
    rcases h with h | ⟨hwu, -⟩ | ⟨hwv, -⟩
    · exact hwC h
    · exact huw.symm hwu
    · exact hvw.symm hwv
  · subst hxw
    rcases h with h | ⟨hwu, -⟩ | ⟨hwv, -⟩
    · exact hwC h
    · exact huw.symm hwu
    · exact hvw.symm hwv
  · exact G.irrefl x hadj

/-- The u–v emitted edge is exactly the P' internal edge. -/
theorem emitAdj_uv (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hA'W : A' ⊆ W G u v w) (hB'W : B' ⊆ W G u v w) :
    emitAdj G u v w A' B' C' P' u v ↔ (u, v) ∈ P' := by
  obtain ⟨-, hvA, -⟩ := not_mem_attach_of_mem_tri G u v w A' hA'W
  obtain ⟨huB, -, -⟩ := not_mem_attach_of_mem_tri G u v w B' hB'W
  constructor
  · intro h
    unfold emitAdj at h
    rcases h with ⟨-, h⟩ | ⟨hvu, -⟩ | ⟨huv', -⟩ | ⟨-, h⟩ | ⟨huw', -⟩ | ⟨hvw', -⟩ |
      ⟨h1, -, -, -, -, -, -⟩
    · rcases h with h | ⟨-, hP⟩ | ⟨hvw', -⟩
      · exact absurd h hvA
      · exact hP
      · exact absurd hvw' hvw
    · exact absurd hvu huv.symm
    · exact absurd huv' huv
    · rcases h with h | ⟨-, hP⟩ | ⟨huw', -⟩
      · exact absurd h huB
      · exact hP
      · exact absurd huw' huw
    · exact absurd huw' huw
    · exact absurd hvw' hvw
    · exact False.elim (h1 rfl)
  · intro hP
    unfold emitAdj
    exact Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, hP⟩)⟩

/-- The u–w emitted edge is exactly the P' internal edge. -/
theorem emitAdj_uw (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hA'W : A' ⊆ W G u v w) (hC'W : C' ⊆ W G u v w) :
    emitAdj G u v w A' B' C' P' u w ↔ (u, w) ∈ P' := by
  obtain ⟨-, -, hwA⟩ := not_mem_attach_of_mem_tri G u v w A' hA'W
  obtain ⟨huC, -, -⟩ := not_mem_attach_of_mem_tri G u v w C' hC'W
  constructor
  · intro h
    unfold emitAdj at h
    rcases h with ⟨-, h⟩ | ⟨hwu, -⟩ | ⟨huv', -⟩ | ⟨hvw', -⟩ | ⟨huw', -⟩ | ⟨-, h⟩ |
      ⟨h1, -, -, -, -, -, -⟩
    · rcases h with h | ⟨hvv, -⟩ | ⟨-, hP⟩
      · exact absurd h hwA
      · exact absurd hvv hvw.symm
      · exact hP
    · exact absurd hwu huw.symm
    · exact absurd huv' huv
    · exact absurd hvw' hvw.symm
    · exact absurd huw' huw
    · rcases h with h | ⟨-, hP⟩ | ⟨huv', -⟩
      · exact absurd h huC
      · exact hP
      · exact absurd huv' huv
    · exact False.elim (h1 rfl)
  · intro hP
    unfold emitAdj
    exact Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, hP⟩)⟩

/-- The v–w emitted edge is exactly the P' internal edge. -/
theorem emitAdj_vw (G : Girth5Graph V) (u v w : V) (A' B' C' : Finset V)
    (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hB'W : B' ⊆ W G u v w) (hC'W : C' ⊆ W G u v w) :
    emitAdj G u v w A' B' C' P' v w ↔ (v, w) ∈ P' := by
  obtain ⟨-, hvB, hwB⟩ := not_mem_attach_of_mem_tri G u v w B' hB'W
  obtain ⟨-, hvC, -⟩ := not_mem_attach_of_mem_tri G u v w C' hC'W
  constructor
  · intro h
    unfold emitAdj at h
    rcases h with ⟨huv', -⟩ | ⟨hwu, -⟩ | ⟨-, h⟩ | ⟨hvw', -⟩ | ⟨huw', -⟩ | ⟨-, h⟩ |
      ⟨-, h2, -, -, -, -, -⟩
    · exact absurd huv' huv.symm
    · exact absurd hwu huw.symm
    · rcases h with h | ⟨hwu', -⟩ | ⟨-, hP⟩
      · exact absurd h hwB
      · exact absurd hwu' huw.symm
      · exact hP
    · exact absurd hvw' hvw.symm
    · exact absurd huw' hvw
    · rcases h with h | ⟨hvu, -⟩ | ⟨-, hP⟩
      · exact absurd h hvC
      · exact absurd hvu huv.symm
      · exact hP
    · exact False.elim (h2 rfl)
  · intro hP
    unfold emitAdj
    exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, hP⟩)⟩))

/-- R119 §B.1, triangle part: a cross edge x–y (x ∈ A', y ∈ B') with
    (u,v) ∉ P' lies on no triangle of the emitted graph. Needs only the
    H3-clique condition (1): any third vertex z of a triangle is either in W
    (triangle already in G) or a new vertex (forcing x,y into one clique). -/
theorem cross_edge_no_triangle (G : Girth5Graph V) (u v w : V)
    (A' B' C' : Finset V) (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hA'W : A' ⊆ W G u v w) (hB'W : B' ⊆ W G u v w) (hC'W : C' ⊆ W G u v w)
    (h1A : IsH3Clique G u v w A') (h1B : IsH3Clique G u v w B')
    (h1C : IsH3Clique G u v w C')
    (x y : V) (hxA : x ∈ A') (hyB : y ∈ B') (hxy : x ≠ y)
    (hcross : G.adj x y) :
    ∀ z, ¬ (emitAdj G u v w A' B' C' P' x y ∧
            emitAdj G u v w A' B' C' P' y z ∧
            emitAdj G u v w A' B' C' P' z x) := by
  have hxW := (mem_W G u v w x).mp (hA'W hxA)
  have hyW := (mem_W G u v w y).mp (hB'W hyB)
  obtain ⟨hxu, hxv, hxw⟩ := hxW
  obtain ⟨hyu, hyv, hyw⟩ := hyW
  intro z hz
  obtain ⟨-, hyz, hzx⟩ := hz
  by_cases hzu : z = u
  · rw [hzu] at hyz hzx
    have hyA : y ∈ A' := by
      rcases emit_left_new G u v w A' B' C' P' y u hyu hyv hyw hyz with
        ⟨h1, -, -, -⟩ | ⟨-, hA⟩ | ⟨hvu, -⟩ | ⟨hwu, -⟩
      · exact False.elim (h1 rfl)
      · exact hA
      · exact False.elim (huv hvu)
      · exact False.elim (huw hwu)
    obtain ⟨hna, -⟩ := h1A x hxA y hyA hxy
    exact hna hcross
  by_cases hzv : z = v
  · rw [hzv] at hyz hzx
    have hxB : x ∈ B' := by
      have h' := emitAdj_symm G u v w A' B' C' P' v x hzx
      rcases emit_left_new G u v w A' B' C' P' x v hxu hxv hxw h' with
        ⟨-, h2, -, -⟩ | ⟨huv', -⟩ | ⟨-, hB⟩ | ⟨hwv, -⟩
      · exact False.elim (h2 rfl)
      · exact False.elim (huv.symm huv')
      · exact hB
      · exact False.elim (absurd hwv hvw)
    obtain ⟨hna, -⟩ := h1B x hxB y hyB hxy
    exact hna hcross
  by_cases hzw : z = w
  · rw [hzw] at hyz hzx
    have hyC : y ∈ C' := by
      rcases emit_left_new G u v w A' B' C' P' y w hyu hyv hyw hyz with
        ⟨-, -, h3, -⟩ | ⟨huw', -⟩ | ⟨hvw', -⟩ | ⟨-, hC⟩
      · exact False.elim (h3 rfl)
      · exact False.elim (huw.symm huw')
      · exact False.elim (hvw.symm hvw')
      · exact hC
    have hxC : x ∈ C' := by
      have h' := emitAdj_symm G u v w A' B' C' P' w x hzx
      rcases emit_left_new G u v w A' B' C' P' x w hxu hxv hxw h' with
        ⟨-, -, h3, -⟩ | ⟨huw', -⟩ | ⟨hvw', -⟩ | ⟨-, hC⟩
      · exact False.elim (h3 rfl)
      · exact False.elim (huw.symm huw')
      · exact False.elim (hvw.symm hvw')
      · exact hC
    obtain ⟨hna, -⟩ := h1C x hxC y hyC hxy
    exact hna hcross
  · have hadj_yz : G.adj y z := by
      rcases emit_left_new G u v w A' B' C' P' y z hyu hyv hyw hyz with
        ⟨-, -, -, hadj⟩ | ⟨hzu', -⟩ | ⟨hzv', -⟩ | ⟨hzw', -⟩
      · exact hadj
      · exact absurd hzu' hzu
      · exact absurd hzv' hzv
      · exact absurd hzw' hzw
    have hadj_zx : G.adj z x := by
      have h' := emitAdj_symm G u v w A' B' C' P' z x hzx
      rcases emit_left_new G u v w A' B' C' P' x z hxu hxv hxw h' with
        ⟨-, -, -, hadj⟩ | ⟨hzu', -⟩ | ⟨hzv', -⟩ | ⟨hzw', -⟩
      · exact G.symm x z hadj
      · exact absurd hzu' hzu
      · exact absurd hzv' hzv
      · exact absurd hzw' hzw
    exact G.noTri x y z hcross hadj_yz hadj_zx

/-- R119 §B.1, 4-cycle part: a cross edge x–y (x ∈ A', y ∈ B') with
    (u,v) ∉ P' lies on no 4-cycle of the emitted graph — every closed 4-walk
    x–y–s–t–x collapses (x = s ∨ y = t). Needs (1) on all three cliques, the
    P'-conditional (2') on the A–C and B–C channels, and (u,v) ∉ P'.
    The 16-case analysis: s, t each either in W or a new vertex. The dangerous
    configuration x–u–v–y–x is killed by (u,v) ∉ P'; the mixed configurations
    x–y–u–w–x, x–y–v–w–x, x–y–w–u–x, x–y–w–v–x are killed by (2') on the other
    two channels (R119's sketch omits these — see dossier). -/
theorem cross_edge_no_c4 (G : Girth5Graph V) (u v w : V)
    (A' B' C' : Finset V) (P' : Finset (V × V))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hA'W : A' ⊆ W G u v w) (hB'W : B' ⊆ W G u v w) (hC'W : C' ⊆ W G u v w)
    (h1A : IsH3Clique G u v w A') (h1B : IsH3Clique G u v w B')
    (h1C : IsH3Clique G u v w C')
    (h2AC : (u, w) ∈ P' → ∀ a ∈ A', ∀ c ∈ C', ¬ G.adj a c)
    (h2BC : (v, w) ∈ P' → ∀ b ∈ B', ∀ c ∈ C', ¬ G.adj b c)
    (huvP : (u, v) ∉ P')
    (x y : V) (hxA : x ∈ A') (hyB : y ∈ B') (hxy : x ≠ y)
    (hcross : G.adj x y) :
    ∀ s t, emitAdj G u v w A' B' C' P' x y →
      emitAdj G u v w A' B' C' P' y s →
      emitAdj G u v w A' B' C' P' s t →
      emitAdj G u v w A' B' C' P' t x → (x = s ∨ y = t) := by
  have hxW := (mem_W G u v w x).mp (hA'W hxA)
  have hyW := (mem_W G u v w y).mp (hB'W hyB)
  obtain ⟨hxu, hxv, hxw⟩ := hxW
  obtain ⟨hyu, hyv, hyw⟩ := hyW
  have hxWm : x ∈ W G u v w := hA'W hxA
  have hyWm : y ∈ W G u v w := hB'W hyB
  have hcross' : G.adj y x := G.symm x y hcross
  intro s t hxyE hys hst htx
  rcases emit_left_new G u v w A' B' C' P' y s hyu hyv hyw hys with
    ⟨hsu, hsv, hsw, hadj_ys⟩ | ⟨hsu_eq, hyA⟩ | ⟨hsv_eq, -⟩ | ⟨hsw_eq, hyC⟩
  · -- s ∈ W. Invert t–x via symmetry (left = x ∈ W).
    have htx' := emitAdj_symm G u v w A' B' C' P' t x htx
    rcases emit_left_new G u v w A' B' C' P' x t hxu hxv hxw htx' with
      ⟨htu, htv, htw, hadj_xt⟩ | ⟨htu_eq, -⟩ | ⟨htv_eq, hxB⟩ | ⟨htw_eq, hxC⟩
    · -- t ∈ W: invert s–t; all four in W, apply G.noC4.
      rcases emit_left_new G u v w A' B' C' P' s t hsu hsv hsw hst with
        ⟨-, -, -, hadj_st⟩ | ⟨htu', -⟩ | ⟨htv', -⟩ | ⟨htw', -⟩
      · rcases G.noC4 x y s t hcross hadj_ys hadj_st (G.symm x t hadj_xt) with h | h
        · exact Or.inl h
        · exact Or.inr h
      · exact absurd htu' htu
      · exact absurd htv' htv
      · exact absurd htw' htw
    · -- t = u: s ∈ A'; x,s ∈ A' share neighbour y ∈ W, or x = s.
      rw [htu_eq] at hst htx
      have hsA : s ∈ A' := by
        rcases emit_left_new G u v w A' B' C' P' s u hsu hsv hsw hst with
          ⟨h1, -, -, -⟩ | ⟨-, hA⟩ | ⟨huv', -⟩ | ⟨huw', -⟩
        · exact False.elim (h1 rfl)
        · exact hA
        · exact False.elim (absurd huv' huv)
        · exact False.elim (absurd huw' huw)
      by_cases hxs : x = s
      · exact Or.inl hxs
      · exfalso
        obtain ⟨-, hH3⟩ := h1A x hxA s hsA hxs
        exact hH3 y hyWm ⟨hcross, hadj_ys⟩
    · -- t = v: x ∈ B', so x,y ∈ B' with an edge — against (1).
      rw [htv_eq] at hst htx
      exfalso
      obtain ⟨hna, -⟩ := h1B x hxB y hyB hxy
      exact hna hcross
    · -- t = w: s ∈ C'; x,s ∈ C' share neighbour y ∈ W, or x = s.
      rw [htw_eq] at hst htx
      have hsC : s ∈ C' := by
        rcases emit_left_new G u v w A' B' C' P' s w hsu hsv hsw hst with
          ⟨-, -, h3, -⟩ | ⟨huw', -⟩ | ⟨hvw', -⟩ | ⟨-, hC⟩
        · exact False.elim (h3 rfl)
        · exact False.elim (huw.symm huw')
        · exact False.elim (hvw.symm hvw')
        · exact hC
      by_cases hxs : x = s
      · exact Or.inl hxs
      · exfalso
        obtain ⟨-, hH3⟩ := h1C x hxC s hsC hxs
        exact hH3 y hyWm ⟨hcross, hadj_ys⟩
  · -- s = u, y ∈ A'.
    rw [hsu_eq] at hys hst
    have htx' := emitAdj_symm G u v w A' B' C' P' t x htx
    rcases emit_left_new G u v w A' B' C' P' x t hxu hxv hxw htx' with
      ⟨htu, htv, htw, hadj_xt⟩ | ⟨htu_eq, -⟩ | ⟨htv_eq, hxB⟩ | ⟨htw_eq, hxC⟩
    · -- t ∈ W: t ∈ A'; x,t ∈ A' with an old edge, or x = t (irrefl).
      have htA : t ∈ A' := by
        have h' := emitAdj_symm G u v w A' B' C' P' u t hst
        rcases emit_left_new G u v w A' B' C' P' t u htu htv htw h' with
          ⟨h1, -, -, -⟩ | ⟨-, hA⟩ | ⟨huv', -⟩ | ⟨huw', -⟩
        · exact False.elim (h1 rfl)
        · exact hA
        · exact False.elim (absurd huv' huv)
        · exact False.elim (absurd huw' huw)
      by_cases hxt : x = t
      · exfalso
        rw [← hxt] at htx
        exact emitAdj_irrefl G u v w A' B' C' P' huv huw hvw hA'W hB'W hC'W x htx
      · exfalso
        obtain ⟨hna, -⟩ := h1A x hxA t htA hxt
        exact hna hadj_xt
    · -- t = u: E u u against irrefl.
      rw [htu_eq] at hst htx
      exfalso
      exact emitAdj_irrefl G u v w A' B' C' P' huv huw hvw hA'W hB'W hC'W u hst
    · -- t = v: E u v needs (u,v) ∈ P', excluded.
      rw [htv_eq] at hst htx
      exfalso
      have hP : (u, v) ∈ P' :=
        (emitAdj_uv G u v w A' B' C' P' huv huw hvw hA'W hB'W).mp hst
      exact huvP hP
    · -- t = w: E u w needs (u,w) ∈ P'; then y–x is an A–C cross edge vs (2').
      rw [htw_eq] at hst htx
      exfalso
      have hP : (u, w) ∈ P' :=
        (emitAdj_uw G u v w A' B' C' P' huv huw hvw hA'W hC'W).mp hst
      exact h2AC hP y hyA x hxC hcross'
  · -- s = v.
    rw [hsv_eq] at hys hst
    have htx' := emitAdj_symm G u v w A' B' C' P' t x htx
    rcases emit_left_new G u v w A' B' C' P' x t hxu hxv hxw htx' with
      ⟨htu, htv, htw, hadj_xt⟩ | ⟨htu_eq, -⟩ | ⟨htv_eq, hxB⟩ | ⟨htw_eq, hxC⟩
    · -- t ∈ W: t ∈ B'; y,t ∈ B' share neighbour x ∈ W, or y = t.
      have htB : t ∈ B' := by
        have h' := emitAdj_symm G u v w A' B' C' P' v t hst
        rcases emit_left_new G u v w A' B' C' P' t v htu htv htw h' with
          ⟨-, h2, -, -⟩ | ⟨huv', -⟩ | ⟨-, hB⟩ | ⟨hvw', -⟩
        · exact False.elim (h2 rfl)
        · exact False.elim (huv.symm huv')
        · exact hB
        · exact False.elim (absurd hvw' hvw)
      by_cases hyt : y = t
      · exact Or.inr hyt
      · exfalso
        obtain ⟨-, hH3⟩ := h1B y hyB t htB hyt
        exact hH3 x hxWm ⟨hcross', hadj_xt⟩
    · -- t = u: E v u needs (u,v) ∈ P', excluded.
      rw [htu_eq] at hst htx
      exfalso
      have hP : (u, v) ∈ P' :=
        (emitAdj_uv G u v w A' B' C' P' huv huw hvw hA'W hB'W).mp
          (emitAdj_symm G u v w A' B' C' P' v u hst)
      exact huvP hP
    · -- t = v: E v v against irrefl.
      rw [htv_eq] at hst htx
      exfalso
      exact emitAdj_irrefl G u v w A' B' C' P' huv huw hvw hA'W hB'W hC'W v hst
    · -- t = w: E v w needs (v,w) ∈ P'; then y–x is a B–C cross edge vs (2').
      rw [htw_eq] at hst htx
      exfalso
      have hP : (v, w) ∈ P' :=
        (emitAdj_vw G u v w A' B' C' P' huv huw hvw hB'W hC'W).mp hst
      exact h2BC hP y hyB x hxC hcross'
  · -- s = w, y ∈ C'.
    rw [hsw_eq] at hys hst
    have htx' := emitAdj_symm G u v w A' B' C' P' t x htx
    rcases emit_left_new G u v w A' B' C' P' x t hxu hxv hxw htx' with
      ⟨htu, htv, htw, hadj_xt⟩ | ⟨htu_eq, -⟩ | ⟨htv_eq, hxB⟩ | ⟨htw_eq, hxC⟩
    · -- t ∈ W: t ∈ C'; y,t ∈ C' share neighbour x ∈ W, or y = t.
      have htC : t ∈ C' := by
        have h' := emitAdj_symm G u v w A' B' C' P' w t hst
        rcases emit_left_new G u v w A' B' C' P' t w htu htv htw h' with
          ⟨-, -, h3, -⟩ | ⟨huw', -⟩ | ⟨hvw', -⟩ | ⟨-, hC⟩
        · exact False.elim (h3 rfl)
        · exact False.elim (huw.symm huw')
        · exact False.elim (hvw.symm hvw')
        · exact hC
      by_cases hyt : y = t
      · exact Or.inr hyt
      · exfalso
        obtain ⟨-, hH3⟩ := h1C y hyC t htC hyt
        exact hH3 x hxWm ⟨hcross', hadj_xt⟩
    · -- t = u: E w u needs (u,w) ∈ P'; then x–y is an A–C cross edge vs (2').
      rw [htu_eq] at hst htx
      exfalso
      have hP : (u, w) ∈ P' :=
        (emitAdj_uw G u v w A' B' C' P' huv huw hvw hA'W hC'W).mp
          (emitAdj_symm G u v w A' B' C' P' w u hst)
      exact h2AC hP x hxA y hyC hcross
    · -- t = v: E w v needs (v,w) ∈ P'; then x–y is a B–C cross edge vs (2').
      rw [htv_eq] at hst htx
      exfalso
      have hP : (v, w) ∈ P' :=
        (emitAdj_vw G u v w A' B' C' P' huv huw hvw hB'W hC'W).mp
          (emitAdj_symm G u v w A' B' C' P' w v hst)
      exact h2BC hP x hxB y hyC hcross
    · -- t = w: E w w against irrefl.
      rw [htw_eq] at hst htx
      exfalso
      exact emitAdj_irrefl G u v w A' B' C' P' huv huw hvw hA'W hB'W hC'W w hst

end Girth5Floor3v
