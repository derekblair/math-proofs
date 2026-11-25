/-
  ESFiberTiling.lean — R193 fiber-{6,11} thinned-tiling catalogue: 16 BLOCKED shapes as `decide`, live-union bounds (fiber 6 ≤6/11, fiber 11 ≤7/11), §4 minimal-subcover argument.

  Paper: papers/fiber-compatibility-composite-suppression-October-11-2026/
  Status: [PROVED] — liveUnion_bound_6, liveUnion_bound_11, shape*_fiber*_blocked
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); machine-checked on bakkie (R202), `lake build` exit 0, zero sorrys, axioms standard-only.
-/

import Mathlib

/-!
# R193 fiber-{6,11} thinned-tiling catalogue (Round 202, Lean lane)

Formalizes the *finite* core of `~/workspace/math-unsolved/ROUND193_DOSSIER.md`:
the realizable thinned-tiling catalogue on fibers 6 and 11.

* The 11 kappa-points (`Fin 11`); each of the 47 box instances `(S, roots)` as
  the `Finset (Fin 11)` of kappa-points it covers (re-derived from the kappa
  construction; all weights are 1, so class counts are point counts).
* The 94 instance verdicts (RULED-OUT = 0 / OPEN = 1 / ACHIEVABLE = 2) from
  `r193_catalog.json` — output of R193's (c mod 5005, S) SAT decision procedure,
  [COMPUTED] data, kernel-checked here only as given tables.
* The 16 shape verdicts (7 minimal 3-cover shapes × 2 fibers + the 2-cover),
  all BLOCKED, as `decide` theorems.
* The live-union bounds: ACHIEVABLE+OPEN instances cover ≤ 6 classes on fiber 6
  and ≤ 7 on fiber 11, as `decide` theorems.
* The census re-derived: the unique 2-cover and exactly 7 minimal 3-covers
  (bitmask enumeration, `decide`).
* The uniform no-tiling theorem: no family of live boxes covers all 11
  kappa-points — the R193 §4 argument for every m ≥ 2 at once.

Cited, not re-derived: R184's tiling criterion / coordinate+box+slice lemmas /
h-bound / complementary-5-slice global impossibility, R188's 10-fiber theorem,
R180's trichotomy / un-thinned census, R55's complete search (c ≤ 7507, h ≤ 2000).
The SAT decision procedure itself (JSON witness scans, candidate enumeration) is
computation outside Lean; its verdict table is taken as [COMPUTED] data.
-/

namespace ESFiberTiling

/-- The 47 box instances: kappa-point coverage of each `(S, roots)` box, in R193
    enumeration order (rsize 1..3, S lex, roots lex). -/
def boxes : List (Finset (Fin 11)) := [
  ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)),  -- box 0: S=(5,) roots=(0,)
  ({6, 7, 8, 9, 10} : Finset (Fin 11)),  -- box 1: S=(5,) roots=(2,)
  ({0, 1, 2, 6, 7} : Finset (Fin 11)),  -- box 2: S=(7,) roots=(0,)
  ({3, 8} : Finset (Fin 11)),  -- box 3: S=(7,) roots=(1,)
  ({4, 5, 9, 10} : Finset (Fin 11)),  -- box 4: S=(7,) roots=(5,)
  ({0, 4, 6, 8, 9} : Finset (Fin 11)),  -- box 5: S=(11,) roots=(3,)
  ({1, 5, 7, 10} : Finset (Fin 11)),  -- box 6: S=(11,) roots=(6,)
  ({2, 3} : Finset (Fin 11)),  -- box 7: S=(11,) roots=(8,)
  ({0, 1, 2} : Finset (Fin 11)),  -- box 8: S=(5, 7) roots=(0, 0)
  ({3} : Finset (Fin 11)),  -- box 9: S=(5, 7) roots=(0, 1)
  ({4, 5} : Finset (Fin 11)),  -- box 10: S=(5, 7) roots=(0, 5)
  ({6, 7} : Finset (Fin 11)),  -- box 11: S=(5, 7) roots=(2, 0)
  ({8} : Finset (Fin 11)),  -- box 12: S=(5, 7) roots=(2, 1)
  ({9, 10} : Finset (Fin 11)),  -- box 13: S=(5, 7) roots=(2, 5)
  ({0, 4} : Finset (Fin 11)),  -- box 14: S=(5, 11) roots=(0, 3)
  ({1, 5} : Finset (Fin 11)),  -- box 15: S=(5, 11) roots=(0, 6)
  ({2, 3} : Finset (Fin 11)),  -- box 16: S=(5, 11) roots=(0, 8)
  ({6, 8, 9} : Finset (Fin 11)),  -- box 17: S=(5, 11) roots=(2, 3)
  ({7, 10} : Finset (Fin 11)),  -- box 18: S=(5, 11) roots=(2, 6)
  (∅ : Finset (Fin 11)),  -- box 19: S=(5, 11) roots=(2, 8)
  ({0, 6} : Finset (Fin 11)),  -- box 20: S=(7, 11) roots=(0, 3)
  ({1, 7} : Finset (Fin 11)),  -- box 21: S=(7, 11) roots=(0, 6)
  ({2} : Finset (Fin 11)),  -- box 22: S=(7, 11) roots=(0, 8)
  ({8} : Finset (Fin 11)),  -- box 23: S=(7, 11) roots=(1, 3)
  (∅ : Finset (Fin 11)),  -- box 24: S=(7, 11) roots=(1, 6)
  ({3} : Finset (Fin 11)),  -- box 25: S=(7, 11) roots=(1, 8)
  ({4, 9} : Finset (Fin 11)),  -- box 26: S=(7, 11) roots=(5, 3)
  ({5, 10} : Finset (Fin 11)),  -- box 27: S=(7, 11) roots=(5, 6)
  (∅ : Finset (Fin 11)),  -- box 28: S=(7, 11) roots=(5, 8)
  ({0} : Finset (Fin 11)),  -- box 29: S=(5, 7, 11) roots=(0, 0, 3)
  ({1} : Finset (Fin 11)),  -- box 30: S=(5, 7, 11) roots=(0, 0, 6)
  ({2} : Finset (Fin 11)),  -- box 31: S=(5, 7, 11) roots=(0, 0, 8)
  (∅ : Finset (Fin 11)),  -- box 32: S=(5, 7, 11) roots=(0, 1, 3)
  (∅ : Finset (Fin 11)),  -- box 33: S=(5, 7, 11) roots=(0, 1, 6)
  ({3} : Finset (Fin 11)),  -- box 34: S=(5, 7, 11) roots=(0, 1, 8)
  ({4} : Finset (Fin 11)),  -- box 35: S=(5, 7, 11) roots=(0, 5, 3)
  ({5} : Finset (Fin 11)),  -- box 36: S=(5, 7, 11) roots=(0, 5, 6)
  (∅ : Finset (Fin 11)),  -- box 37: S=(5, 7, 11) roots=(0, 5, 8)
  ({6} : Finset (Fin 11)),  -- box 38: S=(5, 7, 11) roots=(2, 0, 3)
  ({7} : Finset (Fin 11)),  -- box 39: S=(5, 7, 11) roots=(2, 0, 6)
  (∅ : Finset (Fin 11)),  -- box 40: S=(5, 7, 11) roots=(2, 0, 8)
  ({8} : Finset (Fin 11)),  -- box 41: S=(5, 7, 11) roots=(2, 1, 3)
  (∅ : Finset (Fin 11)),  -- box 42: S=(5, 7, 11) roots=(2, 1, 6)
  (∅ : Finset (Fin 11)),  -- box 43: S=(5, 7, 11) roots=(2, 1, 8)
  ({9} : Finset (Fin 11)),  -- box 44: S=(5, 7, 11) roots=(2, 5, 3)
  ({10} : Finset (Fin 11)),  -- box 45: S=(5, 7, 11) roots=(2, 5, 6)
  (∅ : Finset (Fin 11))  -- box 46: S=(5, 7, 11) roots=(2, 5, 8)
  ]

/-- Bit i set iff kappa-point i is covered. -/
def maskToFinset (m : Nat) : Finset (Fin 11) :=
  Finset.univ.filter (fun k : Fin 11 => m.testBit k.val)

/-- Bitmask mirror of `boxes`, for fast `decide` census. -/
def boxMasks : List Nat :=
  [63, 1984, 199, 264, 1584, 849, 1186, 12, 7, 8, 48, 192, 256, 1536, 17, 34, 12, 832, 1152, 0, 65, 130, 4, 256, 0, 8, 528, 1056, 0, 1, 2, 4, 0, 0, 8, 16, 32, 0, 64, 128, 0, 256, 0, 0, 512, 1024, 0]

theorem masks_match_boxes : ∀ i < 47,
    maskToFinset (boxMasks.getD i 0) = boxes.getD i ∅ :=
  by decide

/-- Instance verdicts on fiber 6: 0 = RULED-OUT, 1 = OPEN, 2 = ACHIEVABLE
    (`r193_catalog.json`, R193's SAT decision procedure — [COMPUTED] data). -/
def verdict6 : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0]

/-- Instance verdicts on fiber 11: 0 = RULED-OUT, 1 = OPEN, 2 = ACHIEVABLE. -/
def verdict11 : List Nat :=
  [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

theorem verdict_lengths : verdict6.length = 47 ∧ verdict11.length = 47 :=
  by decide

/-- Live box indices on a fiber (verdict table as parameter). -/
def liveIdx (verdict : List Nat) : Finset Nat :=
  (List.range 47).toFinset.filter (fun i => verdict.getD i 0 ≠ 0)

/-- Union of all live boxes on a fiber. -/
def liveUnion (verdict : List Nat) : Finset (Fin 11) :=
  (liveIdx verdict).biUnion (fun i => boxes.getD i ∅)

/-- R193 §1(c): live instances on fiber 6 cover at most 6/11 classes. -/
theorem liveUnion_bound_6 : (liveUnion verdict6).card ≤ 6 := by decide

/-- R193 §1(c): live instances on fiber 11 cover at most 7/11 classes. -/
theorem liveUnion_bound_11 : (liveUnion verdict11).card ≤ 7 := by decide

/-- The 7 minimal 3-cover shapes (R188 census, re-derived below), as box indices. -/
def shape0 : List Nat := [0, 5, 6]
def shape1 : List Nat := [0, 5, 18]
def shape2 : List Nat := [0, 6, 17]
def shape3 : List Nat := [0, 17, 18]
def shape4 : List Nat := [2, 3, 4]
def shape5 : List Nat := [5, 6, 7]
def shape6 : List Nat := [5, 6, 16]

/-- The complementary-5-slice 2-cover `({{5}},0)+({{5}},2)`. -/
def cover2 : List Nat := [0, 1]

/-- A shape is BLOCKED iff some constituent instance is RULED-OUT. -/
def shapeBlocked (verdict : List Nat) (sh : List Nat) : Bool :=
  sh.any (fun i => verdict.getD i 0 == 0)

-- R193 §1: the 16 shape×fiber verdicts, all BLOCKED.
theorem shape0_fiber6_blocked : shapeBlocked verdict6 shape0 = true :=
  by decide
theorem shape0_fiber11_blocked : shapeBlocked verdict11 shape0 = true :=
  by decide
theorem shape1_fiber6_blocked : shapeBlocked verdict6 shape1 = true :=
  by decide
theorem shape1_fiber11_blocked : shapeBlocked verdict11 shape1 = true :=
  by decide
theorem shape2_fiber6_blocked : shapeBlocked verdict6 shape2 = true :=
  by decide
theorem shape2_fiber11_blocked : shapeBlocked verdict11 shape2 = true :=
  by decide
theorem shape3_fiber6_blocked : shapeBlocked verdict6 shape3 = true :=
  by decide
theorem shape3_fiber11_blocked : shapeBlocked verdict11 shape3 = true :=
  by decide
theorem shape4_fiber6_blocked : shapeBlocked verdict6 shape4 = true :=
  by decide
theorem shape4_fiber11_blocked : shapeBlocked verdict11 shape4 = true :=
  by decide
theorem shape5_fiber6_blocked : shapeBlocked verdict6 shape5 = true :=
  by decide
theorem shape5_fiber11_blocked : shapeBlocked verdict11 shape5 = true :=
  by decide
theorem shape6_fiber6_blocked : shapeBlocked verdict6 shape6 = true :=
  by decide
theorem shape6_fiber11_blocked : shapeBlocked verdict11 shape6 = true :=
  by decide
theorem cover2_fiber6_blocked : shapeBlocked verdict6 cover2 = true :=
  by decide
theorem cover2_fiber11_blocked : shapeBlocked verdict11 cover2 = true :=
  by decide

/-- Each catalogue shape genuinely covers all 11 kappa-points. -/
theorem shape0_covers :
    (shape0.foldl (fun acc i => acc ∪ boxes.getD i ∅) ∅).card = 11 :=
  by decide
theorem shape1_covers :
    (shape1.foldl (fun acc i => acc ∪ boxes.getD i ∅) ∅).card = 11 :=
  by decide
theorem shape2_covers :
    (shape2.foldl (fun acc i => acc ∪ boxes.getD i ∅) ∅).card = 11 :=
  by decide
theorem shape3_covers :
    (shape3.foldl (fun acc i => acc ∪ boxes.getD i ∅) ∅).card = 11 :=
  by decide
theorem shape4_covers :
    (shape4.foldl (fun acc i => acc ∪ boxes.getD i ∅) ∅).card = 11 :=
  by decide
theorem shape5_covers :
    (shape5.foldl (fun acc i => acc ∪ boxes.getD i ∅) ∅).card = 11 :=
  by decide
theorem shape6_covers :
    (shape6.foldl (fun acc i => acc ∪ boxes.getD i ∅) ∅).card = 11 :=
  by decide
theorem cover2_covers :
    (cover2.foldl (fun acc i => acc ∪ boxes.getD i ∅) ∅).card = 11 :=
  by decide

-- Census re-derivation (R193 §5-V2) via bitmasks: OR == 2047 = all 11 covered.
def maskUnion (idxs : List Nat) : Nat :=
  idxs.foldl (fun acc i => acc ||| boxMasks.getD i 0) 0

def allPairs : List (Nat × Nat) :=
  (List.range 47).flatMap fun i =>
    (List.range' (i + 1) (47 - (i + 1))).map fun j => (i, j)

def allTriples : List (Nat × Nat × Nat) :=
  allPairs.flatMap fun p =>
    (List.range' (p.2 + 1) (47 - (p.2 + 1))).map fun k => (p.1, p.2, k)

set_option maxRecDepth 100000 in
/-- R193 §5-V2: the complementary-5-slice pair is the UNIQUE 2-cover. -/
theorem unique_2cover :
    allPairs.filter (fun p => maskUnion [p.1, p.2] == 2047)
      = [(0, 1)] :=
  by decide

set_option maxRecDepth 100000 in
/-- R193 §5-V2: exactly the 7 catalogue shapes are minimal 3-covers
    (cover all 11, and no 2-subset covers). -/
theorem seven_minimal_3covers :
    allTriples.filter (fun t =>
      (maskUnion [t.1, t.2.1, t.2.2] == 2047) &&
        !((maskUnion [t.1, t.2.1] == 2047) ||
          (maskUnion [t.1, t.2.2] == 2047) ||
          (maskUnion [t.2.1, t.2.2] == 2047)))
      = [(0, 5, 6), (0, 5, 18), (0, 6, 17), (0, 17, 18), (2, 3, 4), (5, 6, 7), (5, 6, 16)] :=
  by decide

/-- R193 §4, uniform m ≥ 2 leg: any family of live boxes on fiber 6 whose union
    is all 11 kappa-points is impossible. The `hlive` hypothesis is the §4
    contrapositive (a RULED-OUT instance cannot be realized: a realizing quad's
    `(c, R₀)` would be a death-avoiding candidate inside R55's complete box,
    hence in the JSON); the covering hypothesis is R184's tiling criterion.
    The m = 2 leg (unique 5-slice pair, globally impossible per R184 §6) and the
    m = 3 leg (the 7 shapes, all BLOCKED above) are the special cases. -/
theorem no_tiling_fiber6 (bs : Finset (Finset (Fin 11)))
    (hlive : ∀ b ∈ bs, ∃ i, i < 47 ∧ verdict6.getD i 0 ≠ 0 ∧ b = boxes.getD i ∅)
    (hcov : bs.biUnion id = Finset.univ) : False := by
  have hsub : bs.biUnion id ⊆ liveUnion verdict6 := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, hi47, hlive_i, rfl⟩ := hlive b hb
    have hmem : i ∈ liveIdx verdict6 := by
      rw [liveIdx, Finset.mem_filter, List.mem_toFinset, List.mem_range]
      exact ⟨hi47, hlive_i⟩
    have hxb' : x ∈ boxes.getD i ∅ := hxb
    rw [liveUnion, Finset.mem_biUnion]
    exact ⟨i, hmem, hxb'⟩
  rw [hcov] at hsub
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hb := liveUnion_bound_6
  omega

/-- R193 §4, uniform m ≥ 2 leg on fiber 11. -/
theorem no_tiling_fiber11 (bs : Finset (Finset (Fin 11)))
    (hlive : ∀ b ∈ bs, ∃ i, i < 47 ∧ verdict11.getD i 0 ≠ 0 ∧ b = boxes.getD i ∅)
    (hcov : bs.biUnion id = Finset.univ) : False := by
  have hsub : bs.biUnion id ⊆ liveUnion verdict11 := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, hi47, hlive_i, rfl⟩ := hlive b hb
    have hmem : i ∈ liveIdx verdict11 := by
      rw [liveIdx, Finset.mem_filter, List.mem_toFinset, List.mem_range]
      exact ⟨hi47, hlive_i⟩
    have hxb' : x ∈ boxes.getD i ∅ := hxb
    rw [liveUnion, Finset.mem_biUnion]
    exact ⟨i, hmem, hxb'⟩
  rw [hcov] at hsub
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hb := liveUnion_bound_11
  omega

end ESFiberTiling
