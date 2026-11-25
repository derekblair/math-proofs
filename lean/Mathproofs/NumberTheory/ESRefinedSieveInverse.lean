/-
  ESRefinedSieveInverse.lean — R169/R178 refined sieve inverse: 44-CRT lemma + 6-class inverse-closure mod 3960.

  Paper: papers/sieve-inverse-branch-isolation-October-11-2026/
  Scope: the residue-algebra kernel and embedded finite data; the external
  lift-set provenance and extension claims remain outside these theorem types.
  All finite arithmetic proofs use kernel-checked tactics.
  Toolchain: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b).
-/

import Mathlib

-- Finite-check heavy module: raise the elaborator recursion limit for `decide`.
set_option maxRecDepth 10000

/-!
# R169 refined-sieve inverse-closure: S1--S3 + the 44-CRT lemma (Round 178, Lean lane)

Source: `~/workspace/math-unsolved/ROUND169_DOSSIER.md` (Lane 3 / Round 169).

The dossier proves (hand + computation, labelled [PROVED*]):
- **S1** (R169 section 5): the lift set's mod-3960 projection is EXACTLY the 6
  classes {1} sub 8 x {1,4,7} sub 9 x {1} sub 5 x {2,6} sub 11
  (as residues: 2521, 721, 1201, 3361, 3841, 2041);
- **S2** (R169 section 6): the 6-class set is inverse-closed mod 3960
  (per-CRT-component: 4*7 = 28 = 1 mod 9, 2*6 = 12 = 1 mod 11);
- **S3** (R169 section 7): CRT-local inverse-closure for general w in the
  saturated regime (fiber arguments for 2^e, e <= 6 and 3^e, e <= 3);
- **44-CRT lemma** (R169 section 4): for s = 1 (mod 24),
  s = 7 (mod 11) <-> s = 29 (mod 44).

This module machine-checks the complete residue-algebra kernel end to end,
including the finite data premises (the 196 parent residues, R169 section 3
F1--F3, verified here by `decide` over the embedded list, rebuilt read-only
from the round JSONs exactly as `r153_shadow.load_frontiers` does).

The residue-algebra statements below use only standard Lean axioms. The
saturated-regime *extension* (R169 section 7(d)) and the break boundary
(R169 section 8) remain [COMPUTED]: they are statements about lift-set
sizes, checked in `r169_diag4.py` / `r169_boundary.py`, not finite residue
computations.
-/

namespace ESRefinedSieve

/-! ## 1. The 44-CRT selectivity lemma (R169 section 4) -/

/-- R169 section 4, forward: in the =1-mod-24 universe, s = 7 (mod 11) forces
s = 29 (mod 44). Dossier proof: s = 7 (mod 11) gives s mod 44 in {7,18,29,40};
s = 1 (mod 24) gives s = 1 (mod 4); only 29 = 1 (mod 4). Here: linear arithmetic. -/
theorem crt44_forward (s : ℤ) (h24 : s ≡ 1 [ZMOD 24]) (h11 : s ≡ 7 [ZMOD 11]) :
    s ≡ 29 [ZMOD 44] := by
  rw [Int.modEq_iff_dvd] at h24 h11 ⊢
  omega

/-- R169 section 4, backward: s = 29 (mod 44) always gives s = 7 (mod 11),
since 11 divides 44. -/
theorem crt44_backward (s : ℤ) (h44 : s ≡ 29 [ZMOD 44]) : s ≡ 7 [ZMOD 11] := by
  rw [Int.modEq_iff_dvd] at h44 ⊢
  omega

/-- R169 section 4, the lemma as stated: for s = 1 (mod 24),
s = 7 (mod 11) <-> s = 29 (mod 44). -/
theorem crt44_iff (s : ℤ) (h24 : s ≡ 1 [ZMOD 24]) :
    (s ≡ 7 [ZMOD 11]) ↔ (s ≡ 29 [ZMOD 44]) :=
  ⟨fun h => crt44_forward s h24 h, crt44_backward s⟩

/-! ## 2. The 6-class support: exactness (S1 residue core, R169 section 5) -/

/-- The 6 residue classes mod 3960 = {1} sub 8 x {1,4,7} sub 9 x {1} sub 5 x {2,6} sub 11,
as explicit residues: (mod 9, mod 11) = (1,2) -> 2521, (1,6) -> 721,
(4,2) -> 1201, (4,6) -> 3361, (7,2) -> 3841, (7,6) -> 2041. -/
def sixClasses : Finset (ZMod 3960) := {2521, 721, 1201, 3361, 3841, 2041}

theorem sixClasses_card : sixClasses.card = 6 := by decide

/-- S1 residue-algebra core (R169 section 5): the CRT-product description of the
6-class support is exact -- a residue mod 3960 lies in the product of the
prime-power projections iff it is one of the 6 classes. -/
theorem sixClasses_exact : ∀ x : ZMod 3960,
    (x.val % 8 = 1 ∧ x.val % 5 = 1 ∧
      (x.val % 9 = 1 ∨ x.val % 9 = 4 ∨ x.val % 9 = 7) ∧
      (x.val % 11 = 2 ∨ x.val % 11 = 6)) ↔ x ∈ sixClasses := by
  intro x
  constructor
  · rintro ⟨h8, h5, h9, h11⟩
    have hlt := x.val_lt
    have h3 : x.val % 3 = 1 := by
      have hmod := Nat.mod_mod_of_dvd x.val (by decide : 3 ∣ 9)
      omega
    have h120 : x.val % 120 = 1 := by omega
    have hv : x.val = 2521 ∨ x.val = 721 ∨ x.val = 1201 ∨
        x.val = 3361 ∨ x.val = 3841 ∨ x.val = 2041 := by
      clear h8 h5 h9 h3
      omega
    rcases hv with h | h | h | h | h | h <;>
      rw [← ZMod.natCast_zmod_val x, h] <;> decide
  · intro hx
    have hc : x = 2521 ∨ x = 721 ∨ x = 1201 ∨ x = 3361 ∨ x = 3841 ∨ x = 2041 := by
      simpa [sixClasses] using hx
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Case analysis on the 6 classes. -/
theorem sixClasses_cases (c : ZMod 3960) (hc : c ∈ sixClasses) :
    c = 2521 ∨ c = 721 ∨ c = 1201 ∨ c = 3361 ∨ c = 3841 ∨ c = 2041 := by
  unfold sixClasses at hc
  simpa using hc

/-! ## 3. Inverse-closure (S2, R169 section 6) -/

/-- S2 mechanism, mod-9 component (R169 section 6): {1,4,7} is inverse-closed
mod 9 (4*7 = 28 = 1). -/
theorem inv_closed_mod9 : ∀ x : ZMod 9, x = 1 ∨ x = 4 ∨ x = 7 →
    ∃ y : ZMod 9, (y = 1 ∨ y = 4 ∨ y = 7) ∧ x * y = 1 := by
  decide

/-- S2 mechanism, mod-11 component (R169 section 6): {2,6} is inverse-closed
mod 11 (2*6 = 12 = 1). -/
theorem inv_closed_mod11 : ∀ x : ZMod 11, x = 2 ∨ x = 6 →
    ∃ y : ZMod 11, (y = 2 ∨ y = 6) ∧ x * y = 1 := by
  decide

/-- S2 mechanism, mod-8 and mod-5 components: the singleton {1} is inverse-closed. -/
theorem inv_closed_mod8 : ∀ x : ZMod 8, x = 1 →
    ∃ y : ZMod 8, y = 1 ∧ x * y = 1 := by
  decide

theorem inv_closed_mod5 : ∀ x : ZMod 5, x = 1 →
    ∃ y : ZMod 5, y = 1 ∧ x * y = 1 := by
  decide

/-- S2 (R169 section 6): the 6-class support is inverse-closed mod 3960.
Explicit inverse pairs: 2521*721 = 1, 1201*2041 = 1, 3361*3841 = 1 (mod 3960). -/
theorem sixClasses_inv_pairs :
    (2521 : ZMod 3960) * 721 = 1 ∧
    (1201 : ZMod 3960) * 2041 = 1 ∧
    (3361 : ZMod 3960) * 3841 = 1 := by
  decide

/-- S2, existential form: every class has its inverse in the set. -/
theorem sixClasses_inv_closed : ∀ x : ZMod 3960, x ∈ sixClasses →
    ∃ y ∈ sixClasses, x * y = 1 := by
  intro x hx
  rcases sixClasses_cases x hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨721, by decide, by decide⟩
  · exact ⟨2521, by decide, by decide⟩
  · exact ⟨2041, by decide, by decide⟩
  · exact ⟨3841, by decide, by decide⟩
  · exact ⟨3361, by decide, by decide⟩
  · exact ⟨1201, by decide, by decide⟩

/-- CRT composition (mechanism behind R169 section 7): inverse-closure composes
across CRT components -- if x*y = 1 in every prime-power component, then x*y = 1. -/
theorem crt_unique_one : ∀ z : ZMod 3960,
    z.val % 8 = 1 → z.val % 9 = 1 → z.val % 5 = 1 → z.val % 11 = 1 → z = 1 := by
  intro z h8 h9 h5 h11
  have hlt := z.val_lt
  have hz : z.val = 1 := by omega
  apply ZMod.val_injective 3960
  exact hz

theorem crt_inv_compose (x y : ZMod 3960)
    (h8 : (x * y).val % 8 = 1) (h9 : (x * y).val % 9 = 1)
    (h5 : (x * y).val % 5 = 1) (h11 : (x * y).val % 11 = 1) :
    x * y = 1 :=
  crt_unique_one (x * y) h8 h9 h5 h11

/-! ## 4. S1 lift mechanism (R169 section 5) -/

/-- M0 = 2042040 = 2^3*3*5*7*11*13*17 (R169 section 5): divisible by 8, 3, 5, 11,
and M0 = 3 (mod 9) -- the source of the mod-9 j-variation. -/
theorem M0_facts :
    8 ∣ 2042040 ∧ 3 ∣ 2042040 ∧ 5 ∣ 2042040 ∧ 11 ∣ 2042040 ∧ 2042040 % 9 = 3 := by
  decide

/-- S1 mechanism (R169 section 5): for a lift element n = sp + M0*j, the
mod-8/5/11 components are j-invariant (M0 = 0 there), and the mod-9 component
stays in {1,4,7}: sp = 1 mod 3 gives sp mod 9 in {1,4,7}; M0 = 3 mod 9 gives
3j in {0,3,6}; {1,4,7}+{0,3,6} = {1,4,7} mod 9. -/
theorem lift_components (sp j : ℕ)
    (h8 : sp % 8 = 1) (h5 : sp % 5 = 1) (h3 : sp % 3 = 1)
    (h11 : sp % 11 = 2 ∨ sp % 11 = 6) :
    (sp + 2042040 * j) % 8 = 1 ∧ (sp + 2042040 * j) % 5 = 1 ∧
      ((sp + 2042040 * j) % 9 = 1 ∨ (sp + 2042040 * j) % 9 = 4 ∨
        (sp + 2042040 * j) % 9 = 7) ∧
      ((sp + 2042040 * j) % 11 = 2 ∨ (sp + 2042040 * j) % 11 = 6) := by
  have e8 : (sp + 2042040 * j) % 8 = 1 := by omega
  have e5 : (sp + 2042040 * j) % 5 = 1 := by omega
  have e9 : (sp + 2042040 * j) % 9 = 1 ∨ (sp + 2042040 * j) % 9 = 4 ∨
      (sp + 2042040 * j) % 9 = 7 := by
    have h93 : ((sp + 2042040 * j) % 9) % 3 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 9)]
      omega
    have h9lt : (sp + 2042040 * j) % 9 < 9 := Nat.mod_lt _ (by norm_num)
    omega
  have e11 : (sp + 2042040 * j) % 11 = 2 ∨ (sp + 2042040 * j) % 11 = 6 := by
    rcases h11 with h | h <;> omega
  exact ⟨e8, e5, e9, e11⟩

/-- Bridge: a natural number's residue mod 3960 determines its ZMod-3960
prime-power projections. -/
theorem natCast_val_mod (n m : ℕ) (h : m ∣ 3960) :
    (((n : ℕ) : ZMod 3960)).val % m = n % m := by
  rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ h]

/-- S1, subset direction (R169 section 5): every lift element's mod-3960
projection lies in the 6-class support -- from the parent residue facts
(hypotheses) plus the lift mechanism. -/
theorem S1_subset (sp j : ℕ)
    (h8 : sp % 8 = 1) (h5 : sp % 5 = 1) (h3 : sp % 3 = 1)
    (h11 : sp % 11 = 2 ∨ sp % 11 = 6) :
    (((sp + 2042040 * j : ℕ)) : ZMod 3960) ∈ sixClasses := by
  obtain ⟨e8, e5, e9, e11⟩ := lift_components sp j h8 h5 h3 h11
  rw [← sixClasses_exact]
  exact ⟨by rw [natCast_val_mod _ _ (by norm_num : 8 ∣ 3960)]; exact e8,
    by rw [natCast_val_mod _ _ (by norm_num : 5 ∣ 3960)]; exact e5,
    by rw [natCast_val_mod _ _ (by norm_num : 9 ∣ 3960)]; exact e9,
    by rw [natCast_val_mod _ _ (by norm_num : 11 ∣ 3960)]; exact e11⟩

/-! ## 5. Parent data: F1--F3 machine-checked (R169 section 3) -/

/-- The 196 parent residues mod M0 = 2042040 (R169 section 1: parents196 =
R71 targets minus R71 cov minus R74 cov; rebuilt read-only from the round
JSONs exactly as `r153_shadow.load_frontiers` does). -/
def parents196 : List ℕ :=
[
    12601, 14401, 20521, 21841, 30241, 48721, 76441, 97561,
    104161, 132721, 149881, 150361, 153001, 159121, 178921, 187321,
    208441, 214561, 217681, 233521, 243601, 254641, 262081, 273121,
    279241, 282361, 298201, 307441, 328561, 334681, 344401, 372961,
    374761, 380881, 390601, 400681, 418321, 419161, 436801, 445561,
    457921, 473281, 483841, 493081, 522601, 529201, 547681, 556921,
    557761, 568801, 574921, 593401, 603961, 615001, 621121, 622441,
    630361, 642721, 677041, 677881, 679681, 685801, 688921, 695041,
    714001, 733321, 742561, 750481, 750961, 753601, 759721, 769441,
    798001, 799801, 805921, 834121, 862681, 871081, 882961, 889561,
    899641, 918121, 929161, 935281, 938401, 964321, 993841, 999961,
    1001281, 1003081, 1018921, 1019761, 1028161, 1040041, 1046161, 1058521,
    1073881, 1095481, 1101601, 1113961, 1120081, 1129801, 1148281, 1157521,
    1158361, 1160161, 1185241, 1204561, 1213801, 1215601, 1221721, 1230961,
    1243321, 1249921, 1277641, 1278481, 1305361, 1314121, 1333921, 1343161,
    1354201, 1360321, 1361641, 1379281, 1397761, 1400401, 1406521, 1409641,
    1434241, 1434721, 1463281, 1471201, 1471681, 1474321, 1480441, 1490161,
    1499401, 1517881, 1518721, 1529761, 1539001, 1554841, 1564921, 1583401,
    1591321, 1591801, 1619521, 1620361, 1628761, 1674481, 1674961, 1685041,
    1696081, 1702201, 1703521, 1711921, 1714561, 1720681, 1722001, 1723801,
    1748881, 1758121, 1779241, 1785841, 1794601, 1805161, 1814401, 1831561,
    1832041, 1842121, 1843921, 1850521, 1860601, 1869001, 1878241, 1879081,
    1880881, 1887001, 1899361, 1905961, 1915201, 1934521, 1936321, 1942441,
    1943761, 1951681, 1962241, 1970641, 1989121, 1999201, 2001001, 2007121,
    2010241, 2016361, 2034841, 2035321,
  ]

/-- R169 section 3, F1--F2: every parent satisfies sp = 1 (mod 8),
sp = 1 (mod 5), sp = 1 (mod 3) (hence sp mod 9 in {1,4,7}), and
sp mod 11 in {2,6} (104 parents at 2, 92 at 6). -/
theorem parent_facts : ∀ sp ∈ parents196,
    sp % 8 = 1 ∧ sp % 5 = 1 ∧ sp % 3 = 1 ∧ (sp % 11 = 2 ∨ sp % 11 = 6) := by
  decide

/-- R169 section 3, F3: the parents' prime-power projections are exactly the
stated inverse-closed sets (inclusion). -/
theorem parent_proj7 : ∀ sp ∈ parents196, sp % 7 = 1 ∨ sp % 7 = 2 ∨ sp % 7 = 4 := by
  decide

theorem parent_proj13 : ∀ sp ∈ parents196,
    sp % 13 = 1 ∨ sp % 13 = 2 ∨ sp % 13 = 3 ∨ sp % 13 = 4 ∨ sp % 13 = 5 ∨
      sp % 13 = 7 ∨ sp % 13 = 8 ∨ sp % 13 = 9 ∨ sp % 13 = 10 ∨ sp % 13 = 12 := by
  decide

theorem parent_proj17 : ∀ sp ∈ parents196,
    sp % 17 = 1 ∨ sp % 17 = 2 ∨ sp % 17 = 3 ∨ sp % 17 = 4 ∨ sp % 17 = 6 ∨
      sp % 17 = 8 ∨ sp % 17 = 9 ∨ sp % 17 = 13 ∨ sp % 17 = 15 ∨ sp % 17 = 16 := by
  decide

/-- R169 section 3, F3: exactness -- every listed residue actually occurs. -/
theorem parent_proj7_exact :
    ∀ r ∈ ([1, 2, 4] : List ℕ), ∃ sp ∈ parents196, sp % 7 = r := by
  decide

theorem parent_proj13_exact :
    ∀ r ∈ ([1, 2, 3, 4, 5, 7, 8, 9, 10, 12] : List ℕ), ∃ sp ∈ parents196, sp % 13 = r := by
  decide

theorem parent_proj17_exact :
    ∀ r ∈ ([1, 2, 3, 4, 6, 8, 9, 13, 15, 16] : List ℕ), ∃ sp ∈ parents196, sp % 17 = r := by
  decide

/-- S3(a) mechanism (R169 section 7): the parent prime-power projection sets
are inverse-closed. -/
theorem proj_inv_closed_7 : ∀ x : ZMod 7, x = 1 ∨ x = 2 ∨ x = 4 →
    ∃ y : ZMod 7, (y = 1 ∨ y = 2 ∨ y = 4) ∧ x * y = 1 := by
  decide

theorem proj_inv_closed_13 : ∀ x : ZMod 13,
    x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨
      x = 12 →
    ∃ y : ZMod 13, (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 7 ∨ y = 8 ∨
      y = 9 ∨ y = 10 ∨ y = 12) ∧ x * y = 1 := by
  decide

theorem proj_inv_closed_17 : ∀ x : ZMod 17,
    x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 6 ∨ x = 8 ∨ x = 9 ∨ x = 13 ∨
      x = 15 ∨ x = 16 →
    ∃ y : ZMod 17, (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 6 ∨ y = 8 ∨ y = 9 ∨
      y = 13 ∨ y = 15 ∨ y = 16) ∧ x * y = 1 := by
  decide

/-! ## 6. S1 exactness: the lift set's mod-3960 projection (R169 section 5) -/

/-- The q-lift set (R169 section 1): L_q = { sp + M0*j : sp in parents196,
0 <= j < q, sp + M0*j not = 0 (mod q) }, projected to ZMod 3960. -/
def liftSet (q : ℕ) : Finset (ZMod 3960) :=
  Finset.image (fun p : ℕ × ℕ => (((p.1 + 2042040 * p.2 : ℕ)) : ZMod 3960))
    ((parents196.toFinset ×ˢ Finset.range q).filter
      (fun p => (p.1 + 2042040 * p.2) % q ≠ 0))

/-- S1, subset direction at the set level (R169 section 5): the lift set
projects into the 6 classes. -/
theorem S1_proj_subset (q : ℕ) (x : ZMod 3960) (hx : x ∈ liftSet q) :
    x ∈ sixClasses := by
  unfold liftSet at hx
  rw [Finset.mem_image] at hx
  obtain ⟨⟨sp, j⟩, hmem, heq⟩ := hx
  have heq' : (((sp + 2042040 * j : ℕ)) : ZMod 3960) = x := heq
  rw [Finset.mem_filter, Finset.mem_product] at hmem
  obtain ⟨⟨hsp, hj⟩, _⟩ := hmem
  rw [List.mem_toFinset] at hsp
  have hf := parent_facts sp hsp
  rw [← heq']
  exact S1_subset sp j hf.1 hf.2.1 hf.2.2.1 hf.2.2.2

/-- S1, surjectivity (R169 section 5): each of the 6 classes is hit by an
actual lift element -- explicit witnesses (sp, j) with sp in parents196,
j < 19, sp + M0*j not = 0 (mod 19):
2521 <- (14401, 0), 721 <- (12601, 0), 1201 <- (14401, 1),
3361 <- (12601, 4), 3841 <- (14401, 2), 2041 <- (12601, 2). -/
theorem S1_proj_surj :
    ∀ c ∈ sixClasses, ∃ sp ∈ parents196, ∃ j : ℕ, j < 19 ∧
      (sp + 2042040 * j) % 19 ≠ 0 ∧ ((((sp + 2042040 * j : ℕ))) : ZMod 3960) = c := by
  intro c hc
  rcases sixClasses_cases c hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨14401, by decide, 0, by decide, by decide, by decide⟩
  · exact ⟨12601, by decide, 0, by decide, by decide, by decide⟩
  · exact ⟨14401, by decide, 1, by decide, by decide, by decide⟩
  · exact ⟨12601, by decide, 4, by decide, by decide, by decide⟩
  · exact ⟨14401, by decide, 2, by decide, by decide, by decide⟩
  · exact ⟨12601, by decide, 2, by decide, by decide, by decide⟩

/-- S1 exact, q = 19 (R169 section 5): the lift set's mod-3960 projection is
EXACTLY the 6 classes. -/
theorem S1_exact : liftSet 19 = sixClasses := by
  ext c
  constructor
  · exact S1_proj_subset 19 c
  · intro hc
    obtain ⟨sp, hsp, j, hj19, hne, heq⟩ := S1_proj_surj c hc
    unfold liftSet
    rw [Finset.mem_image]
    refine ⟨(sp, j), ?_, heq⟩
    rw [Finset.mem_filter, Finset.mem_product, List.mem_toFinset, Finset.mem_range]
    exact ⟨⟨hsp, hj19⟩, hne⟩

/-! ## 7. S3: CRT-local inverse-closure, saturated regime (R169 section 7) -/

/-- S3(b) core (R169 section 7): the full fiber {x : ZMod 64 | x = 1 mod 8}
is inverse-closed -- every element has its inverse in the fiber. -/
theorem fiber2_inv_closed : ∀ x : ZMod 64, x.val % 8 = 1 →
    ∃ y : ZMod 64, y.val % 8 = 1 ∧ x * y = 1 := by
  decide

/-- S3(c) core (R169 section 7): the full fiber {x : ZMod 27 | x = 1 mod 3}
is inverse-closed. -/
theorem fiber3_inv_closed : ∀ x : ZMod 27, x.val % 3 = 1 →
    ∃ y : ZMod 27, y.val % 3 = 1 ∧ x * y = 1 := by
  decide

end ESRefinedSieve
