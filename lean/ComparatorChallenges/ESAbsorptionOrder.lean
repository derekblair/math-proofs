import Mathlib

/-! # ES absorption poset, redundancy collapse, and singleton factorization (ES-005) -/

open Finset

namespace ESAbsorptionOrder

variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]

structure Group (Cell : Type*) where
  C : Finset Cell
  p : Bool
  deriving DecidableEq

def absorpLE (G H : Group Cell) : Prop :=
  G.C ⊆ H.C ∧ (G.p → H.p)

def unionDatum (S : Finset (Group Cell)) : Finset Cell × Finset Cell :=
  (S.biUnion Group.C, S.biUnion fun G => if G.p then G.C else ∅)

theorem absorp_datum_iff {G H : Group Cell} (hG : G.C.Nonempty) :
    unionDatum ({G, H} : Finset (Group Cell)) = unionDatum {H} ↔ absorpLE G H := by
  sorry

def IsCore (S C : Finset (Group Cell)) : Prop :=
  C ⊆ S ∧ unionDatum C = unionDatum S

noncomputable def minCoreSize (S : Finset (Group Cell)) : ℕ :=
  sInf { n : ℕ | ∃ C : Finset (Group Cell), IsCore S C ∧ C.card = n }

noncomputable def rho (S : Finset (Group Cell)) : ℕ :=
  S.card - minCoreSize S

theorem rho_absorption_collapse {G H : Group Cell} (hle : absorpLE G H) (hne : G ≠ H)
    (hH : H.C.Nonempty) :
    rho ({G, H} : Finset (Group Cell)) = 1 := by
  sorry

theorem absorption_collapse_unique_core {G H : Group Cell} (hle : absorpLE G H)
    (hne : G ≠ H) (hH : H.C.Nonempty)
    {C : Finset (Group Cell)}
    (hcore : IsCore ({G, H} : Finset (Group Cell)) C) (hcard : C.card = 1) :
    C = {H} := by
  sorry

def IsUCover (S : Finset (Group Cell)) : Prop :=
  (unionDatum S).1 = Finset.univ

def IsMinimalUCover (S : Finset (Group Cell)) : Prop :=
  IsUCover S ∧ ∀ C : Finset (Group Cell), C ⊂ S → ¬ IsUCover C

theorem singleton_factorization
    (S0 : Finset Cell)
    (𝒢 : Finset (Group Cell)) (hS0 : ∀ c ∈ S0, ∀ g ∈ 𝒢, g.C ≠ {c})
    {S : Finset (Group Cell)} (hS𝒢 : S ⊆ 𝒢) (hmin : IsMinimalUCover S) :
    let T := S.filter (fun g => g.C.card ≠ 1)
    let U := S.filter (fun g => g.C.card = 1)
    S = T ∪ U ∧ Disjoint T U ∧
    (∀ H ∈ T, ∃ x ∈ H.C, ∀ K ∈ T, x ∈ K.C → K = H) ∧
    (∀ c, c ∉ (unionDatum T).1 → ∃! g, g ∈ U ∧ g.C = {c}) ∧
    S0 ⊆ (unionDatum T).1 := by
  sorry

end ESAbsorptionOrder
