import Mathlib.Data.Finset.Card

namespace MixedTagBank

abbrev Label := Bool × Nat
structure Record where
  rank : Nat
  first : Nat
  last : Nat
  deriving DecidableEq

def Record.left (v : Record) : Label := (false,v.first)
def Record.right (v : Record) : Label := (true,v.last)

def avoids (bans : Finset Label) (v : Record) : Prop :=
  v.left ∉ bans ∧ v.right ∉ bans

theorem avoids_of_subset {B F : Finset Label} {v : Record} (h : B ⊆ F)
    (hv : avoids F v) : avoids B v :=
  ⟨fun hb => hv.1 (h hb),fun hb => hv.2 (h hb)⟩

/-- The local selector can be implemented by a single scan. Rank is
    ordinal in any total order refining weight and hop count. -/
def PickLaw (S : Finset Record) (pick : Finset Label → Option Record) : Prop :=
  (∀ B v, pick B=some v → v∈S ∧ avoids B v ∧
    ∀ w∈S, avoids B w → v.rank ≤ w.rank) ∧
  (∀ B, pick B=none → ∀ v∈S, ¬avoids B v)

def bank (pick : Finset Label → Option Record) : Nat → Finset Label → List Record
  | 0,B => (pick B).toList
  | d+1,B => match pick B with
    | none => []
    | some v => v :: (bank pick d (insert v.left B) ++ bank pick d (insert v.right B))

theorem size (pick : Finset Label → Option Record) (d : Nat) (B : Finset Label) :
    (bank pick d B).length+1 ≤ 2^(d+1) := by
  induction d generalizing B with
  | zero =>
    cases h : pick B <;> simp [bank,h,Option.toList]
  | succ d ih =>
    cases E : pick B with
    | none =>
      simp only [bank,E,List.length_nil,Nat.zero_add]
      exact Nat.one_le_pow _ 2 (by decide)
    | some v =>
      have hL := ih (insert v.left B)
      have hR := ih (insert v.right B)
      simp only [bank,E,List.length_cons,List.length_append,Nat.pow_succ]
      omega

private theorem step_card {F B : Finset Label} {j : Label}
    (jf : j ∈ F) (jb : j ∉ B) :
    (F \ insert j B).card+1 = (F \ B).card := by
  have jfb : j ∈ F \ B := Finset.mem_sdiff.mpr ⟨jf,jb⟩
  have E : F \ insert j B = (F \ B).erase j := by
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase]
    tauto
  rw [E]
  exact Finset.card_erase_add_one jfb

/-- For any target exclusion set of remaining size at most d, the bank
    contains a feasible candidate at least as good as any feasible witness. -/
theorem competes {S : Finset Record} {pick : Finset Label → Option Record}
    (law : PickLaw S pick) (d : Nat) {B F : Finset Label}
    (cover : B ⊆ F) (left : (F \ B).card ≤ d)
    {w : Record} (wS : w∈S) (wF : avoids F w) :
    ∃ v∈bank pick d B, v∈S ∧ avoids F v ∧ v.rank ≤ w.rank := by
  classical
  induction d generalizing B with
  | zero =>
    cases h : pick B with
    | none => exact False.elim (law.2 B h w wS (avoids_of_subset cover wF))
    | some v =>
      have V := law.1 B v h
      have EE : F \ B = ∅ := Finset.card_eq_zero.mp (by omega)
      have eq : F ⊆ B := Finset.sdiff_eq_empty_iff_subset.mp EE
      exact ⟨v,by simp [bank,h],V.1,avoids_of_subset eq V.2.1,V.2.2 w wS (avoids_of_subset cover wF)⟩
  | succ d ih =>
    cases h : pick B with
    | none => exact False.elim (law.2 B h w wS (avoids_of_subset cover wF))
    | some v =>
      have V := law.1 B v h
      by_cases L : v.left∈F
      · have c := step_card L V.2.1.1
        obtain ⟨z,zm,zS,zF,zrank⟩ := ih (Finset.insert_subset L cover) (by omega)
        exact ⟨z,by simp [bank,h,zm],zS,zF,zrank⟩
      · by_cases R : v.right∈F
        · have c := step_card R V.2.1.2
          obtain ⟨z,zm,zS,zF,zrank⟩ := ih (Finset.insert_subset R cover) (by omega)
          exact ⟨z,by simp [bank,h,zm],zS,zF,zrank⟩
        · exact ⟨v,by simp [bank,h],V.1,⟨L,R⟩,V.2.2 w wS (avoids_of_subset cover wF)⟩

theorem fifteen (pick : Finset Label → Option Record) :
    (bank pick 3 ∅).length ≤ 15 := by
  have h := size pick 3 ∅
  omega

end MixedTagBank

#print axioms MixedTagBank.competes
#print axioms MixedTagBank.fifteen
