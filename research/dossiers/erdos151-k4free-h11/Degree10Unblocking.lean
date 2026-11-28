import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Lean.Elab.Tactic.Omega

namespace Erdős151

variable {V : Type*}

/-- A set contains no forbidden complete subgraph of the specified family. -/
def Free (bad : Set (Set V)) (T : Set V) : Prop :=
  ∀ A ∈ bad, ¬ A ⊆ T

/-- If two distinct vertices can each individually be added to T but
not simultaneously, they must be adjacent. -/
theorem private_adjacent (bad : Set (Set V)) (adj : V → V → Prop)
    (T : Set V) (x y : V) (hxy : x ≠ y)
    (hc : ∀ A ∈ bad, ∀ u ∈ A, ∀ v ∈ A, u ≠ v → adj u v)
    (hx : Free bad (insert x T)) (hy : Free bad (insert y T))
    (hbad : ¬ Free bad (insert x (insert y T))) : adj x y := by
  classical
  by_contra ha
  apply hbad
  intro A hA hsub
  by_cases hmx : x ∈ A
  · apply hx A hA
    intro z hz
    obtain h | h := Set.mem_insert_iff.mp (hsub hz)
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · obtain e | e := Set.mem_insert_iff.mp h
      · subst z
        exact False.elim (ha (hc A hA x hmx y hz hxy))
      · exact Set.mem_insert_iff.mpr (Or.inr e)
  · apply hy A hA
    intro z hz
    obtain h | h := Set.mem_insert_iff.mp (hsub hz)
    · exact False.elim (hmx (h ▸ hz))
    · exact h

/-- Every private vertex is adjacent to the vertex whose deletion makes
its addition safe. -/
theorem private_adjacent_to_owner (bad : Set (Set V))
    (adj : V → V → Prop) (T : Set V) (x u : V) (hxu : x ≠ u)
    (hc : ∀ A ∈ bad, ∀ v ∈ A, ∀ z ∈ A, v ≠ z → adj v z)
    (hT : Free bad T)
    (hfree : Free bad (insert x (T \ {u})))
    (hbad : ¬ Free bad (insert x T)) : adj x u := by
  classical
  by_contra ha
  apply hbad
  intro A hA hsub
  by_cases hx : x ∈ A
  · apply hfree A hA
    intro z hz
    obtain h | h := Set.mem_insert_iff.mp (hsub hz)
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · apply Set.mem_insert_iff.mpr
      right
      refine ⟨h, ?_⟩
      intro hz'
      have he : z = u := Set.mem_singleton_iff.mp hz'
      subst z
      exact ha (hc A hA x hx u hz hxu)
  · apply hT A hA
    intro z hz
    obtain h | h := Set.mem_insert_iff.mp (hsub hz)
    · exact False.elim (hx (h ▸ hz))
    · exact h

/-- Doubled exterior-incidence inequality, with an arbitrary
neighborhood size D. -/
theorem exterior_incidence (X D I ell a b c d : ℕ)
    (hsmall : a+b+c ≤ D) (hlone : a+2*d ≤ ell)
    (hbase : 3*X ≤ I+2*a+b+c+d) :
    6*X ≤ 2*I+3*D+ell := by omega

/-- At n≥47 even the weakest admissible core degree gives
a contradiction with total incidence capacity. -/
theorem degree10_excluded (n r I ell : ℕ)
    (hn : 47 ≤ n) (hr : 8 ≤ r)
    (hmin : 6*(n-11) ≤ 2*I+30+ell)
    (hmax : I+2*r ≤ 90) (hslots : ell+7*r ≤ 90) : False := by omega

theorem post_price (amb core noniso alpha : ℕ)
    (hr : 8 ≤ core) (hca : core ≤ noniso) (hna : noniso ≤ amb)
    (ha : amb ≤ 9) (hα : 3 ≤ alpha)
    (hα' : 9 ≤ noniso → 4 ≤ alpha) (hprice : alpha+6 ≤ amb) :
    amb=9 ∧ core=8 ∧ noniso=8 ∧ alpha=3 := by
  have hx : ¬9 ≤ noniso := by
    intro hi
    have ht := hα' hi
    omega
  omega

/-- Individually unblocked vertices can be added together when independent. -/
theorem free_add_independent (bad : Set (Set V)) (adj : V → V → Prop)
    (T X : Set V)
    (hc : ∀ A ∈ bad, ∀ u ∈ A, ∀ v ∈ A, u ≠ v → adj u v)
    (hT : Free bad T) (hi : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ¬ adj x y)
    (hadd : ∀ x ∈ X, Free bad (insert x T)) : Free bad (T ∪ X) := by
  classical
  intro A hA hsub
  by_cases h : A ⊆ T
  · exact hT A hA h
  · have hp : ∃ x ∈ A, x ∉ T := by
      by_contra hh
      apply h
      intro x hx
      by_contra hxt
      exact hh ⟨x, hx, hxt⟩
    obtain ⟨x, hx, hxT⟩ := hp
    have hxX := (hsub hx).resolve_left hxT
    apply hadd x hxX A hA
    intro y hy
    by_cases hxy : x = y
    · subst y
      exact Set.mem_insert _ _
    · apply Set.mem_insert_iff.mpr
      right
      rcases hsub hy with h | h
      · exact h
      · exact False.elim (hi x hxX y h hxy (hc A hA x hx y hy hxy))

theorem degree9_excluded (n r I ell z a b c d : ℕ)
    (hn : 47 ≤ n) (hr : 8 ≤ r) (hz : z ≤ 3)
    (hp : 5*a+4*b+5*c ≤ 90) (hlone : a+2*d ≤ ell)
    (hbase : 3*(n-10-z) ≤ I+2*a+b+c+d)
    (hmax : I+3*r ≤ 81) (hslots : ell+8*r ≤ 81) : False := by omega

/-- Bounds z≤9 and b≤36 suffice; no exact R(3,4)=9 theorem needed. -/
theorem degree8_excluded (n I z b : ℕ)
    (hn : 47 ≤ n) (hz : z ≤ 9) (hb : b ≤ 36)
    (hbase : 3*(n-9-z) ≤ I+b) (hmax : I ≤ 40) : False := by omega

#print axioms free_add_independent
#print axioms degree9_excluded
#print axioms degree8_excluded

#print axioms private_adjacent
#print axioms private_adjacent_to_owner
#print axioms exterior_incidence
#print axioms degree10_excluded
#print axioms post_price
end Erdős151
