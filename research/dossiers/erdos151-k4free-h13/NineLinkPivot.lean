import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff
import Lean.Elab.Tactic.Omega

namespace NineLinkPivot
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

def near (G : V → V → Prop) [DecidableRel G] (S : Finset V) (x : V) : Finset V :=
  S.filter (G x)

def deg (G : V → V → Prop) [DecidableRel G] (S : Finset V) (x : V) : ℕ :=
  (near G S x).card

private theorem transposed (G : V → V → Prop) [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (T U : Finset V) :
    (∑ x ∈ T, deg G U x) = ∑ y ∈ U, deg G T y := by
  simp only [deg,near,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : G x y
  · simp [h,sym h]
  · simp [h,show ¬ G y x from fun hr => h (sym hr)]

/-- The degree sum in a triangle-free link, decomposed into a pivot,
its independent neighborhood, and its nonneighbors. -/
theorem degree_sum (G : V → V → Prop) [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (S : Finset V)
    (tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, G x a → G x b → ¬G a b)
    (x : V) (hx : x ∈ S) :
    let T := near G S x
    let U := S \ insert x T
    (∑ y ∈ S, deg G S y) = 2 * deg G S x + ∑ y ∈ U, (deg G S y + deg G T y) := by
  dsimp only
  let T := near G S x
  let U := S \ insert x T
  have hT : T ⊆ S := filter_subset _ _
  have hTx : x ∉ T := by simp [T,near,irr]
  have hsub : insert x T ⊆ S := insert_subset_iff.mpr ⟨hx,hT⟩
  have hRow : ∀ y ∈ T, deg G S y = 1 + deg G U y := by
    intro y hy
    have hxy := (mem_filter.mp hy).2
    have hyx := sym hxy
    have heq : near G S y = insert x (near G U y) := by
      ext z
      simp only [near,mem_filter,mem_insert,U,mem_sdiff]
      constructor
      · rintro ⟨hz,hG⟩
        by_cases hzx : z = x
        · exact Or.inl hzx
        · have hzT : z ∉ T := fun hh => tf x hx y (hT hy) z hz hxy (mem_filter.mp hh).2 hG
          exact Or.inr ⟨⟨hz,by simp [hzx,hzT]⟩,hG⟩
      · rintro (rfl|⟨⟨hz,_⟩,hG⟩)
        · exact ⟨hx,hyx⟩
        · exact ⟨hz,hG⟩
    have hn : x ∉ near G U y := by simp [near,U]
    rw [deg,heq,card_insert_of_notMem hn,deg,Nat.add_comm]
  have hAll : (∑ y ∈ S, deg G S y) = (∑ y ∈ U, deg G S y) +
      (deg G S x + ∑ y ∈ T, deg G S y) := by
    rw [← sum_sdiff hsub (f := deg G S), sum_insert hTx]
  have hSum : (∑ y ∈ T, deg G S y) = deg G S x + ∑ y ∈ T, deg G U y := by
    rw [show (∑ y ∈ T, deg G S y) = ∑ y ∈ T, (1 + deg G U y) by
      exact sum_congr rfl hRow, sum_add_distrib]
    simp [deg,T]
  change (∑ y ∈ S, deg G S y) = 2 * deg G S x + ∑ y ∈ U, (deg G S y + deg G T y)
  rw [hAll,hSum,transposed G sym T U,sum_add_distrib]
  omega

/-- Ambient-induced nine-vertex pivot. Degree sum ≥28 means at least
14 undirected edges. The selected pair is actually nonadjacent in G. -/
theorem ambient_nine_link_pivot (G : V → V → Prop) [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (S : Finset V)
    (tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, G x a → G x b → ¬G a b)
    (hS : S.card = 9)
    (dense : 28 ≤ ∑ y ∈ S, deg G S y) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ¬ G x y ∧ 4 ≤ deg G S x ∧
      (4 ≤ deg G S y ∨ (3 ≤ deg G S y ∧ 2 ≤ deg G (near G S x) y)) := by
  classical
  obtain ⟨x,hx,hd⟩ : ∃ x ∈ S, 4 ≤ deg G S x := by
    by_contra hn
    have ub : ∀ x ∈ S, deg G S x ≤ 3 := by
      intro x hx
      by_contra h
      exact hn ⟨x,hx,by omega⟩
    have hh := (sum_le_sum ub : (∑ x ∈ S, deg G S x) ≤ ∑ _x ∈ S, 3)
    simp [hS] at hh
    omega
  let T := near G S x
  let U := S \ insert x T
  have hsub : insert x T ⊆ S := insert_subset_iff.mpr ⟨hx,filter_subset _ _⟩
  have hTx : x ∉ T := by simp [T,near,irr]
  have hU : U.card = 8 - deg G S x := by
    rw [show U = S \ insert x T from rfl,card_sdiff_of_subset hsub,card_insert_of_notMem hTx,hS]
    simp [deg,T]
  by_contra hn
  have ub : ∀ y ∈ U, deg G S y + deg G T y ≤ 4 := by
    intro y hy
    have hs := (mem_sdiff.mp hy).1
    have ht := (mem_sdiff.mp hy).2
    have hne : x ≠ y := by
      intro he
      subst y
      exact ht (mem_insert_self _ _)
    have hxy : ¬ G x y := by
      intro h
      exact ht (mem_insert_of_mem (mem_filter.mpr ⟨hs,h⟩))
    have hy3 : deg G S y ≤ 3 := by
      by_contra hh
      exact hn ⟨x,hx,y,hs,hne,hxy,hd,Or.inl (by omega)⟩
    have hdT : deg G T y ≤ deg G S y :=
      card_le_card (fun z hz => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hz).1).1,(mem_filter.mp hz).2⟩)
    by_cases hy : 3 ≤ deg G S y
    · have ht1 : deg G T y ≤ 1 := by
        by_contra hh
        exact hn ⟨x,hx,y,hs,hne,hxy,hd,Or.inr ⟨hy,by change 2 ≤ deg G T y; omega⟩⟩
      omega
    · omega
  have hsum := degree_sum G sym irr S tf x hx
  have hb := (sum_le_sum ub :
      (∑ y ∈ U, (deg G S y + deg G T y)) ≤ ∑ _y ∈ U, 4)
  have hmax : deg G S x ≤ 8 := by
    have hh := card_le_card hsub
    rw [card_insert_of_notMem hTx,hS] at hh
    change deg G S x + 1 ≤ 9 at hh
    omega
  change (∑ y ∈ S, deg G S y) =
    2 * deg G S x + ∑ y ∈ U, (deg G S y + deg G T y) at hsum
  simp [hU,Nat.mul_comm] at hb
  omega

#print axioms ambient_nine_link_pivot
end NineLinkPivot
