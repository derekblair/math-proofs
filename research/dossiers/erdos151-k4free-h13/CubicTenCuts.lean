import MixedCatalog
import NineLinkPivot

open scoped BigOperators
namespace H13MixedComponents
open Finset NineLinkPivot
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : V → V → Prop) [DecidableRel G]

def cross (S T : Finset V) : ℕ := ((S ×ˢ T).filter (fun a => G a.1 a.2)).card

theorem cross_count (S T : Finset V) : cross G S T = ∑ v∈S, deg G T v := by
  simp only [cross,deg,near,card_eq_sum_ones,sum_filter,Finset.sum_product]

theorem cross_symm (sym : ∀ {a b}, G a b → G b a) (S T : Finset V) :
    cross G S T = cross G T S := by
  simp only [cross,card_eq_sum_ones,sum_filter,Finset.sum_product]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro y hy
  apply sum_congr rfl
  intro x hx
  by_cases h : G x y
  · simp [h,show G y x from sym h]
  · simp [h,show ¬G y x from fun g => h (sym g)]

theorem cross_total (S : Finset V) (cube : ∀ v, deg G univ v = 3) :
    (∑ v∈S, deg G S v) + cross G S (univ \ S) = 3*S.card := by
  rw [cross_count,←sum_add_distrib]
  have row (v : V) : deg G S v + deg G (univ \ S) v = 3 := by
    have hh := cube v
    have z : near G S v ⊆ near G univ v := by
      intro b hb
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hb).2⟩
    have he : (near G univ v) \ (near G S v) = near G (univ \ S) v := by
      ext b
      simp only [near,mem_sdiff,mem_filter,mem_univ,true_and]
      tauto
    have hc := card_sdiff_of_subset z
    rw [he] at hc
    change deg G (univ \ S) v = deg G univ v - deg G S v at hc
    have hh' : deg G S v ≤ deg G univ v := card_le_card z
    omega
  rw [sum_congr rfl (fun v _ => row v)]
  simp [Nat.mul_comm]

/-- Small side of a cubic triangle-free cut has at least three exits. -/
theorem cubic_small_cut (irr : ∀ a, ¬G a a)
    (tf : ∀ x a b, G x a → G x b → ¬G a b)
    (cube : ∀ v, deg G univ v=3) (S : Finset V)
    (pos : 0<S.card) (small : S.card≤5) :
    3 ≤ cross G S (univ \ S) := by
  have total := cross_total G S cube
  have global (v : V) : deg G S v ≤ 3 := by
    rw [← cube v]
    apply card_le_card
    exact fun x hx => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
  have loc (v : V) (hv : v∈S) : deg G S v ≤ S.card-1 := by
    rw [← card_erase_of_mem hv]
    apply card_le_card
    intro a ha
    exact mem_erase.mpr ⟨fun h=>irr v (h ▸ (mem_filter.mp ha).2),(mem_filter.mp ha).1⟩
  by_cases hsmall : S.card ≤ 3
  · have ub := (sum_le_sum loc : (∑ v∈S, deg G S v) ≤ ∑ _v∈S, (S.card-1))
    simp at ub
    have hs : S.card=1 ∨ S.card=2 ∨ S.card=3 := by omega
    rcases hs with hs|hs|hs <;> rw [hs] at ub total <;> omega
  by_cases pivot : ∃ x∈S, deg G S x=3
  · obtain ⟨x,hx,degree⟩ := pivot
    let A := near G S x
    have hA : A⊆S := filter_subset _ _
    have hc : A.card=3 := degree
    have ul (y : V) (hy : y∈A) : deg G S y ≤ S.card-3 := by
      rw [←hc,←card_sdiff_of_subset hA]
      apply card_le_card
      intro z hz
      refine mem_sdiff.mpr ⟨(mem_filter.mp hz).1,?_⟩
      intro hz'
      exact tf x y z (mem_filter.mp hy).2 (mem_filter.mp hz').2 (mem_filter.mp hz).2
    have ur (y : V) (_hy : y∈S \ A) : deg G S y≤3 := global y
    have hL := (sum_le_sum ul : (∑ y∈A, deg G S y) ≤ ∑ _y∈A, (S.card-3))
    have hR := (sum_le_sum ur : (∑ y∈S\A, deg G S y) ≤ ∑ _y∈S\A, 3)
    simp [hc,card_sdiff_of_subset hA,Nat.mul_comm] at hL hR
    rw [←sum_sdiff hA (f := deg G S)] at total
    have hs : S.card=4 ∨ S.card=5 := by omega
    rcases hs with hs|hs <;> rw [hs] at hL hR total <;> omega
  · have ul : ∀ v∈S, deg G S v≤2 := by
      intro v hv
      have hg := global v
      by_contra h
      exact pivot ⟨v,hv,by omega⟩
    have hh := (sum_le_sum ul : (∑ v∈S, deg G S v) ≤ ∑ _v∈S, 2)
    simp at hh
    omega

theorem cubic_ten_cut (sym : ∀ {a b}, G a b → G b a)
    (irr : ∀ a, ¬G a a) (tf : ∀ x a b, G x a → G x b → ¬G a b)
    (cube : ∀ v, deg G univ v=3) (n : Fintype.card V=10)
    (S : Finset V) (pos : S.Nonempty) (comp : ∃ a,a∉S) :
    3 ≤ cross G S (univ \ S) := by
  by_cases h : S.card≤5
  · exact cubic_small_cut G irr tf cube S (card_pos.mpr pos) h
  · let T := (univ : Finset V) \ S
    have hT : T.card≤5 := by
      simp [T,card_sdiff_of_subset (subset_univ S),n]
      omega
    have hpos : 0<T.card := by
      obtain ⟨a,ha⟩ := comp
      exact card_pos.mpr ⟨a,by simp [T,ha]⟩
    have hcut := cubic_small_cut G irr tf cube T hpos hT
    have hh : (univ : Finset V) \ T = S := by
      ext v; simp [T]
    rw [hh,cross_symm G sym T S] at hcut
    exact hcut

#print axioms cubic_ten_cut
end H13MixedComponents
