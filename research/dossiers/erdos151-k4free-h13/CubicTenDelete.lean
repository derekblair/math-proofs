import CubicTenCuts
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open scoped BigOperators
namespace H13MixedComponents
open Finset NineLinkPivot
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : V → V → Prop) [DecidableRel G]

theorem cross_union (A B C : Finset V) (dis : Disjoint B C) :
    cross G A (B ∪ C) = cross G A B + cross G A C := by
  simp only [cross_count,←sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  unfold deg near
  rw [filter_union,card_union_of_disjoint (dis.mono (filter_subset _ _) (filter_subset _ _))]

theorem cross_mono (A B C : Finset V) (sub : B⊆C) :
    cross G A B ≤ cross G A C := by
  rw [cross_count,cross_count]
  exact sum_le_sum (fun v _ => card_le_card
    (fun w h => mem_filter.mpr ⟨sub (mem_filter.mp h).1,(mem_filter.mp h).2⟩))

theorem induced_sum_even (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (S : Finset V) :
    ∃ m : ℕ, (∑ v∈S, deg G S v) = 2*m := by
  let H : SimpleGraph ↥S :=
    ⟨fun a b => G a.val b.val,⟨fun _ _ h=>sym h⟩,⟨fun a h=>irr a.val h⟩⟩
  letI : DecidableRel H.Adj := fun a b => inferInstanceAs (Decidable (G a.val b.val))
  let φ : ↥S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have value (v : ↥S) : H.degree v = deg G S v.val := by
    rw [←H.card_neighborFinset_eq_degree,←card_map φ]
    congr 1
    ext w
    constructor
    · intro h
      obtain ⟨a,ha,rfl⟩ := mem_map.mp h
      exact mem_filter.mpr ⟨a.property,(H.mem_neighborFinset v a).mp ha⟩
    · intro h
      have hw := mem_filter.mp h
      exact mem_map.mpr ⟨⟨w,hw.1⟩,(H.mem_neighborFinset v ⟨w,hw.1⟩).mpr hw.2,rfl⟩
  refine ⟨H.edgeFinset.card,?_⟩
  rw [←H.sum_degrees_eq_twice_card_edges]
  simp_rw [value]
  exact (sum_attach S (deg G S)).symm

private theorem cross_zero (S T : Finset V)
    (none : ∀ a∈S, ∀ b∈T, ¬ G a b) : cross G S T = 0 := by
  rw [cross_count]
  apply sum_eq_zero
  intro a ha
  unfold deg near
  rw [card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro b hb
  exact none a ha b (mem_filter.mp hb).1 (mem_filter.mp hb).2

/-- In a simple symmetric triangle-free cubic graph on ten vertices,
deleting at most two vertices leaves it connected. -/
theorem cubic_ten_delete (sym : ∀ {a b}, G a b → G b a)
    (irr : ∀ a, ¬G a a) (tf : ∀ x a b, G x a → G x b → ¬G a b)
    (cube : ∀ v, deg G univ v=3) (n : Fintype.card V=10)
    (U : Finset V) (small : U.card≤2) (a b : V) (ha : a∉U) (hb : b∉U) :
    Relation.ReflTransGen (fun x y => G x y ∧ x∉U ∧ y∉U) a b := by
  classical
  let R := fun x y => G x y ∧ x∉U ∧ y∉U
  change Relation.ReflTransGen R a b
  by_contra bad
  let S := univ.filter (fun x => x∉U ∧ Relation.ReflTransGen R a x)
  let T := (univ : Finset V) \ (U∪S)
  have aS : a∈S := by simp [S,ha,Relation.ReflTransGen.refl]
  have bS : b∉S := by simp [S,bad]
  have bT : b∈T := by simp [T,hb,bS]
  have aT : a∉T := by simp [T,aS]
  have disUS : Disjoint U S := disjoint_left.mpr (fun v h hv => (mem_filter.mp hv).2.1 h)
  have disUT : Disjoint U T := disjoint_left.mpr (fun v h hv =>
    (mem_sdiff.mp hv).2 (mem_union_left _ h))
  have disST : Disjoint S T := disjoint_left.mpr (fun v h hv =>
    (mem_sdiff.mp hv).2 (mem_union_right _ h))
  have none : ∀ x∈S, ∀ y∈T, ¬ G x y := by
    intro x hx y hy h
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_sdiff.mp hy).2
    have hp := hx'.2.tail (show R x y from ⟨h,hx'.1,fun hv => hy' (mem_union_left _ hv)⟩)
    exact hy' (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,fun hv=>hy' (mem_union_left _ hv),hp⟩))
  have cutS := cubic_ten_cut G sym irr tf cube n S ⟨a,aS⟩ ⟨b,bS⟩
  have cutT := cubic_ten_cut G sym irr tf cube n T ⟨b,bT⟩ ⟨a,aT⟩
  have compS : (univ : Finset V) \ S = U ∪ T := by
    ext v
    have hx : v∈U → v∉S := fun h => disjoint_left.mp disUS h
    simp only [T,mem_sdiff,mem_union,mem_univ,true_and]
    tauto
  have compT : (univ : Finset V) \ T = U ∪ S := by
    ext v; simp [T]
  have zero := cross_zero G S T none
  rw [compS,cross_union G S U T disUT,zero,add_zero] at cutS
  rw [compT,cross_union G T U S disUS,cross_symm G sym T S,zero,add_zero] at cutT
  have joint : cross G S U + cross G T U ≤ 3*U.card := by
    rw [cross_symm G sym S U,cross_symm G sym T U,←cross_union G U S T disST]
    exact (cross_mono G U (S∪T) univ (subset_univ _)).trans
      (by rw [cross_count]; simp [cube,Nat.mul_comm])
  have eqU : U.card=2 := by omega
  have eqS : cross G S U = 3 := by omega
  have eqT : cross G T U = 3 := by omega
  have st : S.card+T.card=8 := by
    have t := card_sdiff_of_subset (subset_univ (U∪S))
    change T.card = (univ : Finset V).card - (U∪S).card at t
    rw [card_univ,n,card_union_of_disjoint disUS,eqU] at t
    have s := card_le_card (subset_univ (U∪S))
    rw [card_univ,n,card_union_of_disjoint disUS,eqU] at s
    omega
  have impossible (P : Finset V) (psmall : P.card ≤ 4) (pne : P.Nonempty)
      (out : cross G P (univ\P)=3) (toU : cross G P U=3) : False := by
    have sum := cross_total G P cube
    rw [out] at sum
    obtain ⟨m,hm⟩ := induced_sum_even G sym irr P
    rw [hm] at sum
    have opt : P.card=1 ∨ P.card=3 := by omega
    rcases opt with h1|h3
    · obtain ⟨p,rfl⟩ := card_eq_one.mp h1
      rw [cross_count,sum_singleton] at toU
      have h := card_le_card (filter_subset (G p) U)
      change deg G U p ≤ U.card at h
      omega
    · have md : ∀ x∈P, deg G P x ≤ 2 := by
        intro x hx
        have sub : near G P x ⊆ P.erase x := by
          intro y hy
          exact mem_erase.mpr ⟨fun eq=>irr x (eq ▸ (mem_filter.mp hy).2),(mem_filter.mp hy).1⟩
        exact (card_le_card sub).trans (by rw [card_erase_of_mem hx,h3])
      have full : ∀ x∈P, deg G P x = 2 := by
        intro x hx
        have decomp := sum_erase_add _ (fun y=>deg G P y) hx
        have hx2 := md x hx
        have total6 : (∑ y∈P, deg G P y) = 6 := by rw [hm]; omega
        rw [total6] at decomp
        have ub := (sum_le_sum (fun y hy => md y (mem_of_mem_erase hy)) :
          (∑ y∈P.erase x, deg G P y) ≤ ∑ _y∈P.erase x, 2)
        simp [card_erase_of_mem hx,h3] at ub
        omega
      obtain ⟨x,y,z,hxy,hxz,hyz,hh⟩ := card_eq_three.mp h3
      have all (v : V) (hv : v∈P) : near G P v=P.erase v := by
        apply eq_of_subset_of_card_le
        · intro t ht
          exact mem_erase.mpr ⟨fun eq=>irr v (eq ▸ (mem_filter.mp ht).2),(mem_filter.mp ht).1⟩
        · rw [card_erase_of_mem hv,h3]
          exact Nat.le_of_eq (full v hv).symm
      have xy : G x y := (mem_filter.mp (show y∈near G P x by
        rw [all x (by simp [hh]),hh]; simp [hxy.symm])).2
      have xz : G x z := (mem_filter.mp (show z∈near G P x by
        rw [all x (by simp [hh]),hh]; simp [hxz.symm])).2
      have yz : G y z := (mem_filter.mp (show z∈near G P y by
        rw [all y (by simp [hh]),hh]; simp [hyz.symm])).2
      exact tf x y z xy xz yz
  by_cases h : S.card≤4
  · exact impossible S h ⟨a,aS⟩ (by rw [compS,cross_union G S U T disUT,zero,add_zero,eqS]) eqS
  · have hh : T.card≤4 := by omega
    exact impossible T hh ⟨b,bT⟩ (by
      rw [compT,cross_union G T U S disUS,cross_symm G sym T S,zero,add_zero,eqT]) eqT

#print axioms cubic_ten_delete
end H13MixedComponents
