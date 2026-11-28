import NineLinkPivot
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Card

namespace TwoChargedPivots
set_option linter.unusedSectionVars false
open Finset NineLinkPivot
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Both parts of the ambient link are independent. -/
def Bicuts (G : V → V → Prop) (S : Finset V) : Prop :=
  ∃ P Q : Finset V, Disjoint P Q ∧ P ∪ Q = S ∧
    (∀ a ∈ P, ∀ b ∈ P, ¬ G a b) ∧ (∀ a ∈ Q, ∀ b ∈ Q, ¬ G a b)

theorem near_mem (G : V → V → Prop) [DecidableRel G] (S : Finset V) (x y : V) :
    y ∈ near G S x ↔ y ∈ S ∧ G x y := by simp [near]

theorem induced_disjoint_cut (G : V → V → Prop) [DecidableRel G] (S : Finset V)
    (hS : S.card = 10)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, G x a → G x b → ¬G a b)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxyne : x ≠ y) (hxy : ¬ G x y)
    (hx4 : deg G S x = 4) (hy4 : deg G S y = 4)
    (hd : Disjoint (near G S x) (near G S y)) : Bicuts G S := by
  let T := near G S x
  let R := near G S y
  have h1 : x ∉ T := by simp [T,near_mem,irr]
  have h2 : x ∉ R := by simp [R,near_mem,show ¬G y x from fun h => hxy (sym h)]
  have h3 : y ∉ T := by simp [T,near_mem,hxy]
  have h4 : y ∉ R := by simp [R,near_mem,irr]
  let P := insert x R
  let Q := insert y T
  have hdis : Disjoint P Q := by
    rw [disjoint_left]
    intro z hz hz'
    rcases mem_insert.mp hz with rfl|hR <;> rcases mem_insert.mp hz' with hxy'|hT
    · exact hxyne hxy'
    · exact h1 hT
    · exact h4 (hxy' ▸ hR)
    · exact disjoint_left.mp hd hT hR
  have hcP : P.card = 5 := by
    rw [show P = insert x R from rfl,card_insert_of_notMem h2]
    change deg G S y + 1 = 5
    omega
  have hcQ : Q.card = 5 := by
    rw [show Q = insert y T from rfl,card_insert_of_notMem h3]
    change deg G S x + 1 = 5
    omega
  refine ⟨P,Q,hdis,?_,?_,?_⟩
  · apply eq_of_subset_of_card_le
    · exact union_subset (insert_subset_iff.mpr ⟨hx,filter_subset _ _⟩)
        (insert_subset_iff.mpr ⟨hy,filter_subset _ _⟩)
    · rw [card_union_of_disjoint hdis,hcP,hcQ,hS]
  · intro a ha b hb hab
    change a ∈ insert x R at ha
    change b ∈ insert x R at hb
    rcases mem_insert.mp ha with ha|ha <;> rcases mem_insert.mp hb with hb|hb
    · subst a; subst b; exact irr _ hab
    · subst a
      exact disjoint_left.mp hd ((near_mem G S x b).mpr
        ⟨((near_mem G S y b).mp hb).1,hab⟩) hb
    · subst b
      exact disjoint_left.mp hd ((near_mem G S x a).mpr
        ⟨((near_mem G S y a).mp ha).1,sym hab⟩) ha
    · exact tf y hy a ((near_mem G S y a).mp ha).1 b ((near_mem G S y b).mp hb).1
        ((near_mem G S y a).mp ha).2 ((near_mem G S y b).mp hb).2 hab
  · intro a ha b hb hab
    change a ∈ insert y T at ha
    change b ∈ insert y T at hb
    rcases mem_insert.mp ha with ha|ha <;> rcases mem_insert.mp hb with hb|hb
    · subst a; subst b; exact irr _ hab
    · subst a
      exact disjoint_left.mp hd hb ((near_mem G S y b).mpr
        ⟨((near_mem G S x b).mp hb).1,hab⟩)
    · subst b
      exact disjoint_left.mp hd ha ((near_mem G S y a).mpr
        ⟨((near_mem G S x a).mp ha).1,sym hab⟩)
    · exact tf x hx a ((near_mem G S x a).mp ha).1 b ((near_mem G S x b).mp hb).1
        ((near_mem G S x a).mp ha).2 ((near_mem G S x b).mp hb).2 hab

#print axioms induced_disjoint_cut

private theorem near_split (G : V → V → Prop) [DecidableRel G] (v : V)
    (P Q : Finset V) (hd : Disjoint P Q) :
    deg G (P ∪ Q) v = deg G P v + deg G Q v := by
  unfold deg near
  rw [filter_union,card_union_of_disjoint]
  exact (hd.mono (filter_subset _ _) (filter_subset _ _))

set_option maxHeartbeats 550000 in
private theorem one_common_degree_sum (G : V → V → Prop) [DecidableRel G] (S : Finset V)
    (hS : S.card = 10)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, G x a → G x b → ¬ G a b)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxyne : x ≠ y) (hxy : ¬ G x y)
    (hx4 : deg G S x = 4) (hy4 : deg G S y = 4)
    (hinter : ((near G S x) ∩ (near G S y)).card = 1)
    (xCap : ∀ z ∈ S, z ≠ x → ¬G x z → deg G (near G S x) z ≤ 1)
    (yCap : ∀ z ∈ S, z ≠ y → ¬G y z → deg G (near G S y) z ≤ 1) :
    (∑ v ∈ S, deg G S v) ≤ 26 := by
  classical
  let T := near G S x
  let R := near G S y
  let B := R \ T
  have hT : T ⊆ S := filter_subset _ _
  have hR : R ⊆ S := filter_subset _ _
  have hBx : x ∉ B := by simp [B,R,near_mem,show ¬G y x from fun h => hxy (sym h)]
  have hBy : y ∉ B := by simp [B,R,near_mem,irr]
  have hTx : x ∉ T := by simp [T,near_mem,irr]
  have hTy : y ∉ T := by simp [T,near_mem,hxy]
  have hRx : x ∉ R := by simp [R,near_mem,show ¬G y x from fun h => hxy (sym h)]
  have hRy : y ∉ R := by simp [R,near_mem,irr]
  have hcT : T.card = 4 := hx4
  have hcR : R.card = 4 := hy4
  have hI : (T ∩ R).card = 1 := hinter
  have hcTR : (T ∪ R).card = 7 := by
    have hh := card_union_add_card_inter T R
    omega
  have hcB : B.card = 3 := by
    rw [show B = R \ T from rfl,card_sdiff]
    omega
  let M := insert x (insert y (T ∪ R))
  have hM : M ⊆ S := insert_subset_iff.mpr ⟨hx,insert_subset_iff.mpr ⟨hy,union_subset hT hR⟩⟩
  have hMc : M.card = 9 := by
    have hn1 : y ∉ T ∪ R := by simp [hTy,hRy]
    have hn2 : x ∉ insert y (T ∪ R) := by simp [hxyne,hTx,hRx]
    simp [M,card_insert_of_notMem hn2,card_insert_of_notMem hn1,hcTR]
  have hPc : (S \ M).card = 1 := by rw [card_sdiff_of_subset hM,hS,hMc]
  obtain ⟨p,hp⟩ := card_eq_one.mp hPc
  have hpS : p ∈ S := (mem_sdiff.mp (by rw [hp]; exact mem_singleton_self p)).1
  have hpM : p ∉ M := (mem_sdiff.mp (by rw [hp]; exact mem_singleton_self p)).2
  have hpFacts : p ≠ x ∧ p ≠ y ∧ p ∉ T ∧ p ∉ R := by
    simpa [M,not_or] using hpM
  have hTB : Disjoint T B := disjoint_left.mpr
    (fun v hvT hvB => (mem_sdiff.mp hvB).2 hvT)
  have hBp : p ∉ B := fun h => hpFacts.2.2.2 (mem_sdiff.mp h).1
  have hpart : S = (insert x T) ∪ insert y (insert p B) := by
    ext v
    simp only [mem_union,mem_insert]
    constructor
    · intro hv
      by_cases ht : v ∈ T
      · exact Or.inl (Or.inr ht)
      by_cases hr : v ∈ R
      · exact Or.inr (Or.inr (Or.inr (mem_sdiff.mpr ⟨hr,ht⟩)))
      by_cases hxv : v=x
      · exact Or.inl (Or.inl hxv)
      by_cases hyv : v=y
      · exact Or.inr (Or.inl hyv)
      have hm : v ∉ M := by simp [M,hxv,hyv,ht,hr]
      have hz : v ∈ S \ M := mem_sdiff.mpr ⟨hv,hm⟩
      rw [hp] at hz
      exact Or.inr (Or.inr (Or.inl (mem_singleton.mp hz)))
    · rintro ((rfl|ht)|(rfl|rfl|hb))
      · exact hx
      · exact hT ht
      · exact hy
      · exact hpS
      · exact hR (mem_sdiff.mp hb).1
  let U := S \ insert x T
  have hUT : U = insert y (insert p B) := by
    ext v
    change v ∈ S \ insert x T ↔ v ∈ insert y (insert p B)
    rw [mem_sdiff, hpart, mem_union]
    constructor
    · rintro ⟨hv,hn⟩
      exact hv.resolve_left hn
    · intro hv
      refine ⟨Or.inr hv,?_⟩
      rcases mem_insert.mp hv with hv|hv
      · subst v
        simp [hxyne.symm,hTy]
      · rcases mem_insert.mp hv with hv|hv
        · subst v
          simp [hpFacts.1,hpFacts.2.2.1]
        · simp [show v ≠ x from fun he => hBx (he ▸ hv),(mem_sdiff.mp hv).2]
  have hpy : y ∉ insert p B := by simp [hpFacts.2.1.symm,hBy]
  have hpNT : deg G T p ≤ 1 :=
    xCap p hpS hpFacts.1 (fun hh => hpFacts.2.2.1 ((near_mem _ _ _ _).mpr ⟨hpS,hh⟩))
  have hpNR : deg G R p ≤ 1 :=
    yCap p hpS hpFacts.2.1 (fun hh => hpFacts.2.2.2 ((near_mem _ _ _ _).mpr ⟨hpS,hh⟩))
  have hpb : deg G B p ≤ 1 := by
    apply le_trans (b := deg G R p) _ hpNR
    apply card_le_card
    intro v hv
    exact (near_mem G R p v).mpr ⟨(mem_sdiff.mp ((near_mem G B p v).mp hv).1).1,
      ((near_mem G B p v).mp hv).2⟩
  have hyp : ¬ G y p := fun hg => hpFacts.2.2.2 ((near_mem _ _ _ _).mpr ⟨hpS,hg⟩)
  have hxp : ¬ G x p := fun hg => hpFacts.2.2.1 ((near_mem _ _ _ _).mpr ⟨hpS,hg⟩)
  have hpRows : deg G S p = deg G T p + deg G B p := by
    have heq : near G S p = near G (T ∪ B) p := by
      ext v
      simp only [near_mem,mem_union]
      constructor
      · rintro ⟨hv,hg⟩
        have hh : v ∈ (insert x T) ∪ insert y (insert p B) := hpart ▸ hv
        rcases mem_union.mp hh with hh|hh
        · rcases mem_insert.mp hh with he|ht
          · subst v
            exact (hxp (sym hg)).elim
          · exact ⟨Or.inl ht,hg⟩
        · rcases mem_insert.mp hh with he|hh
          · subst v
            exact (hyp (sym hg)).elim
          · rcases mem_insert.mp hh with he|hb
            · subst v
              exact (irr p hg).elim
            · exact ⟨Or.inr hb,hg⟩
      · rintro ⟨ht|hb,hg⟩
        · exact ⟨hT ht,hg⟩
        · exact ⟨hR (mem_sdiff.mp hb).1,hg⟩
    unfold deg
    rw [heq]
    exact near_split G p T B hTB
  have hyT : deg G T y = 1 := by
    have hyy : near G T y = T ∩ R := by
      ext v
      simp only [near_mem,mem_inter]
      exact ⟨fun h => ⟨h.1,(near_mem G S y v).mpr ⟨hT h.1,h.2⟩⟩,
        fun h => ⟨h.1,((near_mem G S y v).mp h.2).2⟩⟩
    change (near G T y).card = 1
    rw [hyy,hI]
  let zeta := fun (b : V) => if G p b then (1:ℕ) else 0
  have hBRows : ∀ b ∈ B, deg G S b + deg G T b ≤ 3 + zeta b := by
    intro b hb
    have hbR := (mem_sdiff.mp hb).1
    have hbS := (near_mem _ _ _ _).mp hbR |>.1
    have hyb := (near_mem _ _ _ _).mp hbR |>.2
    have hbT := (mem_sdiff.mp hb).2
    have hxb : ¬ G x b := fun h => hbT ((near_mem _ _ _ _).mpr ⟨hbS,h⟩)
    have hbt := xCap b hbS (fun h => hBx (h ▸ hb)) hxb
    have hbn : ∀ v ∈ B, ¬ G b v := by
      intro v hv
      have hvR := (near_mem _ _ _ _).mp (mem_sdiff.mp hv).1
      exact tf y hy b hbS v hvR.1 hyb hvR.2
    have hd : near G S b ⊆ (insert y (near G T b)) ∪ near G {p} b := by
      intro v hv
      obtain ⟨hs,hg⟩ := (near_mem _ _ _ _).mp hv
      rw [hpart] at hs
      simp only [mem_union,mem_insert] at hs ⊢
      rcases hs with (rfl|ht)|(rfl|rfl|hB)
      · exact (hxb (sym hg)).elim
      · exact Or.inl (Or.inr ((near_mem _ _ _ _).mpr ⟨ht,hg⟩))
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ((near_mem _ _ _ _).mpr ⟨by simp,hg⟩)
      · exact (hbn _ hB hg).elim
    have hh := (card_le_card hd).trans (card_union_le _ _)
    have hi : (insert y (near G T b)).card ≤ deg G T b + 1 := card_insert_le _ _
    have hz : (near G {p} b).card = zeta b := by
      by_cases h : G p b
      · have h' : G b p := sym h
        simp [near,zeta,h,h',filter_singleton]
      · have h' : ¬ G b p := fun hr => h (sym hr)
        simp [near,zeta,h,h',filter_singleton]
    change deg G S b ≤ (insert y (near G T b)).card + (near G {p} b).card at hh
    change deg G T b ≤ 1 at hbt
    omega
  have hz : (∑ b ∈ B, zeta b) = deg G B p := by
    unfold zeta deg near
    rw [card_eq_sum_ones,sum_filter]
  have hbs := (sum_le_sum hBRows :
    (∑ b ∈ B, (deg G S b + deg G T b)) ≤ ∑ b ∈ B, (3 + zeta b))
  have hrhs : (∑ b ∈ B, (3 + zeta b)) = 9 + deg G B p := by
    rw [sum_add_distrib,hz]
    simp [hcB]
  rw [hrhs] at hbs
  have hedges := degree_sum G sym irr S tf x hx
  change (∑ v ∈ S, deg G S v) = 2 * deg G S x +
    ∑ v ∈ U, (deg G S v + deg G T v) at hedges
  rw [hUT,sum_insert hpy,sum_insert hBp,hx4,hy4,hyT,hpRows] at hedges
  omega

theorem ten_link_two_pivot_dichotomy (G : V → V → Prop) [DecidableRel G] (S : Finset V)
    (hS : S.card = 10)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (tf : ∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, G x a → G x b → ¬ G a b)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxyne : x ≠ y) (hxy : ¬ G x y)
    (hx4 : deg G S x = 4) (hy4 : deg G S y = 4)
    (xCap : ∀ z ∈ S, z ≠ x → ¬G x z → deg G (near G S x) z ≤ 1)
    (yCap : ∀ z ∈ S, z ≠ y → ¬G y z → deg G (near G S y) z ≤ 1) :
    Bicuts G S ∨ (∑ v ∈ S, deg G S v) ≤ 26 := by
  by_cases hd : Disjoint (near G S x) (near G S y)
  · exact Or.inl (induced_disjoint_cut G S hS sym irr tf hx hy hxyne hxy hx4 hy4 hd)
  · have hu := xCap y hy hxyne.symm hxy
    have hEq : near G (near G S x) y = (near G S x) ∩ (near G S y) := by
      ext v
      simp only [near_mem,mem_inter]
      tauto
    rw [deg,hEq] at hu
    have hp : 0 < ((near G S x) ∩ (near G S y)).card := by
      by_contra hn
      exact hd (disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega)))
    exact Or.inr (one_common_degree_sum G S hS sym irr tf hx hy hxyne hxy hx4 hy4 (by omega) xCap yCap)

#print axioms ten_link_two_pivot_dichotomy
end TwoChargedPivots
