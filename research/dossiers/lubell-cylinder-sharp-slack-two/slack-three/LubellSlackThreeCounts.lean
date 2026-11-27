import JohnsonCounts
import LubellSlackTwo

namespace IU.Lubell
open Finset LubellSlackThree

private theorem between_count {X V : Finset Nat} {F : Family} {k : Nat}
    (hXV : X⊆V) (lo : ∀ g∈F, X⊆g) (hi : ∀ g∈F, g⊆V)
    (sz : ∀ g∈F, g.card=k) : F.card≤(V.card-X.card).choose (k-X.card) := by
  classical
  have inj : Set.InjOn (fun g : Finset Nat => g \ X) ↑F := by
    intro a ha b hb e
    have e' := congrArg (fun g : Finset Nat => X∪g) e
    rwa [union_sdiff_of_subset (lo _ ha),union_sdiff_of_subset (lo _ hb)] at e'
  have s : (F.image (fun g => g \ X))⊆(V \ X).powersetCard (k-X.card) := by
    intro g hg
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hg
    apply mem_powersetCard.mpr
    refine ⟨?_, by rw [card_sdiff_of_subset (lo _ hv),sz _ hv]⟩
    intro a ha
    obtain ⟨h1,h2⟩ := mem_sdiff.mp ha
    exact mem_sdiff.mpr ⟨hi _ hv h1,h2⟩
  have bound := card_le_card s
  rwa [card_image_of_injOn inj,card_powersetCard,card_sdiff_of_subset hXV] at bound

private theorem johnson_count_in (G : Finset Nat) (F : Family) (k : Nat)
    (hk : 1≤k) (ambient : ∀ g∈F, g⊆G) (sz : ∀ g∈F, g.card=k)
    (near : ∀ a∈F, ∀ b∈F, k-1≤(a∩b).card) :
    F.card≤max (G.card-(k-1)) (k+1) := by
  by_cases h : 1<F.card
  · obtain ⟨a,ha,_⟩ := one_lt_card.mp h
    rcases johnson_star_or_top F k hk h sz near with ⟨x,hx,X⟩|⟨v,hv,V⟩
    · have XG := (X a ha).trans (ambient a ha)
      have b := star_count G x F k (by omega) ambient X XG sz
      rw [hx] at b
      exact b.trans (le_max_left _ _)
    · exact (top_count v F k hv V sz).trans (le_max_right _ _)
  · omega

private theorem upper_from_top {F : Family} {t u : Nat}
    (V : IsIU F (t+u+3) t u) {Q A : Finset Nat} (qF : Q∈layer F (t+3)) (a : A∈F) :
    A⊆Q := by
  have q := from_layer qF
  have P := V.2 A a Q q.1
  have e := eq_of_subset_of_card_le (show Q⊆A∪Q from subset_union_right) (by omega)
  exact e.symm ▸ subset_union_left

private theorem lower_from_bottom {F : Family} {t u : Nat}
    (V : IsIU F (t+u+3) t u) {T A : Finset Nat} (tf : T∈layer F t) (a : A∈F) :
    T⊆A := by
  have tt := from_layer tf
  have P := V.2 T tt.1 A a
  have e := eq_of_subset_of_card_le (show T∩A⊆T from inter_subset_left) (by omega)
  exact e ▸ inter_subset_right

/-- Three coordinatewise Lubell layer-count caps cover every admissible
    family at excess three. The middle layers use the balanced conflict
    only when their separate Johnson bounds would allow both maxima. -/
theorem slack_three_count_cases {F : Family} {t u : Nat} (ht : 1≤t) (le : t≤u)
    (V : IsIU F (t+u+3) t u) :
    let B := (layer F t).card
    let A := (layer F (t+1)).card
    let C := (layer F (t+2)).card
    let H := (layer F (t+3)).card
    (B≤1 ∧ A≤3 ∧ C≤3 ∧ H≤1) ∨
    (B≤1 ∧ A≤u+3 ∧ C≤u+2 ∧ H=0) ∨
    (B=0 ∧ A≤t+2 ∧ C≤t+3 ∧ H≤1) := by
  classical
  dsimp
  let G := range (t+u+3)
  let A := layer F (t+1)
  let C := layer F (t+2)
  have aSize (a : Finset Nat) (ha : a∈A) : a.card=t+1 := (from_layer ha).2
  have cSize (a : Finset Nat) (ha : a∈C) : a.card=t+2 := (from_layer ha).2
  have aG (a : Finset Nat) (ha : a∈A) : a⊆G := V.1 a (from_layer ha).1
  have cG (a : Finset Nat) (ha : a∈C) : a⊆G := V.1 a (from_layer ha).1
  have aNear (a : Finset Nat) (ha : a∈A) (b : Finset Nat) (hb : b∈A) :
      t+1-1≤(a∩b).card := by
    have hz := (V.2 a (from_layer ha).1 b (from_layer hb).1).1
    omega
  have cNear (a : Finset Nat) (ha : a∈C) (b : Finset Nat) (hb : b∈C) :
      t+2-1≤(a∩b).card := by
    have H := V.2 a (from_layer ha).1 b (from_layer hb).1
    have h := card_union_add_card_inter a b
    have sa := cSize _ ha
    have sb := cSize _ hb
    omega
  have gc : G.card=t+u+3 := card_range _
  have bCap : (layer F t).card≤1 := card_le_one.mpr (fun a ha b hb =>
    Subset.antisymm (lower_from_bottom V ha (from_layer hb).1)
      (lower_from_bottom V hb (from_layer ha).1))
  have hCap : (layer F (t+3)).card≤1 := card_le_one.mpr (fun a ha b hb =>
    Subset.antisymm (upper_from_top V hb (from_layer ha).1)
      (upper_from_top V ha (from_layer hb).1))
  by_cases bottom : (layer F t).Nonempty
  · obtain ⟨T,tF⟩ := bottom
    have tc := (from_layer tF).2
    have TG : T⊆G := V.1 T (from_layer tF).1
    have base (a : Finset Nat) (ha : a∈F) : T⊆a := lower_from_bottom V tF ha
    by_cases top : (layer F (t+3)).Nonempty
    · obtain ⟨Q,qF⟩ := top
      have qc := (from_layer qF).2
      have TQ := base Q (from_layer qF).1
      have b1 := between_count (F:=A) TQ (fun v h => base v (from_layer h).1)
        (fun v h => upper_from_top V qF (from_layer h).1) aSize
      have b2 := between_count (F:=C) TQ (fun v h => base v (from_layer h).1)
        (fun v h => upper_from_top V qF (from_layer h).1) cSize
      rw [tc,qc,show (t+3)-t=3 by omega,show (t+1)-t=1 by omega] at b1
      rw [tc,qc,show (t+3)-t=3 by omega,show (t+2)-t=2 by omega] at b2
      exact Or.inl ⟨bCap,b1,b2,hCap⟩
    · have high0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp top)
      have b1 := star_count G T A (t+1) (by omega) aG
        (fun v h => base v (from_layer h).1) TG aSize
      let D := C.image (fun v => v \ T)
      have cInj : Set.InjOn (fun v : Finset Nat => v \ T) ↑C := by
        intro a ha b hb e
        have h := congrArg (fun v : Finset Nat => T∪v) e
        rwa [union_sdiff_of_subset (base _ (from_layer ha).1),
          union_sdiff_of_subset (base _ (from_layer hb).1)] at h
      have dc : D.card=C.card := card_image_of_injOn cInj
      have dG (g : Finset Nat) (hg : g∈D) : g⊆G\T := by
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hg
        intro z hz
        obtain ⟨h1,h2⟩ := mem_sdiff.mp hz
        exact mem_sdiff.mpr ⟨cG a ha h1,h2⟩
      have ds (g : Finset Nat) (hg : g∈D) : g.card=2 := by
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hg
        rw [card_sdiff_of_subset (base _ (from_layer ha).1),tc,cSize _ ha]
        omega
      have dn (g : Finset Nat) (hg : g∈D) (h : Finset Nat) (hh : h∈D) :
          2-1≤(g∩h).card := by
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hg
        obtain ⟨b,hb,rfl⟩ := mem_image.mp hh
        have e : (a\T)∩(b\T)=(a∩b)\T := by
          ext z
          simp only [mem_inter,mem_sdiff]
          tauto
        rw [e,card_sdiff_of_subset (subset_inter (base _ (from_layer ha).1)
          (base _ (from_layer hb).1)),tc]
        have N := cNear a ha b hb
        omega
      have b2 := johnson_count_in (G\T) D 2 (by decide) dG ds dn
      rw [dc,card_sdiff_of_subset TG,gc,tc,
        show t+u+3-t-(2-1)=u+2 by omega,max_eq_left (by omega : 3≤u+2)] at b2
      rw [gc,tc] at b1
      exact Or.inr (Or.inl ⟨bCap,(show A.card≤u+3 by omega),b2,high0⟩)
  · have low0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp bottom)
    by_cases top : (layer F (t+3)).Nonempty
    · obtain ⟨Q,qF⟩ := top
      have qc := (from_layer qF).2
      have b1 := johnson_count_in Q A (t+1) (by omega)
        (fun v h => upper_from_top V qF (from_layer h).1) aSize aNear
      rw [qc,show (t+3)-(t+1-1)=3 by omega,max_eq_right (by omega : 3≤t+2)] at b1
      have b2 := top_count Q C (t+2) (by omega)
        (fun v h => upper_from_top V qF (from_layer h).1) cSize
      exact Or.inr (Or.inr ⟨low0,b1,b2,hCap⟩)
    · have high0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp top)
      have b1 := johnson_count_in G A (t+1) (by omega) aG aSize aNear
      have b2 := johnson_count_in G C (t+2) (by omega) cG cSize cNear
      rw [gc,show t+u+3-(t+1-1)=u+3 by omega] at b1
      rw [gc,show t+u+3-(t+2-1)=u+2 by omega] at b2
      rw [max_eq_left (by omega : t+2≤u+3)] at b1
      by_cases strict : t<u
      · rw [max_eq_left (by omega : t+3≤u+2)] at b2
        exact Or.inr (Or.inl ⟨bCap,b1,b2,high0⟩)
      · have et : u=t := by omega
        rw [et,max_eq_right (by omega : t+2≤t+3)] at b2
        by_cases ca : A.card≤t+2
        · exact Or.inr (Or.inr ⟨low0,ca,b2,hCap⟩)
        · by_cases cc : C.card≤u+2
          · exact Or.inr (Or.inl ⟨bCap,b1,cc,high0⟩)
          · exfalso
            have Astar : ∃ X : Finset Nat, X.card=t ∧ ∀ g∈A, X⊆g := by
              rcases johnson_star_or_top A (t+1) (by omega) (by omega) aSize aNear with h|⟨P,pC,tP⟩
              · simpa using h
              · exact False.elim (ca (top_count P A (t+1) pC tP aSize))
            have Ctop : ∃ P : Finset Nat, P.card=t+3 ∧ ∀ g∈C, g⊆P := by
              rcases johnson_star_or_top C (t+2) (by omega) (by omega) cSize cNear with ⟨X,xC,xS⟩|h
              · obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<C.card)
                have gX := (xS a ha).trans (cG a ha)
                have Cn := star_count G X C (t+2) (by omega) cG xS gX cSize
                exact False.elim (cc (by omega))
              · exact h
            obtain ⟨X,xC,xS⟩ := Astar
            obtain ⟨P,pC,pS⟩ := Ctop
            obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<A.card)
            exact balanced_middle_conflict G X P A C t ht (by omega) xC pC
              ((xS a ha).trans (aG a ha)) aG cG xS pS aSize cSize (by omega) (by omega)
              (fun a ha b hb => (V.2 a (from_layer ha).1 b (from_layer hb).1).1)

#print axioms slack_three_count_cases
end IU.Lubell
