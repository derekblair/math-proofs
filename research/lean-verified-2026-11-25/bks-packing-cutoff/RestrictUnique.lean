import FixedOrder
namespace CoverCutoff

lemma reverse_comparison (x y z w : ℕ) (h : x<y ↔ z<w)
    (hx : x≠y) (hz : z≠w) : y<x ↔ w<z := by omega

theorem restrict_inj_below {h j : ℕ} (hh:2≤h) (hj:1≤j) (hJ:j≤h)
    (p q : Equiv.Perm (Fin (BigN h j)))
    (hp : Packs (delayed h hh) 3 j p) (hq : Packs (delayed h hh) 3 j q)
    (H : restrictSmall h j hh hj p = restrictSmall h j hh hj q) : p=q := by
  set f := readRank p
  set g := readRank q
  have P : GlobalRows f h j := (packs_iff_global hh hj p).mp hp
  have Q : GlobalRows g h j := (packs_iff_global hh hj q).mp hq
  have NB := bigSize (h:=h) hj
  have NS := smallSize hj
  have hin (a b : ℕ) (ha:a<BigN h j) (hb:b<BigN h j) (hne:a≠b) :
      f a≠f b ∧ g a≠g b :=
    ⟨fun e=>hne (readRank_inj p ha hb e),fun e=>hne (readRank_inj q ha hb e)⟩
  have ac (i c : ℕ) (hi:i<h+j) (hc:c<h+j-1) :
      localA f i < localC f c ↔ localA g i < localC g c := by
    by_cases h1 : i<h-1
    · exact iff_of_true (earlyA_C hh hj P (by omega) hc) (earlyA_C hh hj Q (by omega) hc)
    by_cases h2 : j<c
    · exact iff_of_true (allA_tailC hh hj P hi hc h2) (allA_tailC hh hj Q hi hc h2)
    have ha : uPos (i-(h-1))<SmallN j := by unfold uPos; omega
    have hb : vPos c<SmallN j := by unfold vPos; omega
    have hp' := restrict_comparison hh hj p ha hb
    have hq' := restrict_comparison hh hj q ha hb
    rw [H] at hp'
    rw [kept_U,kept_V,show h-1+(i-(h-1))=i by omega] at hp' hq'
    exact hp'.symm.trans hq'
  have ca (c i : ℕ) (hc:c<h+j-1) (hi:i<h+j) :
      localC f c < localA f i ↔ localC g c < localA g i := by
    have hne := hin (posA i) (posC c) (by unfold posA; omega)
      (by unfold posC; omega) (by unfold posA posC; omega)
    exact reverse_comparison _ _ _ _ (ac i c hi hc) hne.1 hne.2
  apply same_comparisons
  intro x y
  let a := x.val
  let b := y.val
  have ha : a<BigN h j := x.isLt
  have hb : b<BigN h j := y.isLt
  have conv : (f a<f b ↔ g a<g b) → (p x<p y ↔ q x<q y) := by
    intro hc
    change (p x).val < (p y).val ↔ (q x).val < (q y).val
    simpa only [f,g,a,b,readRank_fin] using hc
  apply conv
  have a0 : a%3=0 ∨ a%3=1 ∨ a%3=2 := by omega
  have b0 : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
  rcases a0 with a0|a0|a0 <;> rcases b0 with b0|b0|b0
  · rw [show a=posA (a/3) by unfold posA; omega,show b=posA (b/3) by unfold posA; omega]
    exact (asc_iff P.1 (by omega) (by omega)).trans (asc_iff Q.1 (by omega) (by omega)).symm
  · rw [show a=posA (a/3) by unfold posA; omega,show b=posB (b/3) by unfold posB; omega]
    exact (ab_pos hh hj P (by omega) (by omega)).trans (ab_pos hh hj Q (by omega) (by omega)).symm
  · rw [show a=posA (a/3) by unfold posA; omega,show b=posC (b/3) by unfold posC; omega]
    exact ac _ _ (by omega) (by omega)
  · rw [show a=posB (a/3) by unfold posB; omega,show b=posA (b/3) by unfold posA; omega]
    exact (ab_neg hh hj P (by omega) (by omega)).trans (ab_neg hh hj Q (by omega) (by omega)).symm
  · rw [show a=posB (a/3) by unfold posB; omega,show b=posB (b/3) by unfold posB; omega]
    exact (asc_iff P.2.1 (by omega) (by omega)).trans (asc_iff Q.2.1 (by omega) (by omega)).symm
  · rw [show a=posB (a/3) by unfold posB; omega,show b=posC (b/3) by unfold posC; omega]
    exact iff_of_true (allB_C hh hj hJ P (by omega) (by omega))
      (allB_C hh hj hJ Q (by omega) (by omega))
  · rw [show a=posC (a/3) by unfold posC; omega,show b=posA (b/3) by unfold posA; omega]
    exact ca _ _ (by omega) (by omega)
  · rw [show a=posC (a/3) by unfold posC; omega,show b=posB (b/3) by unfold posB; omega]
    exact iff_of_false (not_lt_of_ge (allB_C hh hj hJ P (by omega) (by omega)).le)
      (not_lt_of_ge (allB_C hh hj hJ Q (by omega) (by omega)).le)
  · rw [show a=posC (a/3) by unfold posC; omega,show b=posC (b/3) by unfold posC; omega]
    exact (asc_iff P.2.2.1 (by omega) (by omega)).trans (asc_iff Q.2.2.1 (by omega) (by omega)).symm

theorem same_counts_below {h j : ℕ} (hh:2≤h) (hj:1≤j) (hJ:j≤h) :
    packCount patternA 2 j = packCount (delayed h hh) 3 j := by
  classical
  let f : {p : Equiv.Perm (Fin (BigN h j)) // Packs (delayed h hh) 3 j p} →
      {p : Equiv.Perm (Fin (SmallN j)) // Packs patternA 2 j p} :=
    fun p => ⟨restrictSmall h j hh hj p.val,restrict_packs hh hj p.val p.prop⟩
  have hF : Function.Bijective f := by
    constructor
    · intro p q he
      apply Subtype.ext
      exact restrict_inj_below hh hj hJ p.val q.val p.prop q.prop (congrArg Subtype.val he)
    · intro p
      exact ⟨⟨liftRanks p.val false,lift_packs hh hj p.val p.prop false⟩,
        Subtype.ext (restrict_lift hh hj p.val false)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hF)).symm

#print axioms same_counts_below
end CoverCutoff
