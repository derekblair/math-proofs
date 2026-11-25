import LiftRetract
namespace CoverCutoff

def witnessKey (j v : ℕ) : ℕ :=
  if v%2=0 then (if v/2<2 then v/2 else v/2+1)
  else if v/2=0 then 2 else j+2+v/2

def witnessLex (j : ℕ) (v : Fin (SmallN j)) : ℕ ×ₗ ℕ :=
  toLex (witnessKey j v.val,v.val)

noncomputable def witnessSmall (j : ℕ) : Equiv.Perm (Fin (SmallN j)) :=
  rankKey (witnessLex j) (fun _ _ h => Fin.ext (congrArg (fun x => (ofLex x).2) h))

lemma witness_lt {j a b : ℕ} (ha:a<SmallN j) (hb:b<SmallN j)
    (hh:witnessKey j a<witnessKey j b) :
    readRank (witnessSmall j) a < readRank (witnessSmall j) b := by
  rw [show readRank (witnessSmall j) a=((witnessSmall j) ⟨a,ha⟩).val from readRank_fin _ ⟨a,ha⟩,
      show readRank (witnessSmall j) b=((witnessSmall j) ⟨b,hb⟩).val from readRank_fin _ ⟨b,hb⟩]
  exact (rankKey_iff _ _ _ _).mpr (Prod.Lex.lt_iff.mpr (Or.inl hh))

lemma witness_U (j i : ℕ) : witnessKey j (uPos i)= if i<2 then i else i+1 := by
  unfold uPos witnessKey
  simp [show (2*i)%2=0 by omega,show (2*i)/2=i by omega]

lemma witness_V (j i : ℕ) : witnessKey j (vPos i)= if i=0 then 2 else j+2+i := by
  unfold vPos witnessKey
  simp [show (2*i+1)%2=1 by omega,show (2*i+1)/2=i by omega]

lemma witnessRow {j : ℕ} (hj:2≤j) : CatalanRows (readRank (witnessSmall j)) j := by
  have hn := smallSize (j:=j) (by omega)
  have hU (i : ℕ) (hi:i≤j) : uPos i<SmallN j := by unfold uPos; omega
  have hV (i : ℕ) (hi:i≤j) : vPos i<SmallN j := by unfold vPos; omega
  refine ⟨?_,?_,?_⟩
  · intro i _ hi
    exact witness_lt (hU _ (by omega)) (hU _ (by omega)) (by simp only [witness_U]; split_ifs <;> omega)
  · intro i _ hi
    exact witness_lt (hV i (by omega)) (hV (i+1) (by omega)) (by
      rw [witness_V j i,witness_V j (i+1)]
      rw [if_neg (show i+1≠0 by omega)]
      split_ifs <;> omega)
  · intro t ht
    exact witness_lt (hU _ (by omega)) (hV _ (by omega)) (by rw [witness_U,witness_V]; split_ifs <;> omega)

lemma witness_gap {j : ℕ} (hj:2≤j) :
    smallU (readRank (witnessSmall j)) 1 < smallV (readRank (witnessSmall j)) 0 ∧
    smallV (readRank (witnessSmall j)) 0 < smallU (readRank (witnessSmall j)) 2 := by
  have hn := smallSize (j:=j) (by omega)
  refine ⟨witness_lt (by unfold uPos; omega) (by unfold vPos; omega) (by simp [witness_U,witness_V]),
         witness_lt (by unfold vPos; omega) (by unfold uPos; omega) (by simp [witness_V,witness_U])⟩

lemma two_lifts_ne {h : ℕ} (hh:2≤h) :
    liftRanks (h:=h) (witnessSmall (h+1)) false ≠ liftRanks (h:=h) (witnessSmall (h+1)) true := by
  let p := witnessSmall (h+1)
  let b := posB (2*h-1)
  let c := posC 0
  have hn := bigSize (h:=h) (j:=h+1) (by omega)
  have hb : b<BigN h (h+1) := by unfold b posB; omega
  have hc : c<BigN h (h+1) := by unfold c posC; omega
  have bk (z : Bool) : bigKey (h:=h) p z b =
      if z then mainU h p 1+1 else mainU h p 2-1 := by
    unfold b
    rw [bigKey_B]
    unfold keyB betweenKey
    have e : 2*h-1-(h-1)=h := by omega
    rw [if_neg (by omega),e,if_neg (by omega),show h+1-(h-1)=2 by omega]
    cases z <;> simp
  have ck (z : Bool) : bigKey (h:=h) p z c = mainV h p 0 := by
    unfold c
    rw [bigKey_C]
    simp [keyC]
  have hg := witness_gap (j:=h+1) (by omega)
  have lo : mainU h p 1+1<mainV h p 0 := by
    dsimp [mainU, mainV, p]
    omega
  have hi : mainV h p 0<mainU h p 2-1 := by
    dsimp [mainU, mainV, p]
    omega
  have q := lift_less p false hc hb (by rw [bk,ck]; exact hi)
  have r := lift_less p true hb hc (by rw [bk,ck]; exact lo)
  intro he
  change liftRanks (h:=h) p false = liftRanks (h:=h) p true at he
  rw [he] at q
  exact (not_lt_of_ge q.le) r

theorem delayed_strict {h : ℕ} (hh:2≤h) :
    packCount patternA 2 (h+1) < packCount (delayed h hh) 3 (h+1) := by
  classical
  let j := h+1
  have hj:1≤j := by omega
  let S := {p : Equiv.Perm (Fin (SmallN j)) // Packs patternA 2 j p}
  let T := {p : Equiv.Perm (Fin (BigN h j)) // Packs (delayed h hh) 3 j p}
  let e : S → T := fun p => ⟨liftRanks p.val false,lift_packs hh hj p.val p.prop false⟩
  have he : Function.Injective e := by
    intro p q hp
    have hc := congrArg (fun r : T => restrictSmall h j hh hj r.val) hp
    apply Subtype.ext
    exact (restrict_lift hh hj p.val false).symm.trans (hc.trans (restrict_lift hh hj q.val false))
  let w : S := ⟨witnessSmall j,(small_packs_iff _).mpr (witnessRow (by omega))⟩
  let w' : T := ⟨liftRanks w.val true,lift_packs hh hj w.val w.prop true⟩
  have hn : ¬ Function.Surjective e := by
    intro hs
    obtain ⟨p,hp⟩ := hs w'
    have hc := congrArg (fun r : T => restrictSmall h j hh hj r.val) hp
    have hW : p=w := Subtype.ext
      ((restrict_lift hh hj p.val false).symm.trans (hc.trans (restrict_lift hh hj w.val true)))
    subst p
    exact two_lifts_ne hh (congrArg Subtype.val hp)
  rw [packCount,packCount,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective e he hn

#print axioms delayed_strict
end CoverCutoff
