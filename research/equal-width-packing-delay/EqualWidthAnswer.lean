import PeerRigid

namespace CoverCutoff

lemma peer_restrict_inj {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (p q : Equiv.Perm (Fin (BigN h j)))
    (pP : Packs (equalWidthPeer h (by omega)) 3 j p)
    (qP : Packs (equalWidthPeer h (by omega)) 3 j q)
    (eq : peerRestrict h j hh hj p = peerRestrict h j hh hj q) :
    p=q := by
  apply same_comparisons
  intro x y
  obtain ⟨a,rfl⟩ := peerLabel_surj hh hj x
  obtain ⟨b,rfl⟩ := peerLabel_surj hh hj y
  rw [peer_cmp_rigid hh hj p ((peer_packs_iff hh hj p).mp pP),
      peer_cmp_rigid hh hj q ((peer_packs_iff hh hj q).mp qP),eq]

noncomputable def peerRestrictSub {h j : ℕ} (hh : 2≤h) (hj : 1≤j)
    (x : {p : Equiv.Perm (Fin (BigN h j)) // Packs (equalWidthPeer h (by omega)) 3 j p}) :
    {p : Equiv.Perm (Fin (SmallN j)) // Packs patternA 2 j p} :=
  ⟨peerRestrict h j hh hj x.val,peer_restrict_packs hh hj x.val x.property⟩

lemma peer_restrict_sub_bijective {h j : ℕ} (hh : 2≤h) (hj : 1≤j) :
    Function.Bijective (peerRestrictSub hh hj) := by
  constructor
  · intro x y eq
    apply Subtype.ext
    exact peer_restrict_inj hh hj x.val y.val x.property y.property (congrArg Subtype.val eq)
  · intro y
    refine ⟨⟨peerLift y.val,peer_lift_valid hh hj y.val y.property⟩,?_⟩
    apply Subtype.ext
    exact peer_retract hh hj y.val

theorem peer_count {h j : ℕ} (hh : 2≤h) (hj : 1≤j) :
    packCount (equalWidthPeer h (by omega)) 3 j = packCount patternA 2 j :=
  Nat.card_congr (Equiv.ofBijective _ (peer_restrict_sub_bijective hh hj))

/-- Agreement through h, followed by strict disagreement, even with both
the pattern length 3h+1 and the overlap 3h−2 required to be equal. -/
theorem equal_length_delay {h : ℕ} (hh : 2≤h) :
    ∃ p q : Equiv.Perm (Fin (3*h+1)), Admissible p 3 ∧ Admissible q 3 ∧
      (∀ j, 1≤j → j≤h → packCount p 3 j = packCount q 3 j) ∧
      packCount p 3 (h+1) < packCount q 3 (h+1) := by
  refine ⟨equalWidthPeer h (by omega),delayed h hh,peer_admissible hh,delayed_admissible hh,?_ ,?_⟩
  · intro j hj hlim
    exact (peer_count hh hj).trans (same_counts_below hh hj hlim)
  · rw [peer_count hh (by omega)]
    exact delayed_strict hh

/-- Any equality-testing cutoff restricted to this length and overlap
must inspect at least h+1 occurrences. -/
theorem width_cutoff_lower {h bound : ℕ} (hh : 2≤h)
    (H : ∀ p q : Equiv.Perm (Fin (3*h+1)), Admissible p 3 → Admissible q 3 →
       (∀ j, 1≤j → j≤bound → packCount p 3 j = packCount q 3 j) →
       ∀ j, 1≤j → packCount p 3 j = packCount q 3 j) :
    h+1≤bound := by
  by_contra! e
  obtain ⟨p,q,hp,hq,agree,differ⟩ := equal_length_delay hh
  have eq := H p q hp hq
    (fun j pos small => agree j pos (by omega)) (h+1) (by omega)
  omega

#print axioms equal_length_delay
#print axioms width_cutoff_lower
end CoverCutoff
