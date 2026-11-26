import BK73LBLogic
import BK73LB4Core

open SimpleGraph

namespace BK73

/-- the graph F?qvo: 10 edges 04 05 06 14 16 25 26 35 36 46 -/
def G1 : SimpleGraph (Fin 7) where
  Adj i j := ab m1 i j = true
  symm := ⟨fun i j h => by
    have key : ∀ i j : Fin 7, ab m1 i j = true → ab m1 j i = true := by decide
    exact key i j h⟩
  loopless := ⟨fun i h => by simp [ab] at h⟩

instance : DecidableRel G1.Adj := fun i j => inferInstanceAs (Decidable (ab m1 i j = true))

theorem G1_ncard : G1.edgeSet.ncard = 10 := by
  have h1 := handshake_code G1
  have h2 : (codeList G1).count true = 10 := by decide
  rw [sum_degrees_eq_twice_card_edges, h2] at h1
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  omega

theorem bfs_cert1 : ∀ a b : Fin 7, (List.finRange 7).all (bfs (adjDel1 a b)) = true := by
  decide +kernel

theorem adjDel1_sound (a b x y : Fin 7) (h : adjDel1 a b x y = true) :
    (G1.deleteEdges {s(a, b)}).Adj x y := by
  rw [deleteEdges_adj]
  simp only [adjDel1, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  refine ⟨h.1, ?_⟩
  rw [Set.mem_singleton_iff, Sym2.eq_iff]
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · rcases h.2.1 with h' | h' <;> exact h' rfl
  · rcases h.2.2 with h' | h' <;> exact h' rfl

theorem G1_bridgeless : Bridgeless G1 := by
  refine ⟨?_, fun e => ?_⟩
  · exact bfs_sound G1 (adjDel1 0 0) (fun x y h => by
      have := adjDel1_sound 0 0 x y h; rw [deleteEdges_adj] at this; exact this.1) (bfs_cert1 0 0)
  · refine Sym2.ind (fun a b => ?_) e
    rw [isBridge_iff, not_not]
    exact (bfs_sound _ (adjDel1 a b) (adjDel1_sound a b) (bfs_cert1 a b)).preconnected a b

theorem G1_noOrient_of (htop : allL lbp4 10 10 [] = true) : ¬ HasOrientDiamLE G1 4 := by
  classical
  rintro ⟨O, hO⟩
  let f : ℕ × ℕ → Bool := fun p =>
    if h : p.1 < 7 ∧ p.2 < 7 then decide (O.arc ⟨p.1, h.1⟩ ⟨p.2, h.2⟩) else false
  let L := EPn.map f
  let t := ofBits L
  have hf : ∀ i j : Fin 7, i < j → t.testBit (pidx i j) = decide (O.arc i j) := by
    intro i j hij
    obtain ⟨hl, he⟩ := EPn_pidx i j hij
    rw [testBit_ofBits, getD_map_lt EPn f _ hl (0, 0), he]
    simp [f]
  have key1 : ∀ u v : Fin 7, O.arc u v → dir t u v = true := by
    intro u v huv
    have hne : u ≠ v := fun h => G1.loopless.irrefl u (h ▸ O.arc_adj u v huv)
    unfold dir
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos (show (u:ℕ) < v from h), hf u v h]; simpa using huv
    · rw [if_neg (show ¬ (u:ℕ) < v by omega), hf v u h]
      simpa using O.anti u v huv
  let os := (List.range 7).map (orow m1 t)
  have key2 : ∀ w v : Fin 7, O.arc w v → (os.getD w 0).testBit v = true := by
    intro w v hwv
    rw [getD_map_range, if_pos w.isLt, orow, testBit_ofBits, getD_map_range, if_pos v.isLt,
      Bool.and_eq_true]
    exact ⟨O.arc_adj w v hwv, key1 w v hwv⟩
  have key3 : ∀ k (u v : Fin 7), DReach O.arc k u v → (iterS os k (2 ^ (u:ℕ))).testBit v = true := by
    intro k u v h
    induction h with
    | refl u => simp [iterS, Nat.testBit_two_pow_self]
    | @tail k a b c _ hbc ih =>
      show (step os (iterS os k (2 ^ (a:ℕ)))).testBit c = true
      rw [step, Nat.testBit_or, Bool.or_eq_true]
      exact Or.inr (bigOr_complete _ _ b _ _ (List.mem_range.mpr b.isLt) ih (key2 b c hbc))
  have hall : ∀ u v : Fin 7, (reach4 os u).testBit v = true := by
    intro u v
    obtain ⟨k, hk, hr⟩ := hO u v
    have := iterS_mono os _ v k (key3 k u v hr) (4 - k)
    rw [show k + (4 - k) = 4 by omega] at this
    exact this
  have hbad : bad4 m1 t = false := by
    rw [bad4, List.any_eq_false]
    intro u hu
    simp only [List.any_eq_true, not_exists, not_and]
    intro v hv
    have := hall ⟨u, List.mem_range.mp hu⟩ ⟨v, List.mem_range.mp hv⟩
    simpa using this
  have hsound := allL_sound lbp4 10 10 [] htop (sel mask1 L).reverse
    (by rw [List.length_reverse, mask1, sel_length]; decide)
    (by rw [List.count_reverse]; exact (List.count_le_length).trans
          (by rw [mask1, sel_length]; decide))
  rw [List.reverse_reverse, List.append_nil, lbp4] at hsound
  have hexp : expand mask1 (sel mask1 L) = L := by
    refine expand_sel EPn _ f (fun p hp hab => ?_)
    obtain ⟨h1, h2⟩ := EPn_lt p hp
    simp only [f, dif_pos (And.intro h1 h2), decide_eq_false_iff_not]
    intro harc
    have := O.arc_adj _ _ harc
    change ab m1 p.1 p.2 = true at this
    rw [hab] at this; exact Bool.false_ne_true this
  rw [hexp] at hsound
  rw [hsound] at hbad
  simp at hbad

end BK73
