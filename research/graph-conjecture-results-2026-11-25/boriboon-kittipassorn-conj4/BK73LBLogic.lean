import BK73Main1
import BK73LBCore

open SimpleGraph

namespace BK73

/-- the graph FCZnw: 13 edges 03 05 06 14 15 16 24 25 26 36 45 46 56 -/
def G0 : SimpleGraph (Fin 7) where
  Adj i j := ab m0 i j = true
  symm := ⟨fun i j h => by
    have key : ∀ i j : Fin 7, ab m0 i j = true → ab m0 j i = true := by decide
    exact key i j h⟩
  loopless := ⟨fun i h => by simp [ab] at h⟩

instance : DecidableRel G0.Adj := fun i j => inferInstanceAs (Decidable (ab m0 i j = true))

theorem G0_ncard : G0.edgeSet.ncard = 13 := by
  have h1 := handshake_code G0
  have h2 : (codeList G0).count true = 13 := by decide
  rw [sum_degrees_eq_twice_card_edges, h2] at h1
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  omega

/-! ### BFS connectivity certificate -/

theorem bfs_sound (H : SimpleGraph (Fin 7)) (A : Fin 7 → Fin 7 → Bool)
    (hA : ∀ x y, A x y = true → H.Adj x y) (h : (List.finRange 7).all (bfs A) = true) :
    H.Connected := by
  have inv : ∀ n x, bfsN A n x = true → H.Reachable 0 x := by
    intro n
    induction n with
    | zero =>
      intro x hx
      have : x = 0 := by simpa [bfsN] using hx
      subst this; rfl
    | succ n ih =>
      intro x hx
      simp only [bfsN, bfsStep, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at hx
      rcases hx with hx | ⟨y, -, hy, hxy⟩
      · exact ih x hx
      · exact (ih y hy).trans (hA y x hxy).reachable
  have hr : ∀ x, H.Reachable 0 x := fun x =>
    inv 6 x (by rw [List.all_eq_true] at h; exact h x (List.mem_finRange x))
  exact ⟨fun x y => (hr x).symm.trans (hr y)⟩

theorem bfs_cert : ∀ a b : Fin 7, (List.finRange 7).all (bfs (adjDel a b)) = true := by
  decide +kernel

theorem adjDel_sound (a b x y : Fin 7) (h : adjDel a b x y = true) :
    (G0.deleteEdges {s(a, b)}).Adj x y := by
  rw [deleteEdges_adj]
  simp only [adjDel, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  refine ⟨h.1, ?_⟩
  rw [Set.mem_singleton_iff, Sym2.eq_iff]
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · rcases h.2.1 with h' | h' <;> exact h' rfl
  · rcases h.2.2 with h' | h' <;> exact h' rfl

theorem G0_bridgeless : Bridgeless G0 := by
  refine ⟨?_, fun e => ?_⟩
  · exact bfs_sound G0 (adjDel 0 0) (fun x y h => by
      have := adjDel_sound 0 0 x y h; rw [deleteEdges_adj] at this; exact this.1) (bfs_cert 0 0)
  · refine Sym2.ind (fun a b => ?_) e
    rw [isBridge_iff, not_not]
    exact (bfs_sound _ (adjDel a b) (adjDel_sound a b) (bfs_cert a b)).preconnected a b

/-! ### No orientation of diameter ≤ 3 -/

theorem expand_sel {α : Type*} (ps : List α) (f g : α → Bool)
    (h : ∀ p ∈ ps, f p = false → g p = false) :
    expand (ps.map f) (sel (ps.map f) (ps.map g)) = ps.map g := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    cases hf : f p
    · have hg := h p List.mem_cons_self hf
      simp only [List.map_cons, hf, hg, sel, expand, ih']
    · simp only [List.map_cons, hf, sel, expand, List.headD_cons, List.tail_cons, ih']

theorem sel_length {α : Type*} (ps : List α) (f g : α → Bool) :
    (sel (ps.map f) (ps.map g)).length = (ps.map f).count true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases hf : f p <;> simp [sel, hf, ih]

def iterS (os : List ℕ) : ℕ → ℕ → ℕ
  | 0, S => S
  | k+1, S => step os (iterS os k S)

theorem step_mono (os : List ℕ) (S v : ℕ) (h : S.testBit v = true) :
    (step os S).testBit v = true := by
  rw [step, Nat.testBit_or, h, Bool.true_or]

theorem iterS_mono (os : List ℕ) (S v k : ℕ) (h : (iterS os k S).testBit v = true) :
    ∀ d, (iterS os (k + d) S).testBit v = true := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih => exact step_mono os _ v ih

theorem bigOr_complete (S v w : ℕ) (g : ℕ → ℕ) (ws : List ℕ) (hw : w ∈ ws)
    (hS : S.testBit w = true) (hg : (g w).testBit v = true) :
    (ws.foldr (fun w acc => if S.testBit w then acc ||| g w else acc) 0).testBit v = true := by
  induction ws with
  | nil => simp at hw
  | cons a ws ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hw with rfl | hw
    · rw [if_pos hS, Nat.testBit_or, hg, Bool.or_true]
    · split_ifs
      · rw [Nat.testBit_or, ih hw, Bool.true_or]
      · exact ih hw

theorem getD_map_lt {α : Type*} (l : List α) (f : α → Bool) (k : ℕ) (hk : k < l.length)
    (d : α) : (l.map f).getD k false = f (l.getD k d) := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem EPn_pidx : ∀ i j : Fin 7, i < j →
    pidx i j < EPn.length ∧ EPn.getD (pidx i j) (0, 0) = ((i : ℕ), (j : ℕ)) := by
  decide

theorem EPn_lt : ∀ p ∈ EPn, p.1 < 7 ∧ p.2 < 7 := by decide

theorem G0_noOrient_of (htop : allL lbp 13 13 [] = true) : ¬ HasOrientDiamLE G0 3 := by
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
    have hne : u ≠ v := fun h => G0.loopless.irrefl u (h ▸ O.arc_adj u v huv)
    unfold dir
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos (show (u:ℕ) < v from h), hf u v h]; simpa using huv
    · rw [if_neg (show ¬ (u:ℕ) < v by omega), hf v u h]
      simpa using O.anti u v huv
  let os := (List.range 7).map (orow m0 t)
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
  have hall : ∀ u v : Fin 7, (reach3 os u).testBit v = true := by
    intro u v
    obtain ⟨k, hk, hr⟩ := hO u v
    have := iterS_mono os _ v k (key3 k u v hr) (3 - k)
    rw [show k + (3 - k) = 3 by omega] at this
    exact this
  have hbad : bad3 m0 t = false := by
    rw [bad3, List.any_eq_false]
    intro u hu
    simp only [List.any_eq_true, not_exists, not_and]
    intro v hv
    have := hall ⟨u, List.mem_range.mp hu⟩ ⟨v, List.mem_range.mp hv⟩
    simpa using this
  have hsound := allL_sound lbp 13 13 [] htop (sel mask0 L).reverse
    (by rw [List.length_reverse, mask0, sel_length]; decide)
    (by rw [List.count_reverse]; exact (List.count_le_length).trans
          (by rw [mask0, sel_length]; decide))
  rw [List.reverse_reverse, List.append_nil, lbp] at hsound
  have hexp : expand mask0 (sel mask0 L) = L := by
    refine expand_sel EPn _ f (fun p hp hab => ?_)
    obtain ⟨h1, h2⟩ := EPn_lt p hp
    simp only [f, dif_pos (And.intro h1 h2), decide_eq_false_iff_not]
    intro harc
    have := O.arc_adj _ _ harc
    change ab m0 p.1 p.2 = true at this
    rw [hab] at this; exact Bool.false_ne_true this
  rw [hexp] at hsound
  rw [hsound] at hbad
  simp at hbad

end BK73
