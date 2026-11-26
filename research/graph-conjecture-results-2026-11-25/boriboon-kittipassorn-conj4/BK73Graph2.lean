import BK73Graph1

open SimpleGraph Finset

namespace BK73

/-! ## Faithful definitions (Boriboon–Kittipassorn, arXiv:2508.17569) -/

/-- bridgeless = connected and no bridge (their definition) -/
def Bridgeless {V : Type*} (G : SimpleGraph V) : Prop := G.Connected ∧ ∀ e, ¬ G.IsBridge e

/-- an orientation: each edge gets exactly one direction, no arcs off the edges -/
structure Orient {V : Type*} (G : SimpleGraph V) where
  arc : V → V → Prop
  arc_adj : ∀ u v, arc u v → G.Adj u v
  total : ∀ u v, G.Adj u v → arc u v ∨ arc v u
  anti : ∀ u v, arc u v → ¬ arc v u

/-- directed walks of length `k` -/
inductive DReach {V : Type*} (r : V → V → Prop) : ℕ → V → V → Prop
  | refl (u : V) : DReach r 0 u u
  | tail {k : ℕ} {u v w : V} : DReach r k u v → r v w → DReach r (k+1) u w

/-- `G` has an orientation of diameter at most `d` -/
def HasOrientDiamLE {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ O : Orient G, ∀ u v, ∃ k ≤ d, DReach O.arc k u v

/-- m(n,d): least `M` such that every bridgeless graph of order `n` and size ≥ `M`
has an orientation of diameter ≤ `d` -/
noncomputable def mnd (n d : ℕ) : ℕ :=
  sInf {M : ℕ | ∀ G : SimpleGraph (Fin n), Bridgeless G → M ≤ G.edgeSet.ncard →
    HasOrientDiamLE G d}

/-! ## A vertex of degree ≤ 1 rules out bridgelessness -/

theorem not_bridgeless_of_degree_le_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v w : V) (hvw : v ≠ w) (h : G.degree v ≤ 1) : ¬ Bridgeless G := by
  rintro ⟨hc, hb⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · obtain ⟨p⟩ := hc.preconnected v w
    cases p with
    | nil => exact hvw rfl
    | cons ha _ =>
      have : 0 < G.degree v := by
        rw [← card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨_, (mem_neighborFinset _ _ _).mpr ha⟩
      omega
  · rw [← card_neighborFinset_eq_degree, Finset.card_eq_one] at h1
    obtain ⟨u, hu⟩ := h1
    have hvu : G.Adj v u := by
      rw [← mem_neighborFinset, hu]; exact Finset.mem_singleton_self u
    apply hb s(v, u)
    rw [isBridge_iff]
    intro hr
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact G.irrefl hvu
    | @cons _ x _ ha _ =>
      rw [deleteEdges_adj] at ha
      obtain ⟨hax, hnot⟩ := ha
      have hx : x = u := by
        have : x ∈ G.neighborFinset v := (mem_neighborFinset _ _ _).mpr hax
        rw [hu] at this; simpa using this
      subst hx
      exact hnot (Set.mem_singleton _)

/-! ## Soundness of the reachability check -/

theorem getD_map_range (f : ℕ → α) (d : α) (j : ℕ) :
    ((List.range 7).map f).getD j d = if j < 7 then f j else d := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simpa using h)]; rfl

theorem bigOr_aux (S v : ℕ) (g : ℕ → ℕ) (ws : List ℕ) :
    (ws.foldr (fun w acc => if S.testBit w then acc ||| g w else acc) 0).testBit v = true →
      ∃ w ∈ ws, S.testBit w = true ∧ (g w).testBit v = true := by
  induction ws with
  | nil => simp
  | cons a ws ih =>
    intro h
    simp only [List.foldr_cons] at h
    split_ifs at h with hS
    · rw [Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨w, hw, h1, h2⟩ := ih h; exact ⟨w, List.mem_cons_of_mem _ hw, h1, h2⟩
      · exact ⟨a, List.mem_cons_self, hS, h⟩
    · obtain ⟨w, hw, h1, h2⟩ := ih h; exact ⟨w, List.mem_cons_of_mem _ hw, h1, h2⟩

section reach
variable (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] (t : ℕ)

/-- the orientation of `G` encoded by `t` -/
def arcT (u v : Fin 7) : Prop := G.Adj u v ∧ dir t u v = true

theorem orow_sound (u : Fin 7) (j : ℕ) (h : (orow (ofBits (codeList G)) t u).testBit j = true) :
    ∃ hj : j < 7, arcT G t u ⟨j, hj⟩ := by
  rw [orow, testBit_ofBits, getD_map_range] at h
  split_ifs at h with hj
  · refine ⟨hj, ?_⟩
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have := ab_code G u ⟨j, hj⟩
    simp only at this
    rw [this] at h1
    exact ⟨of_decide_eq_true h1, h2⟩

def Inv (u : Fin 7) (k S : ℕ) : Prop :=
  ∀ v, S.testBit v = true → ∃ hv : v < 7, ∃ j ≤ k, DReach (arcT G t) j u ⟨v, hv⟩

theorem inv_zero (u : Fin 7) : Inv G t u 0 (2 ^ (u : ℕ)) := by
  intro v hv
  rw [Nat.testBit_two_pow] at hv
  have : (u : ℕ) = v := of_decide_eq_true hv
  subst this
  exact ⟨u.isLt, 0, le_refl _, DReach.refl _⟩

theorem inv_step (u : Fin 7) (k S : ℕ) (h : Inv G t u k S) :
    Inv G t u (k+1) (step ((List.range 7).map (orow (ofBits (codeList G)) t)) S) := by
  intro v hv
  rw [step, Nat.testBit_or, Bool.or_eq_true] at hv
  rcases hv with hv | hv
  · obtain ⟨hv7, j, hj, hr⟩ := h v hv
    exact ⟨hv7, j, by omega, hr⟩
  · obtain ⟨w, hw, hS, hg⟩ := bigOr_aux S v _ _ hv
    have hw7 : w < 7 := List.mem_range.mp hw
    rw [getD_map_range, if_pos hw7] at hg
    obtain ⟨hv7, harc⟩ := orow_sound G t ⟨w, hw7⟩ v hg
    obtain ⟨_, j, hj, hr⟩ := h w hS
    exact ⟨hv7, j+1, by omega, DReach.tail hr harc⟩

theorem good_sound (hg : good (ofBits (codeList G)) t = true) (u v : Fin 7) :
    ∃ k ≤ 3, DReach (arcT G t) k u v := by
  rw [good, goodOs, List.all_eq_true] at hg
  have h := hg u (List.mem_range.mpr u.isLt)
  rw [beq_iff_eq, reach3] at h
  have hI := inv_step G t u 2 _ (inv_step G t u 1 _ (inv_step G t u 0 _ (inv_zero G t u)))
  have hb : (step ((List.range 7).map (orow (ofBits (codeList G)) t))
      (step ((List.range 7).map (orow (ofBits (codeList G)) t))
        (step ((List.range 7).map (orow (ofBits (codeList G)) t)) (2 ^ (u:ℕ))))).testBit v
      = true := by
    rw [h, show (127:ℕ) = 2^7 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simpa using v.isLt
  obtain ⟨_, j, hj, hr⟩ := hI v hb
  exact ⟨j, hj, hr⟩

def orientT : Orient G where
  arc := arcT G t
  arc_adj := fun _ _ h => h.1
  total := by
    intro u v huv
    have hne : (u : ℕ) ≠ v := fun h => G.ne_of_adj huv (Fin.ext h)
    unfold arcT dir
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rw [if_pos h, if_neg (by omega)]
      cases t.testBit (pidx u v) <;> simp [huv, huv.symm]
    · rw [if_neg (by omega), if_pos h]
      cases t.testBit (pidx v u) <;> simp [huv, huv.symm]
  anti := by
    intro u v ⟨huv, h1⟩ ⟨_, h2⟩
    have hne : (u : ℕ) ≠ v := fun h => G.ne_of_adj huv (Fin.ext h)
    unfold dir at h1 h2
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rw [if_pos h] at h1; rw [if_neg (by omega)] at h2; simp [h1] at h2
    · rw [if_neg (by omega)] at h1; rw [if_pos h] at h2; simp [h2] at h1

theorem good_hasOrient (hg : good (ofBits (codeList G)) t = true) : HasOrientDiamLE G 3 :=
  ⟨orientT G t, good_sound G t hg⟩

end reach

end BK73
