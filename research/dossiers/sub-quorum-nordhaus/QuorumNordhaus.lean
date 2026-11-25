import QuorumIncidence

open SimpleGraph
open scoped BigOperators
namespace QuorumBounds

universe u v w
variable {V : Type u} {A : Type v} {B : Type w} [Fintype V] [Fintype A] [Fintype B]

noncomputable section

def allies {C : Type*} (G : SimpleGraph V) (f : V → Option C) (x : V) (i : C) : Finset V :=
  open Classical in Finset.univ.filter fun y => G.Adj x y ∧ f y = some i

def others {C : Type*} (G : SimpleGraph V) (f : V → Option C) (x : V) (i : C) : Finset V :=
  open Classical in Finset.univ.filter fun y => G.Adj x y ∧ ∃ j, f y = some j ∧ j ≠ i

/-- The paper's weak majority of the colored closed neighborhood:
    other-colored neighbors do not exceed same-colored neighbors plus self. -/
def IsSubQuorum {C : Type*} (G : SimpleGraph V) (f : V → Option C) : Prop :=
  ∀ x i, f x = some i → (others G f x i).card ≤ (allies G f x i).card + 1

def coloredClosed {C : Type*} (G : SimpleGraph V) (f : V → Option C) (x : V) :
    Finset V := open Classical in Finset.univ.filter fun y =>
      (x = y ∨ G.Adj x y) ∧ ∃ i, f y = some i

def sameClosed {C : Type*} (G : SimpleGraph V) (f : V → Option C) (x : V) (i : C) :
    Finset V := open Classical in Finset.univ.filter fun y =>
      (x = y ∨ G.Adj x y) ∧ f y = some i

/-- Direct equivalence to the weak closed-neighborhood majority in Definition 2.2. -/
theorem subQuorum_iff_closed {C : Type*} (G : SimpleGraph V) (f : V → Option C) :
    IsSubQuorum G f ↔ ∀ x i, f x = some i →
      (coloredClosed G f x).card ≤ 2 * (sameClosed G f x i).card := by
  classical
  unfold IsSubQuorum
  refine forall_congr' fun x => forall_congr' fun i => ?_
  constructor <;> intro h hx
  all_goals
    have hd : Disjoint (allies G f x i) (others G f x i) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      simp only [allies,others,Finset.mem_filter,Finset.mem_univ,true_and] at hy hy'
      obtain ⟨j,hj,hji⟩ := hy'.2
      exact hji (Option.some.inj (hj.symm.trans hy.2))
    have hna : x ∉ allies G f x i := by simp [allies]
    have hno : x ∉ others G f x i := by simp [others]
    have hsame : sameClosed G f x i = insert x (allies G f x i) := by
      ext y
      by_cases he : x = y
      · subst y
        simp [sameClosed,hx]
      · simp [sameClosed,allies,he,Ne.symm he]
    have hcol : coloredClosed G f x = insert x (allies G f x i ∪ others G f x i) := by
      ext y
      by_cases he : x = y
      · subst y
        simp [coloredClosed,hx]
      · simp only [coloredClosed,allies,others,Finset.mem_filter,Finset.mem_univ,true_and,
          Finset.mem_insert,Finset.mem_union,he,Ne.symm he,false_or]
        constructor
        · rintro ⟨hy, j,hj⟩
          by_cases hji : j = i
          · exact Or.inl ⟨hy,hji ▸ hj⟩
          · exact Or.inr ⟨hy,j,hj,hji⟩
        · rintro (⟨hy,hi⟩|⟨hy,j,hj,_⟩)
          · exact ⟨hy,i,hi⟩
          · exact ⟨hy,j,hj⟩
    have eq₁ := Finset.card_insert_of_notMem hna
    have eq₂ := Finset.card_insert_of_notMem
      (show x ∉ allies G f x i ∪ others G f x i from by simp [hna,hno])
    rw [Finset.card_union_of_disjoint hd] at eq₂
    have hh := h hx
    simp only [hsame,hcol,eq₁,eq₂] at hh ⊢
    omega

variable {G : SimpleGraph V} {f : V → Option A} {g : V → Option B}

omit [Fintype A] [Fintype B] in
theorem alliesBound (c : (Inc f g).ConnectedComponent)
    {x : V} (hx : x ∈ members f g c) {i : A} {j : B}
    (hi : f x = some i) (hj : g x = some j) :
    (allies G f x i).card + (allies Gᶜ g x j).card + 1 ≤ (members f g c).card := by
  classical
  have hd : Disjoint (allies G f x i) (allies Gᶜ g x j) := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    simp only [allies,Finset.mem_filter,Finset.mem_univ,true_and] at hy hz
    exact ((SimpleGraph.compl_adj G _ _).mp hz.1).2 hy.1
  rw [← Finset.card_union_of_disjoint hd]
  have ha : (allies G f x i ∪ allies Gᶜ g x j) ⊆ (members f g c).erase x := by
    intro y hy
    rcases Finset.mem_union.mp hy with h|h
    · simp only [allies,Finset.mem_filter,Finset.mem_univ,true_and] at h
      exact Finset.mem_erase.mpr ⟨h.1.ne', (mem_members f g).mpr
        ((owner_left f g h.2).trans ((owner_left f g hi).symm.trans ((mem_members f g).mp hx)))⟩
    · simp only [allies,Finset.mem_filter,Finset.mem_univ,true_and] at h
      exact Finset.mem_erase.mpr ⟨h.1.ne', (mem_members f g).mpr
        ((owner_right f g h.2).trans ((owner_right f g hj).symm.trans ((mem_members f g).mp hx)))⟩
  have hh := Finset.card_le_card ha
  rw [Finset.card_erase_of_mem hx] at hh
  have hn := Finset.card_pos.mpr (show (members f g c).Nonempty from ⟨x,hx⟩)
  omega

open Classical in
omit [Fintype A] [Fintype B] in
theorem cross_subset (c : (Inc f g).ConnectedComponent)
    {x : V} (hx : x ∈ members f g c) {i : A} {j : B}
    (hi : f x = some i) (hj : g x = some j) (X : Finset V)
    (hX : ∀ y ∈ X, y ∉ members f g c ∧ (∃ a, f y = some a) ∧ (∃ b, g y = some b)) :
    X ⊆ others G f x i ∪ others Gᶜ g x j := by
  classical
  intro y hy
  obtain ⟨hn, ⟨a,ha⟩,⟨b,hb⟩⟩ := hX y hy
  have hxy : x ≠ y := by rintro rfl; exact hn hx
  have hia : a ≠ i := by
    rintro rfl
    exact hn ((mem_members f g).mpr
       ((owner_left f g ha).trans ((owner_left f g hi).symm.trans ((mem_members f g).mp hx))))
  have hjb : b ≠ j := by
    rintro rfl
    exact hn ((mem_members f g).mpr
       ((owner_right f g hb).trans ((owner_right f g hj).symm.trans ((mem_members f g).mp hx))))
  apply Finset.mem_union.mpr
  by_cases hh : G.Adj x y
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh,⟨a,ha,hia⟩⟩)
  · apply Or.inr
    simp only [others,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨(SimpleGraph.compl_adj G _ _).mpr ⟨hxy,hh⟩,⟨b,hb,hjb⟩⟩

theorem cross_bound (h₁ : IsSubQuorum G f) (h₂ : IsSubQuorum Gᶜ g)
    (c d e : (Inc f g).ConnectedComponent) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hd : Positive f g d) (he : Positive f g e)
    {x : V} (hx : x ∈ members f g c) {i : A} {j : B}
    (hi : f x = some i) (hj : g x = some j) :
    (members f g d).card + (members f g e).card ≤ (members f g c).card + 1 := by
  classical
  rw [← Finset.card_union_of_disjoint (members_disjoint f g hde)]
  have hs := cross_subset (G := G) c hx hi hj (members f g d ∪ members f g e) (by
    intro y hy
    rcases Finset.mem_union.mp hy with hy|hy
    · obtain ⟨a,b,ha,hb⟩ := positive_both f g d hd hy
      exact ⟨fun hh => Finset.disjoint_left.mp (members_disjoint f g hcd) hh hy,⟨a,ha⟩,⟨b,hb⟩⟩
    · obtain ⟨a,b,ha,hb⟩ := positive_both f g e he hy
      exact ⟨fun hh => Finset.disjoint_left.mp (members_disjoint f g hce) hh hy,⟨a,ha⟩,⟨b,hb⟩⟩)
  have hb := Finset.card_le_card hs
  have hc := Finset.card_union_le (others G f x i) (others Gᶜ g x j)
  have hh := alliesBound (G := G) c hx hi hj
  have hq₁ := h₁ x i hi
  have hq₂ := h₂ x j hj
  omega

-- Two distinctly colored outside vertices cannot both be adjacent on either side
-- to a vertex whose positive component contains only itself.
theorem not_two {D : Type*} {H : SimpleGraph V} {p : V → Option D}
    (hH : IsSubQuorum H p) {x y z : V} (hyz : y ≠ z)
    {i a b : D} (hi : p x = some i) (ha : p y = some a) (hb : p z = some b)
    (hai : a ≠ i) (hbi : b ≠ i)
    (hcap : (allies H p x i).card = 0)
    (hy : H.Adj x y) (hz : H.Adj x z) : False := by
  classical
  have yh : y ∈ others H p x i := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hy,⟨a,ha,hai⟩⟩
  have zh : z ∈ others H p x i := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hz,⟨b,hb,hbi⟩⟩
  have hf : ({y,z} : Finset V) ⊆ others H p x i := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl <;> assumption
  have hs := Finset.card_le_card hf
  simp [hyz] at hs
  have hh := hH x i hi
  omega

theorem no_three_positive (hf : ∀ i, ∃ x, f x = some i) (hg : ∀ j, ∃ x, g x = some j)
    (h₁ : IsSubQuorum G f) (h₂ : IsSubQuorum Gᶜ g)
    (c d e : (Inc f g).ConnectedComponent) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hc : Positive f g c) (hd : Positive f g d) (he : Positive f g e) : False := by
  classical
  obtain ⟨x,hx⟩ := members_nonempty f g hf hg c
  obtain ⟨y,hy⟩ := members_nonempty f g hf hg d
  obtain ⟨z,hz⟩ := members_nonempty f g hf hg e
  obtain ⟨i,j,hi,hj⟩ := positive_both f g c hc hx
  obtain ⟨a,b,ha,hb⟩ := positive_both f g d hd hy
  obtain ⟨s,t,hs,ht⟩ := positive_both f g e he hz
  have hbc := cross_bound h₁ h₂ c d e hcd hce hde hd he hx hi hj
  have hac := cross_bound h₁ h₂ d c e hcd.symm hde hce hc he hy ha hb
  have hab := cross_bound h₁ h₂ e c d hce.symm hde.symm hcd hc hd hz hs ht
  have xc := Finset.card_pos.mpr (show (members f g c).Nonempty from ⟨x,hx⟩)
  have yc := Finset.card_pos.mpr (show (members f g d).Nonempty from ⟨y,hy⟩)
  have zc := Finset.card_pos.mpr (show (members f g e).Nonempty from ⟨z,hz⟩)
  have hxc := alliesBound (G := G) c hx hi hj
  have hyc := alliesBound (G := G) d hy ha hb
  have hzc := alliesBound (G := G) e hz hs ht
  have hdif {C D : (Inc f g).ConnectedComponent} (hne : C ≠ D)
      {u v : V} (hu : u ∈ members f g C) (hv : v ∈ members f g D)
      {k : A} {l : B} (hk : f u = some k) (hl : g u = some l) :
      u ≠ v ∧ f u ≠ f v ∧ g u ≠ g v := by
    have hu' := (mem_members f g).mp hu
    have hv' := (mem_members f g).mp hv
    have hown := show owner f g u ≠ owner f g v from fun e =>
      hne (Option.some.inj (hu'.symm.trans (e.trans hv')))
    refine ⟨fun e => hown (congrArg (owner f g) e),?_,?_⟩
    · intro eq
      exact hown ((owner_left f g hk).trans (owner_left f g (eq.symm.trans hk)).symm)
    · intro eq
      exact hown ((owner_right f g hl).trans (owner_right f g (eq.symm.trans hl)).symm)
  obtain ⟨hxy,hia,hjb⟩ := hdif hcd hx hy hi hj
  obtain ⟨hxz,his,hjt⟩ := hdif hce hx hz hi hj
  obtain ⟨hyz,has,hbt⟩ := hdif hde hy hz ha hb
  have hia' : i ≠ a := by intro e; exact hia (hi.trans (e ▸ ha.symm))
  have hjb' : j ≠ b := by intro e; exact hjb (hj.trans (e ▸ hb.symm))
  have his' : i ≠ s := by intro e; exact his (hi.trans (e ▸ hs.symm))
  have hjt' : j ≠ t := by intro e; exact hjt (hj.trans (e ▸ ht.symm))
  have has' : a ≠ s := by intro e; exact has (ha.trans (e ▸ hs.symm))
  have hbt' : b ≠ t := by intro e; exact hbt (hb.trans (e ▸ ht.symm))
  by_cases hxy' : G.Adj x y
  · have hxz' : ¬ G.Adj x z := fun hh =>
      not_two h₁ hyz hi ha hs hia'.symm his'.symm (by omega) hxy' hh
    have hyz' : ¬ G.Adj y z := fun hh =>
      not_two h₁ hxz ha hi hs hia' has'.symm (by omega) hxy'.symm hh
    exact not_two h₂ hxy ht hj hb hjt' hbt' (by omega)
      ((SimpleGraph.compl_adj G _ _).mpr ⟨hxz.symm,fun h => hxz' h.symm⟩)
      ((SimpleGraph.compl_adj G _ _).mpr ⟨hyz.symm,fun h => hyz' h.symm⟩)
  · have hh : Gᶜ.Adj x y := (SimpleGraph.compl_adj G _ _).mpr ⟨hxy,hxy'⟩
    have hxz' : G.Adj x z := of_not_not fun h =>
      not_two h₂ hyz hj hb ht hjb'.symm hjt'.symm (by omega) hh
        ((SimpleGraph.compl_adj G _ _).mpr ⟨hxz,h⟩)
    have hyz' : G.Adj y z := of_not_not fun h =>
      not_two h₂ hxz hb hj ht hjb' hbt'.symm (by omega) hh.symm
        ((SimpleGraph.compl_adj G _ _).mpr ⟨hyz,h⟩)
    exact not_two h₁ hxy hs hi ha his' has' (by omega) hxz'.symm hyz'.symm

theorem pos_card_le (hf : ∀ i, ∃ x, f x = some i) (hg : ∀ j, ∃ x, g x = some j)
    (h₁ : IsSubQuorum G f) (h₂ : IsSubQuorum Gᶜ g)
    (S : Finset (Inc f g).ConnectedComponent) (hS : ∀ c ∈ S, Positive f g c) :
    S.card ≤ 2 := by
  classical
  by_contra! hh
  obtain ⟨c,hc⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hdcard : (S.erase c).card = S.card - 1 := Finset.card_erase_of_mem hc
  obtain ⟨d,hd⟩ := Finset.card_pos.mp (show 0 < (S.erase c).card by omega)
  have hecard : ((S.erase c).erase d).card = (S.erase c).card - 1 :=
    Finset.card_erase_of_mem hd
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < ((S.erase c).erase d).card by omega)
  have hd' := Finset.mem_erase.mp hd
  have he' := Finset.mem_erase.mp he
  have he'' := Finset.mem_erase.mp he'.2
  exact no_three_positive hf hg h₁ h₂ c d e hd'.1.symm he''.1.symm he'.1.symm
    (hS c hc) (hS d hd'.2) (hS e he''.2)

/-- Ma–Sahbi–Zhang Conjecture 9.2: the number of colors in any two
    onto partial sub-quorum colorings of complementary graphs sums to at most n+2. -/
theorem nordhausGaddum (hf : ∀ i, ∃ x, f x = some i) (hg : ∀ j, ∃ x, g x = some j)
    (h₁ : IsSubQuorum G f) (h₂ : IsSubQuorum Gᶜ g) :
    Fintype.card A + Fintype.card B ≤ Fintype.card V + 2 := by
  classical
  letI := Fintype.ofFinite (Inc f g).ConnectedComponent
  let U : Finset (Inc f g).ConnectedComponent := Finset.univ
  let P := U.filter (Positive f g)
  have hp : P.card ≤ 2 := pos_card_le hf hg h₁ h₂ P
    (fun _ h => (Finset.mem_filter.mp h).2)
  have hs₁ : (∑ c ∈ U, (palette f g c).card) = Fintype.card A + Fintype.card B := by
    have hh := (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (A ⊕ B)))
      (t := U) (f := (Inc f g).connectedComponentMk) (by intro x _; exact Finset.mem_univ _)).symm
    simpa only [palette, Finset.card_univ, Fintype.card_sum] using hh
  have hs₂ : (∑ c ∈ U, (members f g c).card) ≤ Fintype.card V := by
    calc
      _ = ∑ c ∈ U.image some, ((Finset.univ : Finset V).filter fun x => owner f g x = c).card := by
        rw [Finset.sum_image (fun _ _ _ _ he => Option.some.inj he)]
        rfl
      _ = ((Finset.univ : Finset V).filter fun x => owner f g x ∈ U.image some).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ _ := Finset.card_le_univ _
  have hs₃ : (∑ c ∈ U, if Positive f g c then 1 else 0) = P.card := by
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  have hsum : (∑ c ∈ U, (palette f g c).card) ≤
      ∑ c ∈ U, ((members f g c).card + if Positive f g c then 1 else 0) := by
    apply Finset.sum_le_sum
    intro c _
    by_cases hc : Positive f g c
    · simpa [hc] using palette_bound f g c
    · have hle : (palette f g c).card ≤ (members f g c).card := by
        exact Nat.le_of_not_lt hc
      simpa [hc] using hle
  rw [Finset.sum_add_distrib,hs₁,hs₃] at hsum
  omega

#print axioms nordhausGaddum

end
end QuorumBounds
