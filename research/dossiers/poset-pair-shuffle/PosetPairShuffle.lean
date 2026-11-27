import Mathlib.Tactic

namespace PosetFiber

def IsPrefix (n b : ℕ) (f : ℕ → ℕ) : Prop :=
  f 0 = 0 ∧ f n = b ∧ ∀ i < n, f i ≤ f (i+1) ∧ f (i+1) ≤ f i+1

theorem prefix_min {n b : ℕ} {f g : ℕ → ℕ} (hf : IsPrefix n b f)
    (hg : IsPrefix n b g) : IsPrefix n b (fun i => min (f i) (g i)) := by
  obtain ⟨h0, hn, hs⟩ := hf
  obtain ⟨g0, gn, gs⟩ := hg
  refine ⟨by simp [h0, g0], by simp [hn, gn], ?_⟩
  intro i hi
  have h := hs i hi
  have k := gs i hi
  dsimp
  constructor <;> omega

theorem prefix_max {n b : ℕ} {f g : ℕ → ℕ} (hf : IsPrefix n b f)
    (hg : IsPrefix n b g) : IsPrefix n b (fun i => max (f i) (g i)) := by
  obtain ⟨h0, hn, hs⟩ := hf
  obtain ⟨g0, gn, gs⟩ := hg
  refine ⟨by simp [h0, g0], by simp [hn, gn], ?_⟩
  intro i hi
  have h := hs i hi
  have k := gs i hi
  dsimp
  constructor <;> omega

def Feasible (n b : ℕ) (lower f : ℕ → ℕ) : Prop :=
  IsPrefix n b f ∧ ∀ i ≤ n, lower i ≤ f i

theorem feasible_min {n b : ℕ} {lower f g : ℕ → ℕ}
    (hf : Feasible n b lower f) (hg : Feasible n b lower g) :
    Feasible n b lower (fun i => min (f i) (g i)) := by
  refine ⟨prefix_min hf.1 hg.1, ?_⟩
  intro i hi
  have a := hf.2 i hi
  have z := hg.2 i hi
  dsimp
  omega

theorem feasible_upward {n b : ℕ} {lower f g : ℕ → ℕ}
    (hf : Feasible n b lower f) (hg : IsPrefix n b g)
    (h : ∀ i ≤ n, f i ≤ g i) : Feasible n b lower g :=
  ⟨hg, fun i hi => le_trans (hf.2 i hi) (h i hi)⟩

theorem extremal_prefix {n b : ℕ} (hb : b ≤ n) :
    IsPrefix n b (fun i => min i b) := by
  refine ⟨by simp, by simpa using (min_eq_right hb), ?_⟩
  intro i hi
  dsimp
  constructor <;> omega

theorem crossed_ordinary_not_below {x z b y : ℕ}
    (hx : x < z) (hzy : z < b) (hy : b ≤ y) : x < z ∧ z < y := by omega

section Swap

variable {α : Type*} [PartialOrder α] [DecidableEq α]

def groupA (x y z : α) : Prop := z = x ∨ (x < z ∧ ¬ y < z)
def groupB (x y z : α) : Prop := z = y ∨ (z < y ∧ ¬ z < x)

theorem valid_filtered_swap
    {r : α → ℕ} (hr : StrictMono r) (hi : Function.Injective r)
    {x y a b : α} (hxy : ¬ x ≤ y)
    (ha : x ≤ a) (hb : b ≤ y) (hab : r a < r b)
    (hgap : ∀ z, r a < r z → r z < r b → ¬ groupA x y z ∧ ¬ groupB x y z) :
    StrictMono (fun z => r (Equiv.swap a b z)) := by
  have hne : a ≠ b := fun h => (ne_of_lt hab) (congrArg r h)
  have hno : ¬ a < b := fun h => hxy (ha.trans (h.le.trans hb))
  have hac : r x ≤ r a := hr.monotone ha
  have hbc : r b ≤ r y := hr.monotone hb
  intro u v huv
  have h := hr huv
  by_cases hua : u = a
  · subst u
    by_cases hvb : v = b
    · subst v
      exact (hno huv).elim
    have hva : v ≠ a := Ne.symm (ne_of_lt huv)
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hva hvb]
    by_contra! hrs
    have hz : r v < r b := lt_of_le_of_ne hrs (fun heq => hvb (hi heq))
    exact (hgap v h hz).1 (Or.inr ⟨lt_of_le_of_lt ha huv,
      fun hyv => (not_lt_of_ge (le_trans hz.le hbc)) (hr hyv)⟩)
  by_cases hvb : v = b
  · subst v
    have hub : u ≠ b := ne_of_lt huv
    simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hua hub]
    by_contra! hrs
    have hz : r a < r u := lt_of_le_of_ne hrs (fun heq => hua (hi heq.symm))
    exact (hgap u hz h).2 (Or.inr ⟨lt_of_lt_of_le huv hb,
      fun hux => (not_lt_of_ge (le_trans hac hz.le)) (hr hux)⟩)
  by_cases hub : u = b
  · subst u
    by_cases hva : v = a
    · subst v
      exact (not_lt_of_ge hab.le h).elim
    simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hva hvb]
    exact hab.trans h
  by_cases hva : v = a
  · subst v
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hua hub]
    exact h.trans hab
  simpa only [Equiv.swap_apply_of_ne_of_ne hua hub, Equiv.swap_apply_of_ne_of_ne hva hvb] using h

omit [PartialOrder α] [DecidableEq α] in
theorem exists_filtered_adjacent
    {r : α → ℕ} {A B : α → Prop}
    (h : ∃ a b, A a ∧ B b ∧ r a < r b) :
    ∃ a b, A a ∧ B b ∧ r a < r b ∧
      ∀ z, r a < r z → r z < r b → ¬ A z ∧ ¬ B z := by
  classical
  let W (d : ℕ) := ∃ a b, A a ∧ B b ∧ r a < r b ∧ r b-r a = d
  have ex : ∃ d, W d := by
    obtain ⟨a,b,ha,hb,hab⟩ := h
    exact ⟨r b-r a, a,b,ha,hb,hab,rfl⟩
  obtain ⟨a,b,ha,hb,hab,hd⟩ := Nat.find_spec ex
  refine ⟨a,b,ha,hb,hab,?_⟩
  intro z hza hzb
  constructor
  · intro az
    have hj : W (r b-r z) := ⟨z,b,az,hb,hzb,rfl⟩
    have hm := Nat.find_min' ex hj
    omega
  · intro bz
    have hj : W (r z-r a) := ⟨a,z,ha,bz,hza,rfl⟩
    have hm := Nat.find_min' ex hj
    omega

omit [DecidableEq α] in
theorem groups_disjoint {x y z : α} (hxy : ¬ x ≤ y) (ha : groupA x y z) :
    ¬ groupB x y z := by
  intro hb
  have xa : x ≤ z := ha.elim (fun h => h.symm.le) (fun h => h.1.le)
  have zy : z ≤ y := hb.elim (fun h => h.le) (fun h => h.1.le)
  exact hxy (xa.trans zy)

omit [PartialOrder α] in
private theorem swap_order_on_group
    {r : α → ℕ} (hi : Function.Injective r) {G : α → Prop}
    {a b u v : α} (hb : ¬ G b) (hu : G u) (hv : G v)
    (hgap : ∀ z, min (r a) (r b) < r z → r z < max (r a) (r b) → ¬ G z)
    (_hab : a ≠ b) :
    (r (Equiv.swap a b u) < r (Equiv.swap a b v)) ↔ r u < r v := by
  have ub : u ≠ b := fun h => hb (h ▸ hu)
  have vb : v ≠ b := fun h => hb (h ▸ hv)
  by_cases ua : u = a
  · subst u
    by_cases va : v = a
    · subst v
      simp
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne va vb]
    have kva : r v ≠ r a := fun h => va (hi h)
    have kvb : r v ≠ r b := fun h => vb (hi h)
    by_contra! h
    have hg : ¬ (min (r a) (r b) < r v ∧ r v < max (r a) (r b)) :=
      fun ⟨hh,hk⟩ => hgap v hh hk hv
    omega
  by_cases va : v = a
  · subst v
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne ua ub]
    have kua : r u ≠ r a := fun h => ua (hi h)
    have kub : r u ≠ r b := fun h => ub (hi h)
    by_contra! h
    have hg : ¬ (min (r a) (r b) < r u ∧ r u < max (r a) (r b)) :=
      fun ⟨hh,hk⟩ => hgap u hh hk hu
    omega
  simp only [Equiv.swap_apply_of_ne_of_ne ua ub, Equiv.swap_apply_of_ne_of_ne va vb]

omit [DecidableEq α] in
def SameGroupFiber (x y : α) (r s : α → ℕ) : Prop :=
  (∀ z, ¬ groupA x y z → ¬ groupB x y z → s z = r z) ∧
  (∀ u v, groupA x y u → groupA x y v → (s u < s v ↔ r u < r v)) ∧
  (∀ u v, groupB x y u → groupB x y v → (s u < s v ↔ r u < r v))

theorem sorted_rank_exists [Fintype α] {x y : α} (hxy : ¬ x ≤ y)
    (r : α → ℕ) (hr : StrictMono r) (hi : Function.Injective r) :
    ∃ s : α → ℕ, StrictMono s ∧ Function.Injective s ∧
      SameGroupFiber x y r s ∧ Set.range s = Set.range r ∧
      ∀ a b, groupA x y a → groupB x y b → s b < s a := by
  classical
  let cols := Finset.univ.filter (groupB x y)
  let W (d : ℕ) := ∃ s, StrictMono s ∧ Function.Injective s ∧
    SameGroupFiber x y r s ∧ Set.range s = Set.range r ∧ (∑ z ∈ cols, s z) = d
  have ex : ∃ d, W d := ⟨∑ z ∈ cols, r z, r, hr, hi,
    ⟨fun _ _ _ => rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩, rfl, rfl⟩
  obtain ⟨s, hs, si, sf, sr, sd⟩ := Nat.find_spec ex
  refine ⟨s, hs, si, sf, sr, ?_⟩
  by_contra! bad
  obtain ⟨a,b,ha,hb,hab⟩ := bad
  have ab : a ≠ b := fun eq => groups_disjoint hxy ha (eq ▸ hb)
  have ss : s a < s b := lt_of_le_of_ne hab (fun eq => ab (si eq))
  obtain ⟨a,b,ha,hb,hab,hgap⟩ :=
    exists_filtered_adjacent (A := groupA x y) (B := groupB x y) ⟨a,b,ha,hb,ss⟩
  have az : ¬ groupB x y a := groups_disjoint hxy ha
  have bz : ¬ groupA x y b := fun h => groups_disjoint hxy h hb
  have ab : a ≠ b := ne_of_apply_ne s (ne_of_lt hab)
  have xa : x ≤ a := ha.elim (fun h => h.symm.le) (fun h => h.1.le)
  have byy : b ≤ y := hb.elim (fun h => h.le) (fun h => h.1.le)
  let q := Equiv.swap a b
  let t := fun z => s (q z)
  have ht : StrictMono t := valid_filtered_swap hs si hxy xa byy hab hgap
  have ti : Function.Injective t := si.comp q.injective
  have tr : Set.range t = Set.range r := by
    rw [← sr]
    ext j
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨q z,rfl⟩
    · rintro ⟨z,rfl⟩
      exact ⟨q.symm z, by simp [t]⟩
  have tf : SameGroupFiber x y r t := by
    refine ⟨?_, ?_, ?_⟩
    · intro z na nb
      have za : z ≠ a := fun h => na (h ▸ ha)
      have zb : z ≠ b := fun h => nb (h ▸ hb)
      simpa only [t, q, Equiv.swap_apply_of_ne_of_ne za zb] using sf.1 z na nb
    · intro u v au av
      have z := swap_order_on_group si bz au av (fun z h1 h2 =>
        (hgap z (by omega) (by omega)).1) ab
      exact z.trans (sf.2.1 u v au av)
    · intro u v bu bv
      have z := swap_order_on_group si az bu bv (fun z h1 h2 =>
        (hgap z (by omega) (by omega)).2) ab.symm
      change s (Equiv.swap b a u) < s (Equiv.swap b a v) ↔ s u < s v at z
      rw [Equiv.swap_comm b a] at z
      exact z.trans (sf.2.2 u v bu bv)
  have bw : b ∈ cols := by simp [cols, hb]
  have less : (∑ z ∈ cols, t z) < (∑ z ∈ cols, s z) := by
    apply Finset.sum_lt_sum
    · intro z hz
      have zB : groupB x y z := (Finset.mem_filter.mp hz).2
      have za : z ≠ a := fun h => az (h ▸ zB)
      by_cases zb : z = b
      · subst z
        simpa only [t, q, Equiv.swap_apply_right] using hab.le
      · simp [t, q, Equiv.swap_apply_of_ne_of_ne za zb]
    · exact ⟨b, bw, by simpa only [t, q, Equiv.swap_apply_right] using hab⟩
  have w : W (∑ z ∈ cols, t z) := ⟨t,ht,ti,tf,tr,rfl⟩
  have hm := Nat.find_min' ex w
  omega

omit [PartialOrder α] [DecidableEq α] in
private theorem eq_on_of_rank_image {r s : α → ℕ} (_ri : Function.Injective r)
    (si : Function.Injective s) {G : Set α} (im : r '' G = s '' G)
    (hr : ∀ u ∈ G, ∀ v ∈ G, (r u < r v ↔ s u < s v)) :
    Set.EqOn r s G := by
  classical
  unfold Set.EqOn
  by_contra! he
  let W (d : ℕ) := ∃ z ∈ G, r z = d ∧ r z ≠ s z
  have ex : ∃ d, W d := by
    obtain ⟨z,hz,hn⟩ := he
    exact ⟨r z,z,hz,rfl,hn⟩
  obtain ⟨z,hz,hd,hn⟩ := Nat.find_spec ex
  rcases lt_or_gt_of_ne hn with lt | gt
  · have hm : r z ∈ s '' G := by rw [← im]; exact ⟨z,hz,rfl⟩
    obtain ⟨u,hu,h⟩ := hm
    have huv : r u < r z := (hr u hu z hz).mpr (h ▸ lt)
    have huq : r u ≠ s u := by omega
    have notmin := Nat.find_min' ex (show W (r u) from ⟨u,hu,rfl,huq⟩)
    omega
  · have hm : s z ∈ r '' G := by rw [im]; exact ⟨z,hz,rfl⟩
    obtain ⟨u,hu,h⟩ := hm
    have huv : r u < r z := h ▸ gt
    have huq : r u ≠ s u := by
      intro hh
      exact (ne_of_lt huv) (congrArg r (si (hh ▸ h)))
    have notmin := Nat.find_min' ex (show W (r u) from ⟨u,hu,rfl,huq⟩)
    omega

omit [PartialOrder α] [DecidableEq α] in
private theorem group_images_equal {r s : α → ℕ} (ri : Function.Injective r)
    (si : Function.Injective s) {G : Set α} (ran : Set.range r = Set.range s)
    (out : Set.EqOn r s Gᶜ) : r '' G = s '' G := by
  classical
  ext j
  constructor
  · rintro ⟨z,hz,rfl⟩
    have h : r z ∈ Set.range s := by rw [← ran]; exact ⟨z,rfl⟩
    obtain ⟨u,hu⟩ := h
    by_cases hh : u ∈ G
    · exact ⟨u,hh,hu⟩
    · exact (hh (ri ((out hh).trans hu) ▸ hz)).elim
  · rintro ⟨z,hz,rfl⟩
    have h : s z ∈ Set.range r := by rw [ran]; exact ⟨z,rfl⟩
    obtain ⟨u,hu⟩ := h
    by_cases hh : u ∈ G
    · exact ⟨u,hh,hu⟩
    · exact (hh (si ((out hh).symm.trans hu) ▸ hz)).elim

omit [DecidableEq α] in
theorem reconstruct_rank {x y : α} (hxy : ¬ x ≤ y) {r s t : α → ℕ}
    (ri : Function.Injective r) (si : Function.Injective s)
    (ra : SameGroupFiber x y r t) (sa : SameGroupFiber x y s t)
    (ran : Set.range r = Set.range s)
    (Bim : r '' {z | groupB x y z} = s '' {z | groupB x y z}) : r = s := by
  classical
  let A : Set α := {z | groupA x y z}
  let B : Set α := {z | groupB x y z}
  let G := A ∪ B
  have out : Set.EqOn r s Gᶜ := by
    intro z hz
    have hA : ¬ groupA x y z := fun h => hz (Or.inl h)
    have hB : ¬ groupB x y z := fun h => hz (Or.inr h)
    exact (ra.1 z hA hB).symm.trans (sa.1 z hA hB)
  have gim := group_images_equal ri si ran out
  have aim : r '' A = s '' A := by
    have im {u : α → ℕ} (ui : Function.Injective u) : u '' A = u '' G \ u '' B := by
      ext j
      constructor
      · rintro ⟨z,hz,rfl⟩
        refine ⟨⟨z,Or.inl hz,rfl⟩,?_⟩
        rintro ⟨w,hw,hwz⟩
        exact groups_disjoint hxy hz (ui hwz ▸ hw)
      · rintro ⟨⟨z,hz,rfl⟩, hn⟩
        rcases hz with h | h
        · exact ⟨z,h,rfl⟩
        · exact (hn ⟨z,h,rfl⟩).elim
    rw [im ri,im si,gim]
    congr 1
  have aa := eq_on_of_rank_image ri si aim
    (fun u hu v hv => (ra.2.1 u v hu hv).symm.trans (sa.2.1 u v hu hv))
  have bb := eq_on_of_rank_image ri si Bim
    (fun u hu v hv => (ra.2.2 u v hu hv).symm.trans (sa.2.2 u v hu hv))
  funext z
  by_cases h : z ∈ G
  · exact h.elim (aa ·) (bb ·)
  · exact out h

end Swap

theorem count_from_encoding {E R : Type*} [Fintype E] [Fintype R]
    {n b : ℕ}
    (encode : E → R × ↥((Finset.univ : Finset (Fin n)).powersetCard b))
    (inj : Function.Injective encode) :
    Fintype.card E ≤ Fintype.card R * n.choose b := by
  have h := Fintype.card_le_of_injective encode inj
  simpa [Fintype.card_prod, Finset.card_powersetCard] using h

def RankLinearExtension (α : Type*) [PartialOrder α] [Fintype α] :=
  {r : α ≃ Fin (Fintype.card α) // StrictMono r}

noncomputable def naturalRank {α : Type*} [PartialOrder α] [Fintype α]
    (r : RankLinearExtension α) (z : α) : ℕ := (r.val z).val

theorem choose_bound_for_rank_extensions {α : Type*} [PartialOrder α] [Fintype α]
    {x y : α} (hxy : ¬ x ≤ y) :
    Nat.card (RankLinearExtension α) ≤
    Nat.card {r : RankLinearExtension α // naturalRank r y < naturalRank r x} *
      (Nat.card {z : α // groupA x y z ∨ groupB x y z}).choose
        (Nat.card {z : α // groupB x y z}) := by
  classical
  let E := RankLinearExtension α
  let R := {r : E // naturalRank r y < naturalRank r x}
  let G := Finset.univ.filter (fun z : α => groupA x y z ∨ groupB x y z)
  let B := Finset.univ.filter (groupB x y)
  have sub : B ⊆ G := by
    intro z hz
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp [G, hz]
  have rinj (r : E) : Function.Injective (naturalRank r) :=
    fun _ _ he => r.val.injective (Fin.ext he)
  have rmono (r : E) : StrictMono (naturalRank r) := fun _ _ h => r.property h
  have rr (r : E) : Set.range (naturalRank r) = Set.Iio (Fintype.card α) := by
    ext j
    change (∃ z : α, (r.val z).val = j) ↔ j < Fintype.card α
    constructor
    · rintro ⟨z,rfl⟩
      exact (r.val z).isLt
    · intro h
      exact ⟨r.val.symm ⟨j,h⟩, congrArg Fin.val (r.val.apply_symm_apply _)⟩
  have reps : ∀ r : E, ∃ u : R, SameGroupFiber x y (naturalRank r) (naturalRank u.val) := by
    intro r
    obtain ⟨s,sm,si,sf,sr,so⟩ :=
      sorted_rank_exists hxy (naturalRank r) (rmono r) (rinj r)
    have su (z : α) : s z < Fintype.card α := by
      change s z ∈ Set.Iio (Fintype.card α)
      rw [← rr r, ← sr]
      exact ⟨z,rfl⟩
    let f (z : α) : Fin (Fintype.card α) := ⟨s z,su z⟩
    have hbij : Function.Bijective f := by
      refine ⟨fun a b h => si (congrArg Fin.val h),?_⟩
      intro j
      have h : j.val ∈ Set.range s := by rw [sr,rr r]; exact j.isLt
      obtain ⟨z,hz⟩ := h
      exact ⟨z,Fin.ext hz⟩
    let v : E := ⟨Equiv.ofBijective f hbij, fun _ _ h => sm h⟩
    let u : R := ⟨v, so x y (Or.inl rfl) (Or.inl rfl)⟩
    exact ⟨u,sf⟩
  choose rep hrep using reps
  let spots (r : E) := G.image (naturalRank r)
  have sc (r : E) : (spots r).card = G.card := Finset.card_image_of_injective _ (rinj r)
  let digits (r : E) (z : B) : Fin G.card :=
    ((spots r).orderIsoOfFin (sc r)).symm
      ⟨naturalRank r z, Finset.mem_image.mpr ⟨z,sub z.property,rfl⟩⟩
  let mask (r : E) : Finset (Fin G.card) := Finset.univ.image (digits r)
  have dc (r : E) : (mask r).card = B.card := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro u v he
      have h := ((spots r).orderIsoOfFin (sc r)).symm.injective he
      exact Subtype.ext (rinj r (congrArg Subtype.val h))
  have me (r : E) : mask r ∈ (Finset.univ : Finset (Fin G.card)).powersetCard B.card :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, dc r⟩
  let enc (r : E) := (rep r, (⟨mask r,me r⟩ :
      ↥((Finset.univ : Finset (Fin G.card)).powersetCard B.card)))
  have encinj : Function.Injective enc := by
    intro r s h
    have pr : rep r = rep s := congrArg Prod.fst h
    have pm : mask r = mask s := congrArg (fun p => p.2.val) h
    have rs : Set.range (naturalRank r) = Set.range (naturalRank s) := (rr r).trans (rr s).symm
    have sf := hrep s
    rw [← pr] at sf
    have setsp : naturalRank r '' (G : Set α) = naturalRank s '' (G : Set α) := by
      apply group_images_equal (rinj r) (rinj s) rs
      intro z hz
      have ha : ¬ groupA x y z := by
        intro ha
        exact hz (by simp [G,ha])
      have hb : ¬ groupB x y z := by
        intro hb
        exact hz (by simp [G,hb])
      exact ((hrep r).1 z ha hb).symm.trans (sf.1 z ha hb)
    have sp : spots r = spots s := by
      ext j
      change j ∈ (↑(G.image (naturalRank r)) : Set ℕ) ↔
        j ∈ (↑(G.image (naturalRank s)) : Set ℕ)
      simpa only [Finset.coe_image] using Set.ext_iff.mp setsp j
    have decode (q : E) :
        (mask q).image (fun i => ((spots q).orderIsoOfFin (sc q) i).val) =
          B.image (naturalRank q) := by
      ext j
      simp only [mask, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i,⟨z,rfl⟩,h⟩
        exact ⟨z,z.property,by simpa [digits] using h⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨digits q ⟨z,hz⟩,⟨⟨z,hz⟩,rfl⟩,by simp [digits]⟩
    have deq : B.image (naturalRank r) = B.image (naturalRank s) := by
      rw [← decode r, ← decode s, pm]
      have he : (fun i => ((spots r).orderIsoOfFin (sc r) i).val) =
          (fun i => ((spots s).orderIsoOfFin (sc s) i).val) := by
        funext i
        simp only [Finset.coe_orderIsoOfFin_apply, sp]
      rw [he]
    have bim : naturalRank r '' {z | groupB x y z} = naturalRank s '' {z | groupB x y z} := by
      have idb : (B : Set α) = {z | groupB x y z} := by ext z; simp [B]
      rw [← idb, ← Finset.coe_image, ← Finset.coe_image, deq]
    have hr := reconstruct_rank hxy (rinj r) (rinj s) (hrep r) sf rs bim
    exact Subtype.ext (Equiv.ext fun z => Fin.ext (congrFun hr z))
  let fe : Finite E := Finite.of_injective
    (fun r : E => (r.val : α → Fin (Fintype.card α)))
    (fun r s h => Subtype.ext (Equiv.ext (congrFun h)))
  let fE : Fintype E := Fintype.ofFinite E
  let fR : Fintype R := Fintype.ofFinite R
  have hh := count_from_encoding enc encinj
  have gc : Nat.card {z : α // groupA x y z ∨ groupB x y z} = G.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofFinset (p := {z | groupA x y z ∨ groupB x y z}) G
      (fun z => by simp [G])
  have bc : Nat.card {z : α // groupB x y z} = B.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofFinset (p := {z | groupB x y z}) B (fun z => by simp [B])
  rw [gc,bc]
  exact (Nat.card_eq_fintype_card (α := E)).trans_le <|
    hh.trans_eq (by rw [Nat.card_eq_fintype_card])

end PosetFiber

#print axioms PosetFiber.choose_bound_for_rank_extensions
#print axioms PosetFiber.sorted_rank_exists
