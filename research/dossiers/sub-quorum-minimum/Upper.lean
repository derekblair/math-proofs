import Peel

namespace QuorumMinimum

open Classical QuorumBounds
variable {V C : Type} [Fintype V]
noncomputable section

def Dense (G : SimpleGraph V) (T : Nat) : Prop :=
  ∀ (W : Type) [Fintype W] (u : W ↪ V), T≤Fintype.card W →
    Fintype.card W*(Fintype.card W-1) ≤ 8*ec (G.comap u)

theorem mapped_fiber (f : V → Option C) (i : C) :
    (fiber (supportColor f) (some i)).map (supportEmb f) = fiber f (some i) := by
  ext y
  constructor
  · intro h
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
  · intro h
    have hc : f y = some i := by simpa [fiber] using h
    let u : support f := ⟨y,(mem_support f y).mpr (by simp [hc])⟩
    refine Finset.mem_map.mpr ⟨u, ?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩

theorem find_color (G : SimpleGraph V) (T : Nat) (tpos : 0<T) (D : Dense G T)
    (f : V → Option C) (valid : IsSubQuorum G f) (hf : T ≤ (support f).card) :
    ∃ i : C, (support f).card + 3 ≤ 8*(fiber f (some i)).card := by
  have fs := Fintype.card_coe (support f)
  have hh : T ≤ Fintype.card (support f) := by rwa [fs]
  obtain ⟨v,hv⟩ := max_class_of_dense (G.comap (supportEmb f)) (supportColor f)
    (valid_support G f valid) (tpos.trans_le hh) (D (support f) (supportEmb f) hh)
  cases h : f v with
  | none => exact ((mem_support f v).mp v.property h).elim
  | some i =>
    have h' : supportColor f v = some i := h
    rw [fs,h',←Finset.card_map (supportEmb f),mapped_fiber] at hv
    exact ⟨i,hv⟩

abbrev Col (G : SimpleGraph V) (C : Type) := {f : V → Option C // IsSubQuorum G f}

def peelStep (G : SimpleGraph V) (T : Nat) (tpos : 0<T) (D : Dense G T)
    (f : Col G C) : Col G C :=
  if h : T ≤ (support f.val).card then
    let i := (find_color G T tpos D f.val f.property h).choose
    ⟨eraseColor f.val i, valid_erase G f.val i f.property⟩
  else f

theorem step_shrink (G : SimpleGraph V) (T : Nat) (tpos : 0<T) (D : Dense G T)
    (f : Col G C) :
    let g := peelStep G T tpos D f
    (support g.val).card ≤ (support f.val).card ∧
    (T ≤ (support f.val).card → 8*(support g.val).card ≤ 7*(support f.val).card) ∧
    (palette f.val).card ≤ (palette g.val).card + 1 := by
  dsimp only
  by_cases h : T ≤ (support f.val).card
  · let i := (find_color G T tpos D f.val f.property h).choose
    have he : peelStep G T tpos D f = ⟨eraseColor f.val i, valid_erase G f.val i f.property⟩ := by
      unfold peelStep
      rw [dite_eq_left h]
    rw [he]
    have cap : (support f.val).card + 3 ≤ 8*(fiber f.val (some i)).card :=
      (find_color G T tpos D f.val f.property h).choose_spec
    have eq := card_erase_support f.val i
    change (support (eraseColor f.val i)).card ≤ (support f.val).card ∧
      (T ≤ (support f.val).card → 8*(support (eraseColor f.val i)).card ≤ 7*(support f.val).card) ∧
      (palette f.val).card ≤ (palette (eraseColor f.val i)).card + 1
    exact ⟨by omega,fun _ => by omega,palette_loss f.val i⟩
  · have he : peelStep G T tpos D f = f := by
      unfold peelStep
      rw [dite_eq_right h]
    rw [he]
    exact ⟨le_rfl,fun hh => (h hh).elim,by omega⟩

theorem palette_upper (G : SimpleGraph V) (L : Nat) (hV : Fintype.card V ≤ 2^L)
    (D : Dense G (32*L+1)) (f : V → Option C) (hf : IsSubQuorum G f)
    (lp : 0<L) : (palette f).card ≤ 40*L := by
  let T := 32*L+1
  have t2 : 2≤T := by dsimp [T]; omega
  let st := peelStep (C:=C) G T (by omega) D
  let a : Nat → Col G C := Nat.rec ⟨f,hf⟩ (fun _ x => st x)
  let s (j : Nat) := (support (a j).val).card
  let p (j : Nat) := (palette (a j).val).card
  have H (j : Nat) : s (j+1) ≤ s j ∧ (T≤s j → 8*s (j+1) ≤ 7*s j) ∧
      p j ≤ p (j+1)+1 := step_shrink G T _ D (a j)
  have s0 : s 0 ≤ 2^L := Finset.card_le_univ (support f) |>.trans hV
  have endS := reaches_small s L T t2 s0 (fun j => (H j).1) (fun j => (H j).2.1)
  have loss (j : Nat) : p 0 ≤ p j+j := by
    induction j with
    | zero => simp
    | succ j ih => have h := (H j).2.2; omega
  have ps (j : Nat) : p j ≤ s j := by
    dsimp [p,s]
    rw [palette_support]
    exact Finset.card_image_le
  have Ls := loss (8*L)
  have le := ps (8*L)
  dsimp [T] at endS
  change p 0 ≤ 40*L
  omega

theorem surj_card (f : V → Option (Fin k)) (h : ∀ i, ∃ x, f x = some i) :
    k ≤ (palette f).card := by
  classical
  let b (i : Fin k) : palette f := ⟨some i,by simp [palette,h i]⟩
  have hj : Function.Injective b := by
    intro i j e
    exact Option.some.inj (congrArg Subtype.val e)
  simpa using Fintype.card_le_of_injective b hj

theorem min_order_upper (n L : Nat) (lp : 0<L) (h : n≤2^L) :
    ∃ G : SimpleGraph (Fin n), ∀ a b (f : Fin n → Option (Fin a)) (g : Fin n → Option (Fin b)),
      (∀ i, ∃ v, f v = some i) → (∀ j, ∃ v, g v = some j) →
      IsSubQuorum G f → IsSubQuorum Gᶜ g → a+b≤80*L := by
  obtain ⟨G,hd⟩ := dense_all_both n L lp h
  refine ⟨G,fun a b f g sf sg vf vg => ?_⟩
  have x := (surj_card f sf).trans (palette_upper G L (by simpa using h)
    (fun W _ u hu => (hd W u hu).1) f vf lp)
  have y := (surj_card g sg).trans (palette_upper Gᶜ L (by simpa using h)
    (fun W _ u hu => (hd W u hu).2) g vg lp)
  omega

end

#print axioms palette_upper
#print axioms min_order_upper

end QuorumMinimum
