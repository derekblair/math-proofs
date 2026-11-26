import ColorBridge

namespace QuorumMinimum
open QuorumBounds Classical
variable {V C : Type} [Fintype V]
noncomputable section

def eraseColor (f : V → Option C) (i : C) (v : V) : Option C :=
  if f v = some i then none else f v

theorem eraseColor_eq_some (f : V → Option C) (i j : C) (v : V) :
    eraseColor f i v = some j ↔ f v = some j ∧ j ≠ i := by
  unfold eraseColor
  split
  · rename_i h
    simp [h,eq_comm]
  · rename_i h
    constructor
    · intro e
      exact ⟨e,fun hji => h (hji ▸ e)⟩
    · exact And.left

theorem valid_erase (G : SimpleGraph V) (f : V → Option C) (i : C)
    (hf : IsSubQuorum G f) : IsSubQuorum G (eraseColor f i) := by
  intro v j hj
  obtain ⟨hv,hji⟩ := (eraseColor_eq_some f i j v).mp hj
  have eq : allies G (eraseColor f i) v j = allies G f v j := by
    ext w
    simp [allies,eraseColor_eq_some,hji]
  have sub : others G (eraseColor f i) v j ⊆ others G f v j := by
    intro w hw
    simp only [others,Finset.mem_filter,Finset.mem_univ,true_and,eraseColor_eq_some] at hw ⊢
    obtain ⟨a,k,hw,hn⟩ := hw
    exact ⟨a,k,hw.1,hn⟩
  rw [eq]
  exact (Finset.card_le_card sub).trans (hf v j hv)

theorem support_erase (f : V → Option C) (i : C) :
    support (eraseColor f i) = support f \ fiber f (some i) := by
  ext v
  simp only [mem_support,Finset.mem_sdiff,fiber,Finset.mem_filter,Finset.mem_univ,true_and]
  unfold eraseColor
  split <;> simp_all

theorem card_erase_support (f : V → Option C) (i : C) :
    (support (eraseColor f i)).card + (fiber f (some i)).card = (support f).card := by
  rw [support_erase]
  apply Finset.card_sdiff_add_card_eq_card
  intro v h
  simp [fiber] at h
  simp [mem_support,h]

def palette (f : V → Option C) : Finset (Option C) := (Finset.univ.image f).erase none

theorem palette_support (f : V → Option C) : palette f = (support f).image f := by
  ext c
  simp [palette,mem_support]
  exact ⟨fun ⟨h,v,hv⟩ => ⟨v,hv ▸ h,hv⟩, fun ⟨v,hn,hv⟩ => ⟨hv ▸ hn,v,hv⟩⟩

theorem palette_erase (f : V → Option C) (i : C) :
    palette (eraseColor f i) = (palette f).erase (some i) := by
  ext c
  cases c with
  | none => simp [palette]
  | some j =>
    have hm (g : V → Option C) : some j ∈ palette g ↔ ∃ v, g v = some j := by
      simp [palette]
    rw [hm,Finset.mem_erase,hm]
    simp only [eraseColor_eq_some,ne_eq,Option.some.injEq]
    exact ⟨fun ⟨v,h,hj⟩ => ⟨hj,v,h⟩,fun ⟨hj,v,h⟩ => ⟨v,h,hj⟩⟩

theorem palette_loss (f : V → Option C) (i : C) :
    (palette f).card ≤ (palette (eraseColor f i)).card + 1 := by
  rw [palette_erase]
  by_cases hi : some i ∈ palette f
  · rw [Finset.card_erase_of_mem hi]
    omega
  · simp [Finset.erase_eq_of_notMem hi]

end

#print axioms valid_erase
#print axioms card_erase_support
#print axioms palette_loss

end QuorumMinimum
