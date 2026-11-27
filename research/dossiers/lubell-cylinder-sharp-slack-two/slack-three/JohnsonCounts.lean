import JohnsonClique
import Mathlib.Data.Finset.Powerset
import Lean.Elab.Tactic.Omega

namespace LubellSlackThree
open Finset

variable {α : Type*} [DecidableEq α]
variable (G F : Finset α) 

private theorem star_image (G X : Finset α) (F : Finset (Finset α)) (k : Nat)
    (hk : X.card+1=k) (hG : ∀ g∈F, g⊆G) (hX : ∀ g∈F, X⊆g)
    (hs : ∀ g∈F, g.card=k) :
    (F.image (fun g => g \ X)).card = F.card ∧
      F.image (fun g => g \ X) ⊆ (G \ X).powersetCard 1 := by
  classical
  constructor
  · apply card_image_of_injOn
    intro a ha b hb h
    have hu := congrArg (fun u : Finset α => X∪u) h
    exact (union_sdiff_of_subset (hX a ha)).symm.trans
      (hu.trans (union_sdiff_of_subset (hX b hb)))
  · intro v hv
    obtain ⟨g,hg,E⟩ := mem_image.mp hv
    subst v
    apply mem_powersetCard.mpr
    constructor
    · intro z hz
      obtain ⟨h1,h2⟩ := mem_sdiff.mp hz
      exact mem_sdiff.mpr ⟨hG g hg h1,h2⟩
    · rw [card_sdiff_of_subset (hX g hg), hs g hg]
      omega

theorem star_count (G X : Finset α) (F : Finset (Finset α)) (k : Nat)
    (hk : X.card+1=k) (hG : ∀ g∈F, g⊆G) (hX : ∀ g∈F, X⊆g)
    (hXG : X⊆G) (hs : ∀ g∈F, g.card=k) : F.card≤G.card-X.card := by
  obtain ⟨c,sub⟩ := star_image G X F k hk hG hX hs
  have bound := card_le_card sub
  rw [c, card_powersetCard, Nat.choose_one_right, card_sdiff_of_subset hXG] at bound
  exact bound

theorem full_star_mem (G X : Finset α) (F : Finset (Finset α)) (k : Nat)
    (hk : X.card+1=k) (hG : ∀ g∈F, g⊆G) (hX : ∀ g∈F, X⊆g)
    (hXG : X⊆G) (hs : ∀ g∈F, g.card=k) (hf : G.card-X.card≤F.card)
    (z : α) (hz : z∈G \ X) : X∪{z}∈F := by
  classical
  obtain ⟨c,sub⟩ := star_image G X F k hk hG hX hs
  have E : F.image (fun g => g \ X) = (G \ X).powersetCard 1 :=
    eq_of_subset_of_card_le sub (by
      rw [c, card_powersetCard, Nat.choose_one_right, card_sdiff_of_subset hXG]
      exact hf)
  have H : ({z} : Finset α)∈(G \ X).powersetCard 1 :=
    mem_powersetCard.mpr ⟨singleton_subset_iff.mpr hz,card_singleton _⟩
  rw [←E] at H
  obtain ⟨v,hv,h⟩ := mem_image.mp H
  have e : X∪{z}=v := by rw [←h,union_sdiff_of_subset (hX v hv)]
  rwa [e]

theorem top_count (V : Finset α) (F : Finset (Finset α)) (k : Nat)
    (hv : V.card=k+1) (hV : ∀ g∈F, g⊆V) (hs : ∀ g∈F, g.card=k) :
    F.card≤k+1 := by
  have sub : F⊆V.powersetCard k := fun g hg => mem_powersetCard.mpr ⟨hV g hg,hs g hg⟩
  have C := card_le_card sub
  rwa [card_powersetCard,hv,Nat.choose_succ_self_right] at C

/-- Both middle layers of a balanced slack-three problem cannot attain
    their individual Johnson size caps. -/
theorem balanced_middle_conflict (G X V : Finset α)
    (A B : Finset (Finset α)) (t : Nat)
    (ht : 1≤t) (hn : G.card=2*t+3) (hx : X.card=t) (hv : V.card=t+3)
    (hXG : X⊆G) (hAG : ∀ g∈A, g⊆G) (hBG : ∀ g∈B, g⊆G)
    (hAstar : ∀ g∈A, X⊆g) (hBtop : ∀ g∈B, g⊆V)
    (hAs : ∀ g∈A, g.card=t+1) (hBs : ∀ g∈B, g.card=t+2)
    (hAf : t+3≤A.card) (hBf : t+3≤B.card)
    (hAB : ∀ a∈A, ∀ b∈B, t≤(a∩b).card) : False := by
  classical
  have subB : B⊆V.powersetCard (t+2) :=
    fun g hg => mem_powersetCard.mpr ⟨hBtop g hg,hBs g hg⟩
  have EqB : B=V.powersetCard (t+2) := eq_of_subset_of_card_le subB (by
    rw [card_powersetCard,hv,show t+3=(t+2)+1 by omega,Nat.choose_succ_self_right]
    exact hBf)
  obtain ⟨z,hz⟩ := card_pos.mp (by omega : 0<X.card)
  have neV : V.Nonempty := card_pos.mp (by omega : 0<V.card)
  have H : ∃ b∈B, z∉b := by
    by_cases hzV : z∈V
    · refine ⟨V.erase z,?_,notMem_erase _ _⟩
      rw [EqB]
      exact mem_powersetCard.mpr ⟨erase_subset _ _,by rw [card_erase_of_mem hzV,hv]; omega⟩
    · obtain ⟨v,hvV⟩ := neV
      refine ⟨V.erase v,?_,fun zz => hzV (erase_subset _ _ zz)⟩
      rw [EqB]
      exact mem_powersetCard.mpr ⟨erase_subset _ _,by rw [card_erase_of_mem hvV,hv]; omega⟩
  obtain ⟨b,hb,hzb⟩ := H
  have rc := card_union_le (s:=X) (t:=b)
  have bs := hBs b hb
  obtain ⟨e,he⟩ := sdiff_nonempty_of_card_lt_card (s:=X∪b) (t:=G) (by omega)
  obtain ⟨heG,hen⟩ := mem_sdiff.mp he
  have heX : e∉X := fun hh => hen (mem_union.mpr (Or.inl hh))
  have heb : e∉b := fun hh => hen (mem_union.mpr (Or.inr hh))
  have sf : X∪{e}∈A := full_star_mem G X A (t+1) (by omega) hAG hAstar hXG hAs
    (by omega) e (mem_sdiff.mpr ⟨heG,heX⟩)
  have C : (X∪{e})∩b⊆X.erase z := by
    intro i hi
    obtain ⟨h1,h2⟩ := mem_inter.mp hi
    apply mem_erase.mpr
    refine ⟨fun eq => hzb (eq ▸ h2),?_⟩
    rcases mem_union.mp h1 with l|r
    · exact l
    · have Eq : i=e := mem_singleton.mp r
      exact False.elim (heb (Eq ▸ h2))
  have Cn := card_le_card C
  have Bn := hAB _ sf b hb
  rw [card_erase_of_mem hz,hx] at Cn
  omega

end LubellSlackThree
#print axioms LubellSlackThree.balanced_middle_conflict
