import N62DirectedSplit

namespace Erdos151N62
open Erdős151.Upper Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : V→V→Prop) [DecidableRel E]

def missGhost (g h x : V) : Nat := (if E x g then 0 else 1)+(if E x h then 0 else 1)

theorem marked_two_ghost_cut
    (sym : ∀ {a b}, E a b → E b a)
    (S T : Finset V) (ts : T⊆S) (g h : V)
    (gs : g∈S) (hs : h∈S) (gn : g∉T) (hn : h∉T)
    (cap : ∀ x∈T,row E S x≤3)
    (incomp : ∀ {x y}, x∈T → y∈T → E x y →
      ¬(E x g ∧ E y g) ∧ ¬(E x h ∧ E y h)) :
    let f := ∑ x∈T,missGhost E g h x
    let z := (T.filter (fun x => missGhost E g h x=2)).card
    (∑ x∈T,row E T x)≤2*(f+z) ∧ 2*z≤f := by
  classical
  let Z := T.filter (fun x => missGhost E g h x=2)
  let W := T.filter (fun x => missGhost E g h x=1)
  have zt : Z⊆T := filter_subset _ _
  let f := ∑ x∈T,missGhost E g h x
  have exactF : f=2*Z.card+W.card := by
    let z (x : V) := if missGhost E g h x=2 then 2 else 0
    let w (x : V) := if missGhost E g h x=1 then 1 else 0
    have zz : ∑ x∈T,z x=2*Z.card := by
      unfold z Z; rw [←sum_filter]; simp [Nat.mul_comm]
    have ww : ∑ x∈T,w x=W.card := by
      unfold w W; rw [←sum_filter]; simp
    have e : f=∑ x∈T,(z x+w x) := by
      apply sum_congr rfl
      intro x hx
      unfold z w missGhost
      by_cases hd : E x g <;> by_cases he : E x h <;> simp [hd,he]
    rwa [sum_add_distrib,zz,ww] at e
  have cZ (x : V) (hx : x∈Z) : row E T x≤3 := by
    have h := card_le_card (filter_subset_filter _ ts : T.filter (E x)⊆S.filter (E x))
    have c := cap x (zt hx)
    exact h.trans c
  have cW (x : V) (hx : x∈T\Z) : row E (T\Z) x≤2 := by
    have hx' := mem_sdiff.mp hx
    have hm : E x g ∨ E x h := by
      by_contra! no
      apply hx'.2
      exact mem_filter.mpr ⟨hx'.1,by simp [missGhost,no.1,no.2]⟩
    obtain ⟨p,ps,pn,px⟩ : ∃ p∈S,p∉T ∧ E x p := hm.elim
      (fun e => ⟨g,gs,gn,e⟩) (fun e=>⟨h,hs,hn,e⟩)
    have sub : insert p ((T\Z).filter (E x))⊆S.filter (E x) := by
      intro y hy
      rcases mem_insert.mp hy with rfl|hy
      · exact mem_filter.mpr ⟨ps,px⟩
      · exact mem_filter.mpr
          ⟨ts (mem_sdiff.mp (mem_filter.mp hy).1).1,(mem_filter.mp hy).2⟩
    have r := card_le_card sub
    rw [card_insert_of_notMem (fun h => pn (mem_sdiff.mp (mem_filter.mp h).1).1)] at r
    have d := cap x hx'.1
    change row E (T\Z) x+1≤row E S x at r
    omega
  have ws : W⊆T\Z := by
    intro x hx
    obtain ⟨tx,w⟩ := mem_filter.mp hx
    exact mem_sdiff.mpr ⟨tx,fun hz=>by
      have hh : missGhost E g h x=2 := (mem_filter.mp hz).2
      omega⟩
  have zz (x : V) (hx : x∈(T\Z)\W) : row E (T\Z) x=0 := by
    have hx' := mem_sdiff.mp (mem_sdiff.mp hx).1
    have xf : E x g ∧ E x h := by
      have nz : missGhost E g h x≠2 := fun h => hx'.2 (mem_filter.mpr ⟨hx'.1,h⟩)
      have nw : missGhost E g h x≠1 := fun h => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨hx'.1,h⟩)
      unfold missGhost at nz nw
      by_cases hd : E x g <;> by_cases he : E x h <;> simp_all
    apply card_eq_zero.mpr
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨y,hy⟩
    obtain ⟨yt,edge⟩ := mem_filter.mp hy
    have yc := incomp hx'.1 (mem_sdiff.mp yt).1 edge
    have ng : ¬E y g := fun he => yc.1 ⟨xf.1,he⟩
    have nh : ¬E y h := fun he => yc.2 ⟨xf.2,he⟩
    exact (mem_sdiff.mp yt).2 (mem_filter.mpr
      ⟨(mem_sdiff.mp yt).1,by simp [missGhost,ng,nh]⟩)
  have bd := split_directed_at E sym T Z zt cZ cW W ws zz
  change (∑ x∈T,row E T x)≤2*(f+Z.card) ∧ 2*Z.card≤f
  omega

#print axioms marked_two_ghost_cut
end Erdos151N62
