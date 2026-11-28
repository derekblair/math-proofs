import N62SaturatedProfile

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V→V→Prop) [DecidableRel G]

def support (S : Finset V) (z : V) := S.filter (G z)

theorem support_single {S X : Finset V} (F : SaturationFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (u : V) (hu : u∈S) :
    support G S (F.leaf u) = {u} := by
  obtain ⟨_,hl,hs⟩ := F.leafData u hu
  ext x
  simp only [support,Finset.mem_filter]
  constructor
  · exact fun h => hs x h.1 h.2
  · rintro hx
    have h : x=u := Finset.mem_singleton.mp hx
    subst x
    exact ⟨hu,sym hl.1⟩

theorem support_pair {S : Finset V} (sym : ∀ {a b}, G a b → G b a)
    {u v z : V} (hu : u∈S) (hv : v∈S)
    (lu : Lone G u z) (lv : Lone G v z) (s : supported G S {u,v} z) :
    support G S z={u,v} := by
  ext x
  simp only [support,Finset.mem_filter]
  constructor
  · exact fun h => s x h.1 h.2
  · simp only [Finset.mem_insert,Finset.mem_singleton]
    rintro (rfl|rfl)
    · exact ⟨hu,sym lu.1⟩
    · exact ⟨hv,sym lv.1⟩

theorem double_support_card {S X : Finset V} (F : SaturationFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (z : V) (hz : z∈F.doubles) :
    (support G S z).card=2 := by
  obtain ⟨_,u,hu,v,hv,ne,lu,lv,hpair⟩ := F.doubleData z hz
  rw [support_pair G sym hu hv lu lv hpair]
  simp [Finset.card_insert_of_notMem,ne]

theorem leaf_not_double {S X : Finset V} (F : SaturationFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (u : V) (hu : u∈S) :
    F.leaf u ∉ F.doubles := by
  intro hd
  have e := double_support_card G F sym _ hd
  simp [support_single G F sym u hu] at e

theorem leaf_injOn {S X : Finset V} (F : SaturationFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) :
    Set.InjOn F.leaf (S : Set V) := by
  intro u hu v hv he
  have e := congrArg (support G S) he
  rw [support_single G F sym u hu,support_single G F sym v hv] at e
  exact Finset.singleton_inj.mp e

/-- Two distinct double columns cannot have the same owner pair when
the owners are marked: exchange with one marked singleton leaf. -/
theorem support_injOn_doubles {S X : Finset V} (F : SaturationFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (dXS : Disjoint X S) (s12 : S.card=12)
    (hS : Free (Forbidden G) (S : Set V))
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12) :
    Set.InjOn (support G S) (F.doubles : Set V) := by
  classical
  intro x hx y hy eq
  by_contra hxy
  obtain ⟨xX,u,hu,v,hv,uv,lu,lv,su⟩ := F.doubleData x hx
  obtain ⟨yX,a,ha,b,hb,ab,la,lb,sa⟩ := F.doubleData y hy
  have eqS : support G S y={u,v} := eq.symm.trans (support_pair G sym hu hv lu lv su)
  have uy : Lone G u y := by
    have hy' : u∈support G S y := by simp [eqS]
    have he : u=a ∨ u=b := by
      rw [support_pair G sym ha hb la lb sa] at hy'
      simpa using hy'
    rcases he with rfl|rfl
    · exact la
    · exact lb
  let R := S\({u,v}:Finset V)
  let Y : Finset V := {x,y,F.leaf u}
  have nleafx : F.leaf u≠x := fun h => leaf_not_double G F sym u hu (h ▸ hx)
  have nleafy : F.leaf u≠y := fun h => leaf_not_double G F sym u hu (h ▸ hy)
  have rc : R.card=10 := by
    have r := Finset.card_sdiff_add_card_eq_card
      (show ({u,v}:Finset V)⊆S by simp [Finset.insert_subset_iff,hu,hv])
    change R.card + ({u,v}:Finset V).card = S.card at r
    simp [Finset.card_insert_of_notMem,uv,s12] at r
    omega
  have y3 : Y.card=3 := by
    simp [Y,Finset.card_insert_of_notMem,hxy,Ne.symm nleafx,Ne.symm nleafy]
  have rS : R⊆S := Finset.sdiff_subset
  have yX : Y⊆X := by
    intro z hz
    simp only [Y,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact xX
    · exact yX
    · exact (F.leafData u hu).1
  have rY : Disjoint R Y := Finset.disjoint_left.mpr
    (fun z hzR hzY => Finset.disjoint_left.mp dXS (yX hzY) (rS hzR))
  have yf (z : V) (hz : z ∈ Y) : Lone G u z := by
    simp only [Y,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact lu
    · exact uy
    · exact (F.leafData u hu).2.1
  have cross (z : V) (hz : z∈Y) (r : V) (hr : r∈R) : ¬G z r := by
    intro h
    have hm : r∈support G S z := Finset.mem_filter.mpr ⟨rS hr,h⟩
    have hh : r∉({u,v}:Finset V) := (Finset.mem_sdiff.mp hr).2
    apply hh
    simp only [Y,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · rwa [support_pair G sym hu hv lu lv su] at hm
    · rwa [eqS] at hm
    · rw [support_single G F sym u hu] at hm
      exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hm))
  have freeR : Free (Forbidden G) (R : Set V) := fun T hT h => hS T hT (fun v hv => rS (h hv))
  have free := free_adjoin_independent G sym irr R Y freeR
    (fun a ha b hb => lone_neighbors_nonadjacent G sym (yf a ha) (yf b hb).1) cross
  have cap := upper _ free
  rw [Finset.card_union_of_disjoint rY.symm,rc,y3] at cap
  omega

#print axioms support_injOn_doubles
end Erdos151N62
