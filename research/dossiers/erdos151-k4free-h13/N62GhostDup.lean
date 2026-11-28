import N62DoubleTriangle

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13 Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

theorem duplicate_ghost_no_common (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    {g h u x y : V} (xd : x∈F.doubles) (yd : y∈F.doubles) (xy : x≠y)
    (xe : support G S x={g,h}) (ye : support G S y={g,h})
    (gu : DoubleRel G F g u) (hu : DoubleRel G F h u) : False := by
  have hgu := drel_owners G F gu
  have hhu := drel_owners G F hu
  have gn := drel_ne G F gu
  have hn := drel_ne G F hu
  have gh := drel_ne G F (show DoubleRel G F g h from ⟨x,xd,xe⟩)
  obtain ⟨a,ad,ae⟩ := gu
  obtain ⟨b,bd,be⟩ := hu
  let W : Finset V := {g,h,u}
  let Z : Finset V := {x,y,a,b}
  have ne (p q v : V) (hp : v∈support G S p) (hq : v∉support G S q) : p≠q :=
    fun e=>hq (e ▸ hp)
  have xa : x≠a := ne x a h (by simp [xe]) (by simp [ae,gh.symm,hn])
  have ya : y≠a := ne y a h (by simp [ye]) (by simp [ae,gh.symm,hn])
  have xb : x≠b := ne x b g (by simp [xe]) (by simp [be,gh,gn])
  have yb : y≠b := ne y b g (by simp [ye]) (by simp [be,gh,gn])
  have ab : a≠b := ne a b g (by simp [ae]) (by simp [be,gh,gn])
  have wc : W.card=3 := by simp [W,card_insert_of_notMem,gh,gn,hn]
  have ws : W⊆S := by simp [W,insert_subset_iff,hgu.1,hgu.2,hhu.1]
  have zc : Z.card=4 := by simp [Z,card_insert_of_notMem,xy,xa,xb,ya,yb,ab]
  have zs : Z⊆F.doubles := by simp [Z,insert_subset_iff,xd,yd,ad,bd]
  have sub : ∀ z∈Z, support G S z⊆W := by
    intro z hz
    simp only [Z,mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl|rfl
    · simp [xe,W,insert_subset_iff]
    · simp [ye,W,insert_subset_iff]
    · simp [ae,W,insert_subset_iff]
    · simp [be,W,insert_subset_iff]
  have cap := three_owner_double_cap G F sym irr sc sf out upper W Z (by omega) ws zs sub
  omega

#print axioms duplicate_ghost_no_common
end Erdos151N62
