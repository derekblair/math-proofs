import N62SimpleOwner
import N62TripleOwnerCap

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13 Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

private theorem support_wrap {S P : Finset V} {z : V} (h : support G S z=P) :
    supported G S P z := fun y hy hG => h ▸ mem_filter.mpr ⟨hy,hG⟩

theorem owner_double_triangle_leaf (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    {r u v z : V} (rm : r∈F.marks)
    (ru : DoubleRel G F r u) (rv : DoubleRel G F r v)
    (zd : z∈F.doubles) (zsup : support G S z={u,v}) :
    Lone G (F.leaf r) z := by
  have rU := drel_ne G F ru
  have rV := drel_ne G F rv
  have uV := drel_ne G F (show DoubleRel G F u v from ⟨z,zd,zsup⟩)
  have us := (drel_owners G F ru).2
  have vs := (drel_owners G F rv).2
  obtain ⟨x,xd,xsup⟩ := ru
  obtain ⟨y,yd,ysup⟩ := rv
  have out' (x : V) (hx : x∈X) : x∉S := Finset.disjoint_left.mp out hx
  have pairs (a b k : V) (ha : k∈support G S a) (hb : k∉support G S b) : a≠b :=
    fun e => hb (e ▸ ha)
  have xy : x≠y := pairs x y u (by simp [xsup]) (by simp [ysup,rU.symm,uV])
  have zx : z≠x := pairs z x v (by simp [zsup]) (by simp [xsup,rV.symm,uV.symm])
  have zy : z≠y := pairs z y u (by simp [zsup]) (by simp [ysup,rU.symm,uV])
  have one := near_single_support G F sym rm
  have le (a : V) (ha : a∈F.doubles) : F.leaf r≠a := by
    intro e
    have ct := support_two G F ha
    rw [←e,one,card_singleton] at ct
    omega
  have ln {a b : V} (ha : a∈F.doubles) (hb : b∈support G S a) : Lone G b a :=
    near_double_lone_of_support G F ha hb
  exact owner_triangle_forces_lone G sym irr S r u v x y z (F.leaf r)
    (F.markSub rm) us vs rU rV uV (out' _ (F.dblData x xd).1) (out' _ (F.dblData y yd).1)
    (out' _ (F.dblData z zd).1) (out' _ (F.leafData r rm).1)
    xy (le x xd) (le y yd) zx zy (le z zd)
    (ln xd (by simp [xsup])) (ln xd (by simp [xsup]))
    (ln yd (by simp [ysup])) (ln yd (by simp [ysup]))
    (ln zd (by simp [zsup])) (ln zd (by simp [zsup]))
    (F.leafData r rm).2.1
    (support_wrap G xsup) (support_wrap G ysup) (support_wrap G zsup) (support_wrap G one)
    sc sf (fun T ht hf => by have := upper T hf; omega)

theorem ghost_pair_common_independent (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    {g h u v : V} (um : u∈F.marks) (vm : v∈F.marks)
    (gh : DoubleRel G F g h)
    (ug : DoubleRel G F u g) (uh : DoubleRel G F u h)
    (vg : DoubleRel G F v g) (vh : DoubleRel G F v h) : ¬DoubleRel G F u v := by
  intro uv
  obtain ⟨z,zd,zsup⟩ := gh
  have lu := owner_double_triangle_leaf G F sym irr sc sf out upper um ug uh zd zsup
  have lv := owner_double_triangle_leaf G F sym irr sc sf out upper vm vg vh zd zsup
  have luv := marked_drel_forces_leaf G F sym irr sc sf out upper um vm uv
  exact luv.2 z ⟨lu.1,lv.1⟩

#print axioms owner_double_triangle_leaf
#print axioms ghost_pair_common_independent
end Erdos151N62
