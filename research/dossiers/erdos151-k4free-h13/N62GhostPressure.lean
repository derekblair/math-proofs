import N62DoubleTriangle
import N62DoubleRow

namespace Erdos151N62
open Erdős151 Erdős151.Upper Erdos151H12 Erdos151H13 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]
variable {S X : Finset V}

theorem near_marked_ghost_book_pressure (F : NearOwnerFrame G S X)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (T : Finset V) (g h : V) (gn : g∉T) (hn : h∉T)
    (tm : T⊆F.marks) (gm : g∈F.marks) (ghD : DoubleRel G F g h) :
    let Lg := weightedSet T (DoubleRel G F g)
    let Lh := weightedSet T (DoubleRel G F h)
    1+Lg.card+(Lg∩Lh).card ≤ (neighbors G (F.leaf g)).card := by
  classical
  let E := DoubleRel G F
  let Lg := weightedSet T (E g)
  let Lh := weightedSet T (E h)
  let N := insert h Lg
  have gmS := F.markSub gm
  have gh := drel_ne G F ghD
  have dMem (u : V) (hu : u∈N) : E g u := by
    rcases mem_insert.mp hu with rfl|h
    · exact ghD
    · exact (mem_filter.mp h).2
  have nSub : N⊆S.erase g := by
    intro u hu
    have edge := dMem u hu
    exact mem_erase.mpr ⟨(drel_ne G F edge).symm,(drel_owners G F edge).2⟩
  have paired (u : V) (hu : u∈N) : ∃ z∈X, Lone G g z ∧ Lone G u z ∧ support G S z={g,u} := by
    obtain ⟨z,zd,e⟩ := dMem u hu
    exact ⟨z,(F.dblData z zd).1,near_double_lone_of_support G F zd (by simp [e]),
      near_double_lone_of_support G F zd (by simp [e]),e⟩
  let K := Lg∩Lh
  have ex (u : V) (hu : u∈K) : ∃ z∈F.doubles, support G S z={h,u} :=
    (mem_filter.mp (mem_inter.mp hu).2).2
  let pick (u : V) := if hu : u∈K then Classical.choose (ex u hu) else h
  have p (u : V) (hu : u∈K) : pick u∈F.doubles ∧ support G S (pick u)={h,u} := by
    unfold pick
    rw [dif_pos hu]
    exact Classical.choose_spec (ex u hu)
  have hp : Set.InjOn pick (K:Set V) := by
    intro u uu v vv e
    have eq := congrArg (support G S) e
    rw [(p u uu).2,(p v vv).2] at eq
    have up : u∈({h,v}:Finset V) := eq ▸ (by simp : u∈({h,u}:Finset V))
    simp only [mem_insert,mem_singleton] at up
    have ut : u∈T := (mem_filter.mp (mem_inter.mp uu).1).1
    exact up.resolve_left (fun e => hn (e ▸ ut))
  let R := K.image pick
  have rc : R.card=K.card := card_image_of_injOn hp
  have ep (z : V) (hz : z∈R) : ∃ u∈N, ∃ v∈N, u≠v ∧
      Lone G u z ∧ Lone G v z ∧ support G S z={u,v} := by
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
    have h := p u hu
    exact ⟨_,mem_insert_self _ _,u,mem_insert_of_mem (mem_inter.mp hu).1,
      drel_ne G F (show DoubleRel G F _ u from ⟨pick u,h.1,h.2⟩),
      near_double_lone_of_support G F h.1 (by simp [h.2]),
      near_double_lone_of_support G F h.1 (by simp [h.2]),h.2⟩
  have rx : R⊆X := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
    exact (F.dblData _ (p u hu).1).1
  have lg : Lg⊆N∩F.marks := fun x hx => mem_inter.mpr ⟨mem_insert_of_mem hx,tm (mem_filter.mp hx).1⟩
  have P := marked_leaf_pressure G sym irr S X F.marks N R g F.leaf out sc sf upper
    gmS gm F.markSub nSub F.leafData paired ep rx
  have h := card_le_card lg
  change 1+Lg.card+K.card≤(neighbors G (F.leaf g)).card
  omega

#print axioms near_marked_ghost_book_pressure
end Erdos151N62
