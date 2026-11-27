import GeometricChargeMoment
import GeometricGraphEdit
import Mathlib.Data.Finset.Prod

namespace RobustFolkman
open Finset
variable {V : Type*} [DecidableEq V]

theorem pair_eq_pair_cases {a b c d : V} (ab : a ≠ b)
    (h : ({a,b} : Finset V) = {c,d}) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have ha : a=c ∨ a=d := by
    have ma : a∈({c,d} : Finset V) := h ▸ (by simp)
    simpa using ma
  have hb : b=c ∨ b=d := by
    have mb : b∈({c,d} : Finset V) := h ▸ (by simp)
    simpa using mb
  grind

theorem triangle_third {T : Finset (Finset V)} {a b : V}
    (ab : a ≠ b) (h : triangleShape T) (e : ({a,b}:Finset V)∈T) :
    ∃ w, w≠a ∧ w≠b ∧ T=triangleEdges a b w := by
  rcases h with ⟨x,y,z,xy,xz,yz,rfl⟩
  simp only [triangleEdges, mem_insert, mem_singleton] at e
  rcases e with hxy | hxz | hyz
  · rcases pair_eq_pair_cases ab hxy with ⟨ha,hb⟩|⟨ha,hb⟩
    · subst a; subst b
      exact ⟨z,xz.symm,yz.symm,rfl⟩
    · subst a; subst b
      refine ⟨z,yz.symm,xz.symm,?_⟩
      unfold triangleEdges
      rw [pair_comm y x]
      ext t
      simp only [mem_insert,mem_singleton]
      tauto
  · rcases pair_eq_pair_cases ab hxz with ⟨ha,hb⟩|⟨ha,hb⟩
    · subst a; subst b
      refine ⟨y,xy.symm,yz,?_⟩
      unfold triangleEdges
      rw [pair_comm z y]
      ext t
      simp only [mem_insert,mem_singleton]
      tauto
    · subst a; subst b
      refine ⟨y,yz,xy.symm,?_⟩
      unfold triangleEdges
      rw [pair_comm z x, pair_comm z y]
      ext t
      simp only [mem_insert,mem_singleton]
      tauto
  · rcases pair_eq_pair_cases ab hyz with ⟨ha,hb⟩|⟨ha,hb⟩
    · subst a; subst b
      refine ⟨x,xy,xz,?_⟩
      unfold triangleEdges
      rw [pair_comm y x, pair_comm z x]
      ext t
      simp only [mem_insert,mem_singleton]
      tauto
    · subst a; subst b
      refine ⟨x,xz,xy,?_⟩
      unfold triangleEdges
      rw [pair_comm z y, pair_comm z x, pair_comm y x]
      ext t
      simp only [mem_insert,mem_singleton]
      tauto

structure FiveLabel (H : EdgeGraph V) where
  u : V
  v : V
  x : V
  y : V
  z : V
  uv : u≠v
  xy : x≠y
  zx : z≠x
  zy : z≠y
  ux : u≠x
  uy : u≠y
  vx : v≠x
  vy : v≠y
  uz : u≠z
  vz : v≠z
  edges_eq : H=forbiddenEdges u v x y z

theorem fiveLabel_of_copy (G H : EdgeGraph V) (h : H∈forbiddenCopies G) :
    Nonempty (FiveLabel H) := by
  rcases (mem_copies.mp h).2 with ⟨u,v,x,y,z,uv,xy,zx,zy,ux,uy,vx,vy,uz,vz,eq⟩
  exact ⟨⟨u,v,x,y,z,uv,xy,zx,zy,ux,uy,vx,vy,uz,vz,eq⟩⟩

noncomputable def marked (H : EdgeGraph V) : Finset V := by
  classical
  exact if h : Nonempty (FiveLabel H) then
    {(Classical.choice h).u,(Classical.choice h).z} else ∅

theorem marked_hit (G H : EdgeGraph V) (h : H∈forbiddenCopies G) :
    marked H∈H := by
  classical
  have L := fiveLabel_of_copy G H h
  unfold marked
  rw [dite_eq_left L]
  have eq := (Classical.choice L).edges_eq
  exact Eq.mpr (congrArg (fun (S : EdgeGraph V) =>
    ({(Classical.choice L).u,(Classical.choice L).z} : Finset V)∈S) eq) (by simp [forbiddenEdges])

theorem triangle_marked_classification (G H T : EdgeGraph V)
    (h : H∈forbiddenCopies G) (t : T∈triangles G) (e : marked H∈T) :
    let L := Classical.choice (fiveLabel_of_copy G H h)
    ∃ w, w≠L.u ∧ w≠L.z ∧ T=triangleEdges L.u L.z w ∧
      (w=L.v ∨ w=L.x ∨ w=L.y ∨ w∉({L.u,L.v,L.x,L.y,L.z}:Finset V)) := by
  classical
  let hL := fiveLabel_of_copy G H h
  let L := Classical.choice hL
  change ∃ w, w ≠ L.u ∧ w ≠ L.z ∧ T=triangleEdges L.u L.z w ∧ _
  have E : ({L.u,L.z} : Finset V)∈T := by
    unfold marked at e
    rwa [dite_eq_left hL] at e
  obtain ⟨w,hu,hz,eq⟩ := triangle_third L.uz (mem_triangles.mp t).2 E
  refine ⟨w,hu,hz,eq,?_⟩
  simp only [mem_insert,mem_singleton]
  tauto


variable [Fintype V]

theorem charge_marked_row (G H : EdgeGraph V) (h : H∈forbiddenCopies G) :
    let L := Classical.choice (fiveLabel_of_copy G H h)
    ((triangles G).filter (fun T => marked H∈T)).card ≤
      3+((univ : Finset V).filter (fun w =>
        w∉({L.u,L.v,L.x,L.y,L.z}:Finset V) ∧ {L.u,w}∈G ∧ {L.z,w}∈G)).card := by
  classical
  let L := Classical.choice (fiveLabel_of_copy G H h)
  let inside : Finset V := {L.v,L.x,L.y}
  let outside : Finset V := univ.filter (fun w =>
    w∉({L.u,L.v,L.x,L.y,L.z}:Finset V) ∧ {L.u,w}∈G ∧ {L.z,w}∈G)
  change ((triangles G).filter (fun T => marked H∈T)).card ≤ 3+outside.card
  have dominate : (triangles G).filter (fun T => marked H∈T) ⊆
      (inside∪outside).image (triangleEdges L.u L.z) := by
    intro T ht
    obtain ⟨ht,hm⟩ := mem_filter.mp ht
    obtain ⟨w,_,_,eq,whereW⟩ := triangle_marked_classification G H T h ht hm
    change T=triangleEdges L.u L.z w at eq
    change w=L.v ∨ w=L.x ∨ w=L.y ∨ w∉({L.u,L.v,L.x,L.y,L.z}:Finset V) at whereW
    refine mem_image.mpr ⟨w,mem_union.mpr ?_,eq.symm⟩
    rcases whereW with hw|hw|hw|hw
    · left; simp [inside,hw]
    · left; simp [inside,hw]
    · left; simp [inside,hw]
    · right
      have sub := (mem_triangles.mp ht).1
      rw [eq] at sub
      exact mem_filter.mpr ⟨mem_univ _,hw,sub (by simp [triangleEdges]),
        sub (by simp [triangleEdges])⟩
  have ic : inside.card≤3 := by
    calc
      inside.card ≤ ({L.x,L.y}:Finset V).card+1 := card_insert_le _ _
      _ ≤ (({L.y}:Finset V).card+1)+1 := Nat.add_le_add_right (card_insert_le _ _) _
      _ = 3 := by simp
  exact (card_le_card dominate).trans (card_image_le.trans
    (card_union_le _ _ |>.trans (Nat.add_le_add_right ic _)))

#print axioms triangle_marked_classification
#print axioms charge_marked_row
end RobustFolkman
