import RobustFolkman
import ParagliderCayley
import Mathlib.Data.Finset.Powerset

namespace RobustFolkman
open Finset
variable {V : Type*} [DecidableEq V]

abbrev EdgeGraph (V : Type*) := Finset (Finset V)

def hasEdge (G : EdgeGraph V) (x y : V) : Prop := x≠y ∧ ({x,y}:Finset V)∈G

def triangleEdges (x y z : V) : Finset (Finset V) := {{x,y},{x,z},{y,z}}

def forbiddenEdges (u v x y z : V) : Finset (Finset V) :=
  {{x,y},{u,x},{u,y},{v,x},{v,y},{u,z},{v,z}}

def triangleShape (T : Finset (Finset V)) : Prop :=
  ∃ x y z, x≠y ∧ x≠z ∧ y≠z ∧ T=triangleEdges x y z

def forbiddenShape (T : Finset (Finset V)) : Prop :=
  ∃ u v x y z, u≠v ∧ x≠y ∧ z≠x ∧ z≠y ∧
    u≠x ∧ u≠y ∧ v≠x ∧ v≠y ∧ u≠z ∧ v≠z ∧ T=forbiddenEdges u v x y z

noncomputable def triangles (G : EdgeGraph V) : Finset (Finset (Finset V)) := by
  classical
  exact G.powerset.filter triangleShape

noncomputable def forbiddenCopies (G : EdgeGraph V) : Finset (Finset (Finset V)) := by
  classical
  exact G.powerset.filter forbiddenShape

theorem mem_triangles {G : EdgeGraph V} {T : Finset (Finset V)} :
    T∈triangles G ↔ T⊆G ∧ triangleShape T := by
  classical
  simp [triangles]

theorem mem_copies {G : EdgeGraph V} {H : Finset (Finset V)} :
    H∈forbiddenCopies G ↔ H⊆G ∧ forbiddenShape H := by
  classical
  simp [forbiddenCopies]

theorem contains_iff_nonempty (G : EdgeGraph V) :
    Paraglider.Contains (hasEdge G) ↔ (forbiddenCopies G).Nonempty := by
  classical
  constructor
  · rintro ⟨u,v,x,y,z,uv,xy,zx,zy,exy,ux,uy,vx,vy,uz,vz⟩
    refine ⟨forbiddenEdges u v x y z,mem_copies.mpr ⟨?_,?_⟩⟩
    · intro e he
      simp only [forbiddenEdges,mem_insert,mem_singleton] at he
      rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      exacts [exy.2,ux.2,uy.2,vx.2,vy.2,uz.2,vz.2]
    · exact ⟨u,v,x,y,z,uv,xy,zx,zy,ux.1,uy.1,vx.1,vy.1,uz.1,vz.1,rfl⟩
  · rintro ⟨H,hH⟩
    obtain ⟨sub,u,v,x,y,z,uv,xy,zx,zy,ux,uy,vx,vy,uz,vz,rfl⟩ := mem_copies.mp hH
    exact ⟨u,v,x,y,z,uv,xy,zx,zy,⟨xy,sub (by simp [forbiddenEdges])⟩,
      ⟨ux,sub (by simp [forbiddenEdges])⟩,⟨uy,sub (by simp [forbiddenEdges])⟩,
      ⟨vx,sub (by simp [forbiddenEdges])⟩,⟨vy,sub (by simp [forbiddenEdges])⟩,
      ⟨uz,sub (by simp [forbiddenEdges])⟩,⟨vz,sub (by simp [forbiddenEdges])⟩⟩

theorem triangles_after_delete (G D : EdgeGraph V) :
    triangles (G\D)=alive (triangles G) D := by
  classical
  ext T
  rw [mem_triangles,alive,mem_filter,mem_triangles]
  constructor
  · rintro ⟨sub,s⟩
    exact ⟨⟨fun e et => (mem_sdiff.mp (sub et)).1,s⟩,
      disjoint_left.mpr fun e ed et => (mem_sdiff.mp (sub et)).2 ed⟩
  · rintro ⟨⟨sub,s⟩,disj⟩
    exact ⟨fun e et => mem_sdiff.mpr ⟨sub et,fun ed => disjoint_left.mp disj ed et⟩,s⟩

/-- Exact non-induced forbidden graph and edge-colour statement. The
probabilistic part is only needed to supply the single finite charge bound. -/
theorem avoid_subdivided_k4 (G : EdgeGraph V) (pick : EdgeGraph V → Finset V)
    (hit : ∀ H∈forbiddenCopies G, pick H∈H)
    (robust : ∀ c : Finset V → Bool,
      charge (triangles G) (forbiddenCopies G) pick < (mono (triangles G) c).card) :
    ∃ G' : EdgeGraph V, G'⊆G ∧ ¬Paraglider.Contains (hasEdge G') ∧
      ∀ c : Finset V → Bool, ∃ t∈triangles G', Monochrom c t := by
  classical
  let D := cutEdges (forbiddenCopies G) pick
  obtain ⟨avoids,retains⟩ := robust_avoidance G (triangles G) (forbiddenCopies G) pick hit robust
  refine ⟨G\D,sdiff_subset,?_,?_⟩
  · intro contains
    obtain ⟨H,hH⟩ := (contains_iff_nonempty _).mp contains
    have K := mem_copies.mp hH
    have present : H∈forbiddenCopies G :=
      mem_copies.mpr ⟨K.1.trans sdiff_subset,K.2⟩
    exact avoids H present K.1
  · rw [triangles_after_delete]
    exact retains

#print axioms contains_iff_nonempty
#print axioms avoid_subdivided_k4
end RobustFolkman
