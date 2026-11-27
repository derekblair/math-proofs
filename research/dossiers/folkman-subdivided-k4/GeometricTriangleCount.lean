import GeometricGraphEdit
import GeometricTriangleOverlap
import GeometricChargeGraph

namespace RobustFolkman
open Finset Moment
variable {V : Type*} [DecidableEq V]

theorem powerset_two_triple {x y z : V} (xy : x≠y) (xz : x≠z) (yz : y≠z) :
    ({x,y,z}:Finset V).powersetCard 2=triangleEdges x y z := by
  ext e
  rw [Finset.mem_powersetCard]
  constructor
  · rintro ⟨sub,hc⟩
    obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp hc
    have ha := sub (show a∈({a,b}:Finset V) by simp)
    have hb := sub (show b∈({a,b}:Finset V) by simp)
    simp only [mem_insert,mem_singleton] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
      first | contradiction | simp [triangleEdges,Finset.pair_comm]
  · intro h
    simp only [triangleEdges,mem_insert,mem_singleton] at h
    rcases h with rfl|rfl|rfl
    · exact ⟨by simp [Finset.subset_iff], Finset.card_eq_two.mpr ⟨x,y,xy,rfl⟩⟩
    · exact ⟨by simp [Finset.subset_iff], Finset.card_eq_two.mpr ⟨x,z,xz,rfl⟩⟩
    · exact ⟨by simp [Finset.subset_iff], Finset.card_eq_two.mpr ⟨y,z,yz,rfl⟩⟩

theorem triple_vertices (s : Finset V) (sc : s.card=3) :
    (s.powersetCard 2).biUnion id = s := by
  obtain ⟨x,y,z,xy,xz,yz,rfl⟩ := Finset.card_eq_three.mp sc
  rw [powerset_two_triple xy xz yz]
  ext w
  simp [triangleEdges]

variable [Fintype V]

noncomputable def tripleTriangles (G : EdgeGraph V) : Finset (Finset V) := by
  classical
  exact ((univ : Finset V).powersetCard 3).filter (fun s => s.powersetCard 2 ⊆ G)

theorem triangles_image (G : EdgeGraph V) :
    triangles G=(tripleTriangles G).image (fun s => s.powersetCard 2) := by
  classical
  ext T
  rw [mem_triangles,mem_image]
  constructor
  · rintro ⟨sub,x,y,z,xy,xz,yz,rfl⟩
    refine ⟨{x,y,z},mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,?_⟩,?_⟩,
      powerset_two_triple xy xz yz⟩
    · exact Finset.card_eq_three.mpr ⟨x,y,z,xy,xz,yz,rfl⟩
    · rwa [powerset_two_triple xy xz yz]
  · rintro ⟨s,hs,rfl⟩
    obtain ⟨h₁,h₂⟩ := mem_filter.mp (show s∈_ from hs)
    obtain ⟨x,y,z,xy,xz,yz,rfl⟩ := Finset.card_eq_three.mp (mem_powersetCard.mp h₁).2
    exact ⟨h₂,x,y,z,xy,xz,yz,powerset_two_triple xy xz yz⟩

theorem triangles_card (G : EdgeGraph V) : (triangles G).card=(tripleTriangles G).card := by
  classical
  rw [triangles_image,Finset.card_image_of_injOn]
  intro s hs t ht eq
  have hs3 := (mem_powersetCard.mp (mem_filter.mp (show s∈tripleTriangles G from hs)).1).2
  have ht3 := (mem_powersetCard.mp (mem_filter.mp (show t∈tripleTriangles G from ht)).1).2
  exact (triple_vertices s hs3).symm.trans
    ((congrArg (fun X : Finset (Finset V) => X.biUnion id) eq).trans (triple_vertices t ht3))

noncomputable def triangleIndicator {K : Type*} [Zero K] [One K]
    (G : EdgeGraph V) (s : Finset V) : K := by
  classical
  exact if s.powersetCard 2 ⊆ G then 1 else 0

theorem triangles_card_sum {K : Type*} [AddCommMonoidWithOne K] (G : EdgeGraph V) :
    ((triangles G).card : K)=∑ s∈(univ : Finset V).powersetCard 3, triangleIndicator G s := by
  classical
  rw [triangles_card]
  exact (Finset.sum_boole _ _).symm


variable {Ω K : Type*} [Fintype Ω] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem variance_actual_triangles_upper (p : Ω→K) (p1 : (∑ ω,p ω)=1)
    (G : Ω → EdgeGraph V) (u d : K) (d0 : 0≤d)
    (m : ∀ i∈(univ : Finset V).powersetCard 3, mean p (fun ω => triangleIndicator (G ω) i)=u)
    (cor : ∀ i j, i∈(univ : Finset V).powersetCard 3 → j∈(univ : Finset V).powersetCard 3 →
      i≠j → (j∩i).card≠2 →
      mean p (fun ω => triangleIndicator (G ω) i * triangleIndicator (G ω) j) ≤ u^2)
    (dia : ∀ i j, i∈(univ : Finset V).powersetCard 3 → j∈(univ : Finset V).powersetCard 3 →
      i≠j → (j∩i).card=2 →
      mean p (fun ω => triangleIndicator (G ω) i * triangleIndicator (G ω) j) ≤ d) :
    mean p (fun ω => (((triangles (G ω)).card : K)-
      (↑((Fintype.card V).choose 3) : K)*u)^2) ≤
    (↑((Fintype.card V).choose 3) : K)*(u+(↑(3*(Fintype.card V-3)) : K)*d) := by
  simp_rw [triangles_card_sum]
  have h := triangle_variance_upper p p1 (univ : Finset V) (fun i ω => triangleIndicator (G ω) i)
    u d d0 (fun i ω => ?_) m cor dia
  · simpa only [card_univ] using h
  · unfold triangleIndicator
    split <;> simp

#print axioms triangles_card_sum
#print axioms variance_actual_triangles_upper
end RobustFolkman
