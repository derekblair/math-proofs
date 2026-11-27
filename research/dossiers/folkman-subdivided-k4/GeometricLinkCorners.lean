import GeometricFolkmanReduction

namespace RobustFolkman.GeometricGap
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

def triVertices (T : EdgeGraph V) : Finset V := T.biUnion id
def incidentSides (T : EdgeGraph V) (v : V) : EdgeGraph V := T.filter (fun e => v∈e)

noncomputable def rootMixed (T : EdgeGraph V) (c : Finset V→Bool) (v : V) : ℝ := by
  classical
  exact if v∈triVertices T ∧ ¬Monochrom c (incidentSides T v) then 1 else 0

noncomputable def rootIncidence (T : EdgeGraph V) (v : V) : ℝ :=
  if v∈triVertices T then 1 else 0

noncomputable def monoContribution (T : EdgeGraph V) (c : Finset V→Bool) : ℝ := by
  classical
  exact if Monochrom c T then 1 else 0

theorem incident_triplet (a b d : V) (ab : a≠b) (ad : a≠d) (bd : b≠d) :
    incidentSides (triangleEdges a b d) a={{a,b},{a,d}} ∧
    incidentSides (triangleEdges a b d) b={{a,b},{b,d}} ∧
    incidentSides (triangleEdges a b d) d={{a,d},{b,d}} := by
  constructor
  · ext e
    simp [incidentSides,triangleEdges,ab,ad]
    grind
  constructor
  · ext e
    simp [incidentSides,triangleEdges,ab,bd]
    grind
  · ext e
    simp [incidentSides,triangleEdges,ad,bd]
    grind

theorem mono_two_iff {W : Type*} [DecidableEq W] (c : W→Bool) (u v : W) :
    Monochrom c {u,v} ↔ c u=c v := by
  constructor
  · exact fun h => h u (by simp) v (by simp)
  · intro h e he f hf
    simp only [mem_insert,mem_singleton] at he hf
    rcases he with rfl|rfl <;> rcases hf with rfl|rfl <;> simp [h]

theorem mono_three_iff {W : Type*} [DecidableEq W] (c : W→Bool) (u v w : W) :
    Monochrom c {u,v,w} ↔ c u=c v ∧ c v=c w := by
  constructor
  · exact fun h => ⟨h u (by simp) v (by simp),h v (by simp) w (by simp)⟩
  · rintro ⟨h,k⟩ e he f hf
    simp only [mem_insert,mem_singleton] at he hf
    rcases he with rfl|rfl|rfl <;> rcases hf with rfl|rfl|rfl <;> simp [h,k]

theorem triple_vertices_exact (a b d : V) :
    triVertices (triangleEdges a b d)={a,b,d} := by
  ext w
  simp [triVertices,triangleEdges]

theorem local_link_corner_count (T : EdgeGraph V) (shape : triangleShape T)
    (c : Finset V→Bool) :
    (∑ v : V, rootMixed T c v)+2*monoContribution T c=2 := by
  classical
  obtain ⟨a,b,d,ab,ad,bd,rfl⟩ := shape
  let S : Finset V := {a,b,d}
  have ex : (∑ v : V, rootMixed (triangleEdges a b d) c v) =
      ∑ v∈S, rootMixed (triangleEdges a b d) c v := by
    symm
    apply Finset.sum_subset (subset_univ _)
    intro v _ hv
    simp [rootMixed,triple_vertices_exact,show v∉({a,b,d}:Finset V) from hv]
  obtain ⟨ha,hb,hd⟩ := incident_triplet a b d ab ad bd
  rw [ex]
  have n1 : a∉({b,d}:Finset V) := by simp [ab,ad]
  have n2 : b∉({d}:Finset V) := by simp [bd]
  dsimp only [S]
  rw [sum_insert n1,sum_insert n2,sum_singleton]
  simp only [rootMixed,triple_vertices_exact,mem_insert,mem_singleton,
    true_or,or_true,true_and,ha,hb,hd,mono_two_iff,monoContribution,
    show Monochrom c (triangleEdges a b d) ↔ c {a,b}=c {a,d} ∧ c {a,d}=c {b,d} from mono_three_iff _ _ _ _]
  cases h₁ : c {a,b} <;> cases h₂ : c {a,d} <;> cases h₃ : c {b,d} <;> norm_num [h₁,h₂,h₃]

theorem local_link_incidence (T : EdgeGraph V) (shape : triangleShape T) :
    ∑ v : V, rootIncidence T v = 3 := by
  classical
  obtain ⟨a,b,d,ab,ad,bd,rfl⟩ := shape
  have cc : ({a,b,d}:Finset V).card=3 := Finset.card_eq_three.mpr ⟨a,b,d,ab,ad,bd,rfl⟩
  simp only [rootIncidence,triple_vertices_exact]
  rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  simp [cc]

#print axioms local_link_corner_count
#print axioms local_link_incidence
end RobustFolkman.GeometricGap
