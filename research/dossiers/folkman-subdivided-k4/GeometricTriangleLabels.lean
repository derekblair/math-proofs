import GeometricChargeEvents
import GeometricTriangleCount

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

def tripleLabel (u v w : V) : Fin 2⊕Unit→V :=
  Sum.elim (fun i => if i=0 then u else v) (fun _ => w)

theorem tripleLabel_injective {u v w : V} (uv : u≠v) (uw : u≠w) (vw : v≠w) :
    Function.Injective (tripleLabel u v w) := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j
  all_goals fin_cases i <;> fin_cases j <;> first | rfl | (simp [tripleLabel] at h; grind)

theorem triangle_labeled_iff (u v w : V) (uv : u≠v) (uw : u≠w) (vw : v≠w)
    (g : EdgeGraph V) :
    labeledPattern triangleCon ⟨tripleLabel u v w,tripleLabel_injective uv uw vw⟩ g ↔
      ({u,v,w}:Finset V).powersetCard 2 ⊆ g := by
  rw [powerset_two_triple uv uw vw,triangleCon,page_labeled_iff,edge_labeled_iff]
  simp [triangleEdges,hasEdge,tripleLabel,oldLabels,uv,uw,vw,Finset.insert_subset_iff,
    and_assoc]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem triangle_moment_exact (t : ℝ) (s : Finset V) (sc : s.card=3) :
    Moment.mean (sphericalHostWeight (E:=E) t) (fun g => triangleIndicator g s) =
      (patternMass (E:=E) triangleCon t).toReal := by
  classical
  obtain ⟨u,v,w,uv,uw,vw,rfl⟩ := Finset.card_eq_three.mp sc
  let l : Fin 2⊕Unit↪V := ⟨tripleLabel u v w,tripleLabel_injective uv uw vw⟩
  have per (g : EdgeGraph V) : triangleIndicator (K:=ℝ) g {u,v,w}=labeledIndicator triangleCon l g := by
    simp only [triangleIndicator,labeledIndicator]
    rw [triangle_labeled_iff u v w uv uw vw]
    split <;> simp_all
  simp_rw [per]
  exact labeled_moment_probability triangleCon triangle_noloop l t

#print axioms triangle_moment_exact
end RobustFolkman.GeometricGap
