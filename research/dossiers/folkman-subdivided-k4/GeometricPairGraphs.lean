import GeometricPairMoment
import GeometricDirectedLinkSum

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset Matrix
open scoped ENNReal BigOperators
variable {J S : Type*} [Fintype J] [DecidableEq J]

noncomputable def samplePredicateGraph (A : Set (S×S)) (x : J→S) : EdgeGraph J := by
  classical
  exact ((offDiagonal : Finset (J×J)).filter (fun i => (x i.1,x i.2)∈A)).image orderedEdge

theorem samplePredicate_edge_eq (A : Set (S×S)) (x : J→S) (e : Finset J) :
    e∈samplePredicateGraph A x ↔ ∃ i j, i≠j ∧ (x i,x j)∈A ∧ ({i,j}:Finset J)=e := by
  classical
  simp only [samplePredicateGraph,Finset.mem_image,Finset.mem_filter,offDiagonal,
    Finset.mem_univ,true_and,Prod.exists,orderedEdge,and_assoc]

theorem samplePredicate_pair (A : Set (S×S)) (x : J→S)
    (sym : ∀ u v, (u,v)∈A ↔ (v,u)∈A) {i j : J} (ij : i≠j) :
    ({i,j}:Finset J)∈samplePredicateGraph A x ↔ (x i,x j)∈A := by
  rw [samplePredicate_edge_eq]
  constructor
  · rintro ⟨a,b,ab,p,eq⟩
    rcases pair_orientation ab eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact p
    · exact (sym _ _).2 p
  · exact fun p => ⟨i,j,ij,p,rfl⟩

theorem samplePredicate_mono (A B : Set (S×S)) (x : J→S) (sub : A⊆B) :
    samplePredicateGraph A x⊆samplePredicateGraph B x := by
  intro e he
  rcases (samplePredicate_edge_eq A x e).1 he with ⟨i,j,n,p,rfl⟩
  exact (samplePredicate_edge_eq B x _).2 ⟨i,j,n,sub p,rfl⟩

/-- The number of unordered exceptional edges is no greater than the
number of exceptional ordered observations. The inequality avoids all
symmetry assumptions on the exceptional predicate. -/
theorem samplePredicate_card_le_count (A : Set (S×S)) (x : J→S) :
    ((samplePredicateGraph A x).card:ℝ≥0∞)≤samplePairCount (J:=J) A x := by
  classical
  unfold samplePredicateGraph samplePairCount
  have eq : (∑ p ∈ (offDiagonal : Finset (J×J)), A.indicator (fun _ => (1:ℝ≥0∞)) (x p.1,x p.2)) =
    (((offDiagonal : Finset (J×J)).filter (fun p => (x p.1,x p.2)∈A)).card:ℝ≥0∞) := by
    simp only [Set.indicator]
    rw [←Finset.sum_filter]
    simp [nsmul_eq_mul]
  rw [eq]
  exact_mod_cast Finset.card_image_le

theorem samplePredicate_sdiff_count (A B : Set (S×S)) (x : J→S) :
    (((samplePredicateGraph A x \ samplePredicateGraph B x).card):ℝ≥0∞)
      ≤ samplePairCount (J:=J) (A\B) x := by
  classical
  have sub : (samplePredicateGraph A x \ samplePredicateGraph B x)⊆
      samplePredicateGraph (A\B) x := by
    intro e he
    obtain ⟨ha,hb⟩ := Finset.mem_sdiff.1 he
    obtain ⟨i,j,ne,h,rfl⟩ := (samplePredicate_edge_eq A x e).1 ha
    have h2 : (x i,x j)∉B := fun hb' => hb ((samplePredicate_edge_eq B x _).2 ⟨i,j,ne,hb',rfl⟩)
    exact (samplePredicate_edge_eq (A\B) x _).2 ⟨i,j,ne,⟨h,h2⟩,rfl⟩
  exact (by exact_mod_cast Finset.card_le_card sub :
    (((samplePredicateGraph A x \ samplePredicateGraph B x).card):ℝ≥0∞)≤
      ((samplePredicateGraph (A\B) x).card:ℝ≥0∞)).trans (samplePredicate_card_le_count _ _)

#print axioms samplePredicate_sdiff_count
end RobustFolkman.GeometricGap
