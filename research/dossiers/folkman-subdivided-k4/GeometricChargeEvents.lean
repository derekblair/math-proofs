import GeometricForbiddenLabels

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Finset Set
open scoped ENNReal
variable {V : Type*} [DecidableEq V] [Fintype V]

def freshLabel (r : Tuple5 V) (w : V) : Five⊕Unit→V :=
  Sum.elim (tupleLabel r) (fun _ => w)

theorem tupleLabel_mem (r : Tuple5 V) (i : Five) :
    tupleLabel r i ∈ ({r.1,r.2.1,r.2.2.1,r.2.2.2.1,r.2.2.2.2}:Finset V) := by
  rcases i with (i|i)|i
  · fin_cases i <;> simp [tupleLabel]
  · fin_cases i <;> simp [tupleLabel]
  · simp [tupleLabel]

theorem freshLabel_injective (r : Tuple5 V) (w : V) (g : EdgeGraph V)
    (p : goodFresh g r w) : Function.Injective (freshLabel r w) := by
  obtain ⟨good,notin,_,_⟩ := p
  have j := tupleLabel_injective r g good
  intro a b eq
  rcases a with a|a <;> rcases b with b|b
  · exact congrArg Sum.inl (j eq)
  · change tupleLabel r a = w at eq
    exact (notin (eq ▸ tupleLabel_mem r a)).elim
  · change w = tupleLabel r b at eq
    exact (notin (eq.symm ▸ tupleLabel_mem r b)).elim
  · cases a
    cases b
    rfl

theorem extension_labeled_iff (r : Tuple5 V) (w : V) (j : Function.Injective (freshLabel r w))
    (g : EdgeGraph V) :
    labeledPattern extCon ⟨freshLabel r w,j⟩ g ↔ goodFresh g r w := by
  rcases r with ⟨u,v,x,y,z⟩
  have ee (i : Five) : w ≠ tupleLabel (u,v,x,y,z) i :=
    j.ne (show (Sum.inr () : Five⊕Unit)≠Sum.inl i by simp)
  have wu : w≠u := by simpa [tupleLabel] using ee (.inl (.inr 0))
  have wv : w≠v := by simpa [tupleLabel] using ee (.inl (.inr 1))
  have wx : w≠x := by simpa [tupleLabel] using ee (.inl (.inl 0))
  have wy : w≠y := by simpa [tupleLabel] using ee (.inl (.inl 1))
  have wz : w≠z := by simpa [tupleLabel] using ee (.inr ())
  have hJ : Function.Injective (tupleLabel (u,v,x,y,z)) :=
    fun _ _ h => Sum.inl.inj (j h)
  rw [extCon,page_labeled_iff]
  have eq : oldLabels (⟨freshLabel (u,v,x,y,z) w,j⟩ : Five⊕Unit ↪ V) =
      ⟨tupleLabel (u,v,x,y,z),hJ⟩ := by ext i; rfl
  rw [eq,forbidden_labeled_iff]
  simp [freshLabel,tupleLabel,goodFresh,hasEdge,wu,wv,wx,wy,wz,Ne.symm]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem forbidden_moment_bound (t : ℝ) (r : Tuple5 V) :
    Moment.mean (sphericalHostWeight (E:=E) t) (fun g => copyIndicator g r) ≤
      (patternMass (E:=E) subEdges t).toReal := by
  classical
  by_cases h : Function.Injective (tupleLabel r)
  · let l : Five↪V := ⟨tupleLabel r,h⟩
    have per (g : EdgeGraph V) : copyIndicator (K:=ℝ) g r=labeledIndicator subEdges l g := by
      simp only [copyIndicator,labeledIndicator]
      rw [forbidden_labeled_iff r h]
    simp_rw [per]
    exact (labeled_moment_probability subEdges forbidden_noloop l t).le
  · have no (g : EdgeGraph V) : ¬goodTuple g r := fun p => h (tupleLabel_injective r g p)
    simp [copyIndicator,no,Moment.mean]

theorem extension_moment_bound (t : ℝ) (rw : Tuple5 V×V) :
    Moment.mean (sphericalHostWeight (E:=E) t) (fun g => freshIndicator g rw) ≤
      (patternMass (E:=E) extCon t).toReal := by
  classical
  by_cases h : Function.Injective (freshLabel rw.1 rw.2)
  · let l : Five⊕Unit↪V := ⟨freshLabel rw.1 rw.2,h⟩
    have per (g : EdgeGraph V) : freshIndicator (K:=ℝ) g rw=labeledIndicator extCon l g := by
      simp only [freshIndicator,labeledIndicator]
      rw [extension_labeled_iff rw.1 rw.2 h]
    simp_rw [per]
    exact (labeled_moment_probability extCon extension_noloop l t).le
  · have no (g : EdgeGraph V) : ¬goodFresh g rw.1 rw.2 := fun p => h (freshLabel_injective _ _ g p)
    simp [freshIndicator,no,Moment.mean]

#print axioms forbidden_moment_bound
#print axioms extension_moment_bound
end RobustFolkman.GeometricGap
