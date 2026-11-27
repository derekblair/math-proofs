import GeometricRootOverlap

namespace RobustFolkman.GeometricGap
open MeasureTheory Finset Set
open scoped ENNReal
variable {V E : Type*} [DecidableEq V] [Fintype V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem tripleLabel_mem (a b c : V) (i : Fin 2⊕Unit) :
    tripleLabel a b c i∈({a,b,c}:Finset V) := by
  rcases i with i|i
  · fin_cases i <;> simp [tripleLabel]
  · simp [tripleLabel]

theorem disjoint_triangle_moments (t : ℝ) (s r : Finset V)
    (sc : s.card=3) (rc : r.card=3) (dis : Disjoint s r) :
    Moment.mean (sphericalHostWeight (E:=E) t)
      (fun g => triangleIndicator g s * triangleIndicator g r) =
      ((patternMass (E:=E) triangleCon t).toReal)^2 := by
  classical
  obtain ⟨a,b,c,ab,ac,bc,rfl⟩ := Finset.card_eq_three.mp sc
  obtain ⟨d,e,f,de,df,ef,rfl⟩ := Finset.card_eq_three.mp rc
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let ν := σ.prod (σ.prod σ)
  let T := Fin 2⊕Unit
  let L := Sum.elim (tripleLabel b c a) (tripleLabel e f d)
  have inj : Function.Injective L := by
    intro i j h
    rcases i with i|i <;> rcases j with j|j
    · exact congrArg Sum.inl (tripleLabel_injective bc ab.symm ac.symm h)
    · have li : L (.inl i) ∈ ({a,b,c}:Finset V) := by
        simpa [L,Finset.mem_insert,or_comm,or_left_comm,or_assoc] using tripleLabel_mem b c a i
      have lj : L (.inr j) ∈ ({d,e,f}:Finset V) := by
        simpa [L,Finset.mem_insert,or_comm,or_left_comm,or_assoc] using tripleLabel_mem e f d j
      exact False.elim (Finset.disjoint_left.mp dis li (h.symm ▸ lj))
    · have li : L (.inr i) ∈ ({d,e,f}:Finset V) := by
        simpa [L,Finset.mem_insert,or_comm,or_left_comm,or_assoc] using tripleLabel_mem e f d i
      have lj : L (.inl j) ∈ ({a,b,c}:Finset V) := by
        simpa [L,Finset.mem_insert,or_comm,or_left_comm,or_assoc] using tripleLabel_mem b c a j
      exact False.elim (Finset.disjoint_left.mp dis lj (h ▸ li))
    · exact congrArg Sum.inr (tripleLabel_injective ef de.symm df.symm h)
  let l : T⊕T↪V := ⟨L,inj⟩
  let F := fun a' : V→UnitSphere E =>
    ((a' a,a' b,a' c),(a' d,a' e,a' f))
  have pres : MeasurePreserving F (Measure.pi fun _ : V => σ) (ν.prod ν) := by
    exact ((packTri_measurePreserving σ).prod (packTri_measurePreserving σ)).comp <|
      (measurePreserving_sumPiEquivProdPi (fun _ : T⊕T => σ)).comp
        (pi_embedding_measurePreserving σ l)
  let B := triangleFromRoot (E:=E) t
  let P : EdgeGraph V→Prop := fun g =>
    ({a,b,c}:Finset V).powersetCard 2 ⊆ g ∧ ({d,e,f}:Finset V).powersetCard 2 ⊆ g
  have seteq : F ⁻¹' (B×ˢB) = {v | P (pointGraph t v)} := by
    ext v
    exact and_congr (triangle_event_root t a b c ab ac bc v).symm
      (triangle_event_root t d e f de df ef v).symm
  have Bm : MeasurableSet B := triangleFromRoot_measurable t
  have mp := pres.measure_preimage (Bm.prod Bm).nullMeasurableSet
  rw [seteq,Measure.prod_prod,←pow_two] at mp
  have eq (g : EdgeGraph V) :
      triangleIndicator (K:=ℝ) g {a,b,c} * triangleIndicator g {d,e,f} =
        if P g then 1 else 0 := by
    simp only [triangleIndicator,P]
    split <;> split <;> simp_all
  simp_rw [eq]
  rw [mean_event_of_host,mp,ENNReal.toReal_pow,
    triangle_root_mass (E:=E) t a b c ab ac bc]

#print axioms disjoint_triangle_moments
end RobustFolkman.GeometricGap
