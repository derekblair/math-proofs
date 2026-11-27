import GeometricDiamondEvents
import GeometricSharedRoot

namespace RobustFolkman.GeometricGap
open MeasureTheory MeasureTheory.Measure Finset Set
open scoped InnerProductSpace ENNReal
variable {S : Type*} [MeasurableSpace S]

def packTri (p : (Fin 2⊕Unit)→S) : S×(S×S) :=
  (p (.inr ()),p (.inl 0),p (.inl 1))

def packRootedTwo (p : Five→S) : S×((S×S)×(S×S)) :=
  (p (.inr ()),(p (.inl (.inl 0)),p (.inl (.inl 1))),
     (p (.inl (.inr 0)),p (.inl (.inr 1))))

theorem packTri_measurePreserving (σ : Measure S) [SigmaFinite σ] :
    MeasurePreserving packTri (Measure.pi fun _ : Fin 2⊕Unit => σ) (σ.prod (σ.prod σ)) := by
  have M := measurePreserving_swap.comp <|
    (measurePreserving_piFinTwo (fun _ : Fin 2 => σ)).prod (measurePreserving_funUnique σ Unit)
      |>.comp (measurePreserving_sumPiEquivProdPi (fun _ : Fin 2⊕Unit => σ))
  exact M

theorem packRootedTwo_measurePreserving (σ : Measure S) [SigmaFinite σ] :
    MeasurePreserving packRootedTwo (Measure.pi fun _ : Five => σ)
      (σ.prod ((σ.prod σ).prod (σ.prod σ))) := by
  have MM := (measurePreserving_piFinTwo (fun _ : Fin 2 => σ)).prod
    (measurePreserving_piFinTwo (fun _ : Fin 2 => σ))
    |>.comp (measurePreserving_sumPiEquivProdPi (fun _ : Four => σ))
  have M := measurePreserving_swap.comp <| (MM.prod (measurePreserving_funUnique σ Unit))
    |>.comp (measurePreserving_sumPiEquivProdPi (fun _ : Five => σ))
  exact M

variable {V E : Type*} [DecidableEq V] [Fintype V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem mean_event_of_host (t : ℝ) (P : EdgeGraph V→Prop) [DecidablePred P] :
    Moment.mean (sphericalHostWeight (E:=E) t) (fun g => if P g then (1:ℝ) else 0) =
      ((Measure.pi fun _ : V => uniformSphere (volume : Measure E)) {x | P (pointGraph t x)}).toReal := by
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  have e (g : EdgeGraph V) : sphericalHostWeight (E:=E) t g*(if P g then (1:ℝ) else 0) =
      if P g then sphericalHostWeight (E:=E) t g else 0 := by split <;> simp
  unfold Moment.mean
  simp_rw [e]
  exact finiteGraphMass_event (Measure.pi fun _ : V => σ) (pointGraph t)
    (measurable_pointGraph_fiber t) P

theorem triangle_event_root (t : ℝ) (u v w : V) (uv : u≠v) (uw : u≠w) (vw : v≠w)
    (x : V→UnitSphere E) :
    ({u,v,w}:Finset V).powersetCard 2 ⊆ pointGraph t x ↔
      (x u,x v,x w)∈triangleFromRoot t := by
  rw [powerset_two_triple uv uw vw]
  have e (a b : V) (ab : a≠b) :
      ({a,b}:Finset V)∈pointGraph t x ↔ t≤⟪(x a:E),(x b:E)⟫_ℝ := by
    have := pointGraph_hasEdge t x a b
    simpa [hasEdge,ab] using this
  simp [triangleEdges,Finset.insert_subset_iff,e _ _ uv,e _ _ uw,e _ _ vw,triangleFromRoot,triangleAt]

#print axioms triangle_event_root
end RobustFolkman.GeometricGap
