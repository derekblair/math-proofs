import GeometricBandLift
import GeometricTypicalFolkman

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem rootedLink_succAbove (N : ℕ) (t : ℝ) (x : Fin (N+1)→UnitSphere E)
    (v : Fin (N+1)) :
    rootedLinkEdges (pointGraph t x) v=
      liftEdges v.succAboveEmb (samplePredicateGraph (triangleAt t (x v)) (fun i => x (v.succAbove i))) := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.card_eq_two.1 (rootedLink_two _ _ _ he) with ⟨a,b,ab,rfl⟩
    obtain ⟨⟨va,px⟩,⟨vb,py⟩,⟨_,pz⟩⟩ := (rootedLinkEdge_iff (pointGraph t x) v a b ab).1 he
    obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq va.symm
    obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq vb.symm
    have ij : i≠j := fun h => ab (hi.symm.trans (congrArg v.succAbove h |>.trans hj))
    have pr : (x (v.succAbove i),x (v.succAbove j))∈triangleAt t (x v) := by
      rw [hi,hj]
      exact ⟨(pointGraph_pair t x va).1 px,(pointGraph_pair t x vb).1 py,(pointGraph_pair t x ab).1 pz⟩
    apply Finset.mem_map.2
    refine ⟨{i,j},(samplePredicate_edge_eq _ _ _).2 ⟨i,j,ij,pr,rfl⟩,?_⟩
    simp [map_insert,map_singleton,hi,hj]
  · intro h
    rcases Finset.mem_map.1 h with ⟨T,hT,rfl⟩
    rcases (samplePredicate_edge_eq _ _ _).1 hT with ⟨i,j,ij,hij,rfl⟩
    have ai := v.succAbove_ne i
    have aj := v.succAbove_ne j
    have bj : v.succAbove i≠v.succAbove j := v.succAboveEmb.injective.ne ij
    change t≤⟪(x v).val,(x (v.succAbove i)).val⟫_ℝ ∧ t≤⟪(x v).val,(x (v.succAbove j)).val⟫_ℝ ∧
      t≤⟪(x (v.succAbove i)).val,(x (v.succAbove j)).val⟫_ℝ at hij
    change ({i,j}:Finset (Fin N)).map v.succAboveEmb ∈ _
    rw [map_insert,map_singleton]
    exact (rootedLinkEdge_iff (pointGraph t x) v _ _ bj).2
      ⟨⟨ai.symm,(pointGraph_pair t x ai.symm).2 hij.1⟩,
        ⟨aj.symm,(pointGraph_pair t x aj.symm).2 hij.2.1⟩,⟨bj,(pointGraph_pair t x bj).2 hij.2.2⟩⟩

def sampleBadCut {J : Type*} [Fintype J] [DecidableEq J] (t : ℝ) (a : UnitSphere E)
    (y : J→UnitSphere E) : Prop :=
  ∃ b : J→Bool,
    let G := samplePredicateGraph (triangleAt t a) y
    (5/8:ℝ)*(G.card:ℝ)<cutCount G b

theorem typical_root_bound_from_conditionals (N : ℕ) (t ε : ℝ) (ε0 : 0≤ε) (v : Fin (N+1))
    (hs : ∀ a : UnitSphere E,
      let σ := uniformSphere (volume : Measure E)
      (Measure.pi (fun _ : Fin N => σ)).real {y | sampleBadCut t a y}≤ε) :
    Moment.mean (sphericalHostWeight (V:=Fin (N+1)) (E:=E) t)
      (fun g => if v∈failingRoots g then 1 else 0)≤ε := by
  classical
  rw [mean_event_of_host]
  let σ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let ν := Measure.pi (fun _ : Fin N => σ)
  let μ := Measure.pi (fun _ : Fin (N+1) => σ)
  let B := {x : Fin (N+1)→UnitSphere E | v∈failingRoots (pointGraph t x)}
  have bm : MeasurableSet B := measurable_pointGraph_pred t (fun g => v∈failingRoots g)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => UnitSphere E) v
  have P := measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => σ) v
  let R := e.symm ⁻¹' B
  have rm : MeasurableSet R := e.symm.measurable bm
  have law : μ B=(σ.prod ν) R := by
    have h := P.measure_preimage rm.nullMeasurableSet
    change μ (e ⁻¹' R)=(σ.prod ν) R at h
    rw [show e ⁻¹' R=B by ext x; simp [R]] at h
    exact h
  have sub (a : UnitSphere E) :
      (Prod.mk a ⁻¹' R) ⊆ {y : Fin N→UnitSphere E | sampleBadCut t a y} := by
    intro y hy
    let x := e.symm (a,y)
    have er : e x=(a,y) := e.apply_symm_apply _
    have ex : x v=a := congrArg Prod.fst er
    have ey : (fun i : Fin N => x (v.succAbove i))=y := congrArg Prod.snd er
    have fail : ¬RootCutGood (pointGraph t x) v := (mem_failingRoots _ _).1 hy
    unfold RootCutGood at fail
    push_neg at fail
    obtain ⟨b,hb⟩ := fail
    have l := rootedLink_succAbove N t x v
    rw [ex,ey] at l
    have eq (G : EdgeGraph (Fin (N+1))) :
        rootedLinkCut G v b=cutCount (rootedLinkEdges G v) b := rfl
    rw [eq,l,liftEdges_card,liftEdges_cut] at hb
    exact ⟨b ∘ v.succAboveEmb,hb⟩
  have mass : (σ.prod ν) R≤ENNReal.ofReal ε := by
    rw [Measure.prod_apply rm]
    calc
      _ ≤ ∫⁻ _ : UnitSphere E, ENNReal.ofReal ε ∂σ := by
        apply lintegral_mono
        intro a
        have h := hs a
        change (ν {y | sampleBadCut t a y}).toReal≤ε at h
        have hh := ENNReal.ofReal_le_ofReal h
        rw [ENNReal.ofReal_toReal (measure_ne_top ν _)] at hh
        exact (measure_mono (sub a)).trans hh
      _ = _ := by rw [lintegral_const,measure_univ,mul_one]
  change (μ B).toReal≤ε
  rw [law]
  have x := ENNReal.toReal_mono ENNReal.ofReal_ne_top mass
  exact x.trans_eq (ENNReal.toReal_ofReal ε0)

#print axioms rootedLink_succAbove
#print axioms typical_root_bound_from_conditionals
end RobustFolkman.GeometricGap
