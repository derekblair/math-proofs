import ActivePairPartitions

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
variable (μ ω ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ω] [IsFiniteMeasure ν]

/-- All saturated outside edges lie between positive active pairs. The remaining
outside points have zero outside degree a.e. Each active pair has one common
half-mass anchor partition, and the corresponding 0/1 profiles are exact a.e.
in both Fubini directions. A dummy empty pair is permitted. -/
theorem saturated_active_pairs
    (hω : ω≪μ) (hν : ν≪μ) (K : Kernel X) (nonzero : ν univ≠0)
    (S : Set X) (ms : MeasurableSet S) (concentrated : ∀ᵐ x ∂ω, x∈S)
    (tri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0)
    (sat : ∀ᵐ x ∂ω, mass ν/2≤deg ν K x) :
    ∃ (I : Type) (_ : Countable I) (_ : Nonempty I) (P Q A : I→Set X),
      (∀ i, MeasurableSet (P i) ∧ MeasurableSet (Q i) ∧ MeasurableSet (A i)) ∧
      (∀ i, P i∪Q i⊆S) ∧ (∀ i, Disjoint (P i) (Q i)) ∧
      Pairwise (Disjoint on fun i => P i∪Q i) ∧
      (∀ᵐ z ∂ω.prod ω, 0<K.W z → ∃ i,
        (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i)) ∧
      (∀ᵐ x ∂ω, x∈(⋃ i,P i∪Q i) ↔ 0<deg ω K x) ∧
      (∀ i, (P i=∅ ∧ Q i=∅) ∨
        (0<ω.real (P i) ∧ 0<ω.real (Q i) ∧
         ν.real (A i)=mass ν/2 ∧ ν.real (A i)ᶜ=mass ν/2 ∧
         (∀ᵐ v ∂ν, (fun x=>K.W (v,x)) =ᵐ[ω.restrict (P i)] (fun _=>oneOn (A i) v)) ∧
         (∀ᵐ v ∂ν, (fun x=>K.W (v,x)) =ᵐ[ω.restrict (Q i)] (fun _=>oneOn (A i)ᶜ v)) ∧
         (∀ᵐ x ∂ω.restrict (P i), (fun v=>K.W (x,v)) =ᵐ[ν] oneOn (A i)) ∧
         (∀ᵐ x ∂ω.restrict (Q i), (fun v=>K.W (x,v)) =ᵐ[ν] oneOn (A i)ᶜ))) := by
  classical
  obtain ⟨T,tm,tg,tp,tu⟩ := countable_generating_pi (X:=X)
  obtain ⟨I,ic,inh,P,Q,mp,mq,inside,inner,outer,support,root⟩ :=
    paired_profile_cells ω ν K T tm tg tp tu nonzero S ms (edge_complement μ ν ω hν hω K tri sat)
  letI : Countable I := ic
  obtain ⟨p,q,pm,qm,subs,positive,disj,disjall,edge,isolates,row⟩ :=
    prune_active_pairs ω ν K S P Q mp mq inside inner outer support concentrated root
  have ex (i : I) : ∃ A : Set X, MeasurableSet A ∧
      ((p i=∅ ∧ q i=∅) ∨ (0<ω.real (p i) ∧ 0<ω.real (q i) ∧
       ν.real A=mass ν/2 ∧ ν.real Aᶜ=mass ν/2 ∧
       (∀ᵐ v ∂ν, (fun x=>K.W (v,x)) =ᵐ[ω.restrict (p i)] (fun _=>oneOn A v)) ∧
       (∀ᵐ v ∂ν, (fun x=>K.W (v,x)) =ᵐ[ω.restrict (q i)] (fun _=>oneOn Aᶜ v)) ∧
       (∀ᵐ x ∂ω.restrict (p i), (fun v=>K.W (x,v)) =ᵐ[ν] oneOn A) ∧
       (∀ᵐ x ∂ω.restrict (q i), (fun v=>K.W (x,v)) =ᵐ[ν] oneOn Aᶜ))) := by
    rcases positive i with h|⟨hp,hq⟩
    · exact ⟨∅,MeasurableSet.empty,Or.inl h⟩
    · have rowi := row.mono (fun v hv => hv i)
      obtain ⟨A,am,a,b,c,d,e,f⟩ := active_pair_anchor_halves ω ν K (p i) (q i) hp hq sat rowi
      exact ⟨A,am,Or.inr ⟨hp,hq,a,b,c,d,e,f⟩⟩
  choose A Am Aprofile using ex
  exact ⟨I,ic,inh,p,q,A,fun i=>⟨pm i,qm i,Am i⟩,
    fun i=>(union_subset_union (subs i).1 (subs i).2).trans (inside i),
    disj,disjall,edge,isolates,Aprofile⟩

#print axioms saturated_active_pairs
end SparseHalfGraphon
