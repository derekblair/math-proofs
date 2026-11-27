import EnergyTermination

open MeasureTheory Set Function
namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma meanBlock_relabel {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {ι ι' : Type*} (e : ι≃ι') (c : Y→ι) (f : Y→ℝ) :
    meanBlock ν (e ∘ c) f=meanBlock ν c f := by
  funext x
  have h : cell (e ∘ c) (e (c x))=cell c (c x) := by
    ext y
    simp [cell,Function.comp_def]
  unfold meanBlock meanCell
  change (∫ y in cell (e ∘ c) (e (c x)), f y ∂ν)/ν.real (cell (e ∘ c) (e (c x)))=_
  rw [h]

lemma blockKernel_W_relabel {ι ι' : Type*} [Fintype ι] [Fintype ι']
    [MeasurableSpace ι] [MeasurableSpace ι'] [MeasurableSingletonClass ι]
    [MeasurableSingletonClass ι'] (e : ι≃ι') (c : X→ι) (K : Kernel X)
    (hc : Measurable c) (hec : Measurable (e ∘ c)) :
    (blockKernel μ K (e ∘ c) hec).W=(blockKernel μ K c hc).W := by
  change meanBlock (μ.prod μ) (pairLabel (e ∘ c)) K.W=_
  have he : pairLabel (e ∘ c)=(e.prodCongr e) ∘ pairLabel c := rfl
  rw [he]
  exact meanBlock_relabel (μ.prod μ) (e.prodCongr e) (pairLabel c) K.W

structure ColorPartition (X : Type*) [MeasurableSpace X] where
  size : ℕ
  label : X→Fin size
  measurable_label : Measurable label

def refines (P Q : ColorPartition X) : Prop :=
  ∃ p : Fin Q.size→Fin P.size, ∀ x, P.label x=p (Q.label x)

lemma refines_refl (P : ColorPartition X) : refines P P := ⟨id,fun _ => rfl⟩
lemma refines_trans {P Q R : ColorPartition X} (hp : refines P Q) (hq : refines Q R) :
    refines P R := by
  obtain ⟨p,hp⟩ := hp
  obtain ⟨q,hq⟩ := hq
  exact ⟨p ∘ q,fun x => by rw [hp,hq]; rfl⟩

noncomputable def partitionKernel (K : Kernel X) (P : ColorPartition X) : Kernel X :=
  blockKernel μ K P.label P.measurable_label

theorem four_way_refine (K : Kernel X) (hμ : mass μ=1) (ε:ℝ) (hε : 0≤ε)
    (P : ColorPartition X) (hfail : ¬CutBound μ K (partitionKernel μ K P) ε) :
    ∃ Q : ColorPartition X, refines P Q ∧ Q.size≤P.size*4 ∧
      blockEnergy μ (partitionKernel μ K P)+ε^2 < blockEnergy μ (partitionKernel μ K Q) := by
  classical
  obtain ⟨S,T,hS,hT,hstep⟩ :=
    weak_regular_step μ K P.label P.measurable_label hμ ε hε hfail
  let ι := Fin P.size×Bool×Bool
  let e : ι≃Fin (Fintype.card ι) := Fintype.equivFin ι
  let c : X→ι := refinedLabel P.label S T
  have hc : Measurable c := refine_meas P.label P.measurable_label S T hS hT
  let Q : ColorPartition X :=
    ⟨Fintype.card ι,e ∘ c,(measurable_of_countable e).comp hc⟩
  refine ⟨Q,⟨fun i => (e.symm i).1,?_⟩,?_,?_⟩
  · intro x
    change P.label x=(e.symm (e (c x))).1
    simp [c,refinedLabel]
  · dsimp [Q,ι]
    simp [Fintype.card_prod,Nat.mul_assoc]
  · have hm := blockKernel_W_relabel μ e c K hc Q.measurable_label
    unfold blockEnergy partitionKernel at *
    rw [hm]
    exact hstep

/-- Finite marked weak regularity, with a bound on the number of cells
and preservation of each original label. -/
theorem finite_weak_regular (K : Kernel X) (hμ : mass μ=1) (ε:ℝ) (hε : 0<ε)
    (n:ℕ) (hn : 1<((n:ℝ)+1)*ε^2) (P : ColorPartition X) :
    ∃ Q : ColorPartition X, refines P Q ∧ Q.size≤P.size*4^n ∧
      CutBound μ K (partitionKernel μ K Q) ε := by
  obtain ⟨Q,hgood,href,hcard⟩ := energy_termination
    (fun Q => blockEnergy μ (partitionKernel μ K Q)) ColorPartition.size
    (fun Q => CutBound μ K (partitionKernel μ K Q) ε) refines
    refines_refl (fun h₁ h₂ => refines_trans h₁ h₂) (ε^2) (by positivity)
    (fun Q => block_energy_range μ (partitionKernel μ K Q) hμ)
    (fun Q hf => by
      obtain ⟨R,hr,hc,he⟩ := four_way_refine μ K hμ ε hε.le Q hf
      exact ⟨R,hr,he,hc⟩) n hn P
  exact ⟨Q,href,hcard,hgood⟩

#print axioms finite_weak_regular
end SparseHalfGraphon
