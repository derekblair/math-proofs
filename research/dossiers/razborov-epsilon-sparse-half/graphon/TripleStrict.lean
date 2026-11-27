import TripleSignatures

open Set MeasureTheory
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν]

noncomputable def threeLoad (S T U : Set X) : X→ℝ :=
  fun x => S.indicator (fun _ => 1) x + T.indicator (fun _ => 1) x +
    U.indicator (fun _ => 1) x

def UnitHalf (S T U : Set X) : Prop :=
  ∃ j : Bool×Bool×Bool, ∃ f : X→ℝ, Measurable f ∧
    (∀ x,0≤f x ∧ f x≤1) ∧ (∫ x,f x ∂ν)=2 ∧
    (∫ x,threeLoad (side S j.1) (side T j.2.1) (side U j.2.2) x*f x ∂ν)<2

private lemma load_instr (S T U : Set X) (j : Bool×Bool×Bool) (x : X)
    (hx : x∈tripleCell S T U j) :
    threeLoad S T U x =
      (if j.1 then 1 else 0)+(if j.2.1 then 1 else 0)+(if j.2.2 then 1 else 0) := by
  rcases j with ⟨a,b,c⟩
  have hf (A : Set X) (v : Bool) (hv : x∈side A v) :
      A.indicator (fun _ => (1:ℝ)) x=(if v then 1 else 0) := by
    cases v
    · exact indicator_of_notMem hv _
    · exact indicator_of_mem hv _
  unfold threeLoad
  rw [hf S a hx.1.1,hf T b hx.1.2,hf U c hx.2]

theorem positive_parity_half (S T U : Set X)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hST : Orthogonal ν S T) (hSU : Orthogonal ν S U) (hTU : Orthogonal ν T U)
    (x : ℝ) (hx : x=ν.real (tripleCell S T U (false,false,false))) (x0 : 0<x) (x2 : x≤1/2) :
    ∃ f : X→ℝ, Measurable f ∧ (∀ y,0≤f y ∧ f y≤1) ∧
      (∫ y,f y ∂ν)=2 ∧ (∫ y,threeLoad S T U y*f y ∂ν)<2 := by
  have hp := triple_parity ν S T U hS hT hU hST hSU hTU
  dsimp only at hp
  rw [←hx] at hp
  obtain ⟨m,m0,m1,ms,_,mc⟩ := SparseHalfSaturatedOrthogonal.sparse_singles x x0.le x2
  let q : Bool×Bool×Bool→ℝ
    | (false,false,false) => x
    | (true,false,false) => m
    | (false,true,false) => m
    | (false,false,true) => m
    | _ => 0
  let c : Bool×Bool×Bool→ℝ :=
    fun j => (if j.1 then 1 else 0)+(if j.2.1 then 1 else 0)+(if j.2.2 then 1 else 0)
  have hq (j : Bool×Bool×Bool) : 0≤q j ∧ q j≤ν.real (tripleCell S T U j) := by
    rcases j with ⟨a,b,d⟩
    cases a <;> cases b <;> cases d
    all_goals first | exact ⟨x0.le,le_of_eq hx⟩ |
      (refine ⟨m0,?_⟩; rw [hp]; exact m1) |
      exact ⟨le_rfl,measureReal_nonneg⟩
  obtain ⟨f,fm,fb,fs,fc⟩ := measurable_cell_fill ν (tripleCell S T U)
    (tripleCell_meas S T U hS hT hU) (fun _ _ => tripleCell_disjoint S T U)
    q c hq (threeLoad S T U) (load_instr S T U)
  refine ⟨f,fm,fb,?_,?_⟩
  · rw [fs,Fintype.sum_prod_type]
    simp [Fintype.sum_prod_type,Fintype.sum_bool,q]
    linarith
  · rw [fc,Fintype.sum_prod_type]
    simp [Fintype.sum_prod_type,Fintype.sum_bool,c,q]
    linarith [mc x0]

lemma flip_first (S T U : Set X) (a b c : Bool) :
    tripleCell Sᶜ T U (a,b,c)=tripleCell S T U (!a,b,c) := by
  cases a <;> simp [tripleCell,side]

lemma ortho_first_flip (S T : Set X) (h : Orthogonal ν S T) :
    Orthogonal ν Sᶜ T := by
  rintro ⟨a,b⟩
  cases a
  · simpa [sigCell] using h (true,b)
  · simpa [sigCell] using h (false,b)

/-- Any pairwise-orthogonal but not parity-degenerate triple of unit
blocks admits a strict normalized half by selecting one side per pair. -/
theorem orthogonal_strict_or_parity (S T U : Set X)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hST : Orthogonal ν S T) (hSU : Orthogonal ν S U) (hTU : Orthogonal ν T U) :
    UnitHalf ν S T U ∨
    ((ν.real (tripleCell S T U (false,false,false))=0 ∨
      ν.real (tripleCell S T U (false,false,false))=1) ∧
    ∀ a b c : Bool, ν.real (tripleCell S T U (a,b,c))=
      if xor (xor a b) c then 1-ν.real (tripleCell S T U (false,false,false))
      else ν.real (tripleCell S T U (false,false,false))) := by
  let x := ν.real (tripleCell S T U (false,false,false))
  have hp : ∀ a b c : Bool, ν.real (tripleCell S T U (a,b,c))=
      if xor (xor a b) c then 1-x else x := triple_parity ν S T U hS hT hU hST hSU hTU
  have xp : 0≤x := measureReal_nonneg
  have x' : ν.real (tripleCell S T U (true,false,false))=1-x := hp true false false
  have x1 : x≤1 := by linarith [measureReal_nonneg (μ:=ν) (s:=tripleCell S T U (true,false,false))]
  by_cases e : x=0 ∨ x=1
  · exact Or.inr ⟨e,hp⟩
  · have xp' : 0<x := lt_of_le_of_ne xp (fun y => e (Or.inl y.symm))
    have x1' : x<1 := lt_of_le_of_ne x1 (fun y => e (Or.inr y))
    left
    by_cases x2 : x≤1/2
    · exact ⟨(true,true,true),positive_parity_half ν S T U hS hT hU hST hSU hTU x rfl xp' x2⟩
    · have xe : 1-x=ν.real (tripleCell Sᶜ T U (false,false,false)) := by
        rw [flip_first]; exact x'.symm
      exact ⟨(false,true,true),positive_parity_half ν Sᶜ T U hS.compl hT hU
        (ortho_first_flip ν S T hST) (ortho_first_flip ν S U hSU) hTU
        (1-x) xe (by linarith) (by linarith)⟩

#print axioms orthogonal_strict_or_parity
end SparseHalfCountableEndpoint
