import ActiveBankEndpoints
import TwoLargeLightKernel

open Set MeasureTheory Function Filter
open scoped ENNReal BigOperators
namespace SparseHalfGraphon

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
variable {K : Kernel Y} {A : Set Y} {I : Type*} (B : ActiveBank μ K A I)

noncomputable def ActiveBank.isBigP (j : I) : Bool := decide (μ.real (B.Q j)≤μ.real (B.P j))

noncomputable def ActiveBank.pick (j : I) (b : Bool) : Set Y :=
  B.side j (Bool.xor (B.isBigP j) b)

noncomputable def ActiveBank.pickSig (j : I) : Set Y :=
  B.anchorSide j (Bool.xor (B.isBigP j) true)

lemma ActiveBank.pick_sig_matches (j : I) (b : Bool) :
    SparseHalfCountableEndpoint.side (B.pickSig j) b =
      B.anchorSide j (Bool.xor (B.isBigP j) b) := by
  cases h : B.isBigP j <;> cases b <;>
    simp [SparseHalfCountableEndpoint.side,ActiveBank.pickSig,ActiveBank.anchorSide,h]

lemma ActiveBank.pick_mass (j : I) (b : Bool) :
    μ.real (B.pick j b)=(if b then B.p j else B.q j)/10 := by
  unfold ActiveBank.pick ActiveBank.p ActiveBank.q larger10 smaller10
  cases b
  · by_cases h : μ.real (B.Q j)≤μ.real (B.P j)
    · simp [ActiveBank.isBigP,ActiveBank.side,h,min_eq_right h]
    · have h' := (lt_of_not_ge h).le
      simp [ActiveBank.isBigP,ActiveBank.side,h,min_eq_left h']
  · by_cases h : μ.real (B.Q j)≤μ.real (B.P j)
    · simp [ActiveBank.isBigP,ActiveBank.side,h,max_eq_left h]
    · have h' := (lt_of_not_ge h).le
      simp [ActiveBank.isBigP,ActiveBank.side,h,max_eq_right h']

lemma ActiveBank.pickSig_mass (j : I) (hn : 0<B.p j) (hAm : μ.real A=2/5) :
    ((10:ℝ≥0∞) • μ.restrict A).real (B.pickSig j)=2 := by
  rcases B.profiles j with ⟨hp,hq⟩ | ⟨_,_,hP,hQ,_⟩
  · simp [ActiveBank.p,larger10,hp,hq] at hn
  have hm : mass (μ.restrict A)=2/5 := by simp [mass,hAm]
  have hPick : (μ.restrict A).real (B.pickSig j)=1/5 := by
    cases hh : B.isBigP j
    · have he : B.pickSig j=(B.R j)ᶜ := by simp [ActiveBank.pickSig,hh,ActiveBank.anchorSide]
      rw [he,hQ,hm]
      norm_num
    · have he : B.pickSig j=B.R j := by simp [ActiveBank.pickSig,hh,ActiveBank.anchorSide]
      rw [he,hP,hm]
      norm_num
  rw [measureReal_ennreal_smul_apply,hPick]
  norm_num

lemma ActiveBank.pick_meas (j : I) (b : Bool) : MeasurableSet (B.pick j b) := B.side_meas _ _
lemma ActiveBank.pickSig_meas (j : I) : MeasurableSet (B.pickSig j) := by
  unfold ActiveBank.pickSig
  generalize Bool.xor (B.isBigP j) true = b
  cases b
  · exact (B.meas j).2.2
  · exact (B.meas j).2.2.compl

lemma ActiveBank.pick_out (j : I) (b : Bool) : Disjoint A (B.pick j b) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (B.inside j (B.side_sub j _ hy)) hx

lemma ActiveBank.pick_cross (j : I) (b : Bool) :
    ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict (B.pick j b)),
      K.W z=(SparseHalfCountableEndpoint.side (B.pickSig j) b).indicator (fun _=>(1:ℝ)) z.1 := by
  rw [B.pick_sig_matches]
  exact B.cross_rect _ _

lemma ActiveBank.pick_zero (i j : I) (b c : Bool) (h : i=j → b=c) :
    ∀ᵐ z ∂(μ.restrict (B.pick i b)).prod (μ.restrict (B.pick j c)),K.W z=0 := by
  apply B.outside_zero
  intro e
  subst j
  rw [h rfl]

lemma ActiveBank.pick_disj (u v : I×Bool) (h : u≠v) :
    Disjoint (B.pick u.1 u.2) (B.pick v.1 v.2) := by
  refine (B.side_disj (i:=(u.1,Bool.xor (B.isBigP u.1) u.2)) (j:=(v.1,Bool.xor (B.isBigP v.1) v.2))) ?_
  intro he
  rcases u with ⟨i,b⟩
  rcases v with ⟨j,c⟩
  have hij : i=j := congrArg Prod.fst he
  subst j
  have hh : Bool.xor (B.isBigP i) b=Bool.xor (B.isBigP i) c := congrArg Prod.snd he
  have hbc : b=c := by cases he : B.isBigP i <;> simpa [he] using hh
  exact h (Prod.ext rfl hbc)

#print axioms ActiveBank.pick_cross
#print axioms ActiveBank.pickSig_mass
end SparseHalfGraphon
