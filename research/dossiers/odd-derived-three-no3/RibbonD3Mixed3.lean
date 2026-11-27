import RibbonD3Mixed3Check
namespace RibbonD3Mixed3
open Ribbon5Bridge RibbonD3WordSelection RibbonD3Low RibbonD3PortEval RibbonAffine
open RibbonDerived3 HaarClass4Structure HaarClass4Ports RibbonClass4Fallback
variable {G K : Type*} [Group G] [Field K]

def F (k t : Fin 3) (a b : K) : K :=
  if t.val = 0 then 1 else
  if k.val = 0 then (if t.val = 1 then a*b+a+b else a*b-2*a+b) else
  if k.val = 1 then (if t.val = 1 then 2*a*b-a-1 else a*b+a+1) else
  if t.val = 1 then a*b+b-2 else a*b+b+1

private theorem evalF (k t : Fin 3) (a b : Kˣ) :
    pl a b (fmono k t) = F k t (a:K) (b:K) := by
  fin_cases k <;> fin_cases t <;>
    norm_num [fmono,F,pl,mon,Units.val_mul,zpow_ofNat,Units.val_pow_eq_pow_val] <;> ring

theorem factor_nonzero (k : Fin 3) (a b : Kˣ) (pivot : (a:K) ≠ 1)
    (h3 : (3:K) ≠ 0) (nz : ∀ t, F k t (a:K) (b:K) ≠ 0)
    (i j : Nat) (h : covers k i j = true) :
    pl a b (reps k)[i]!.tr ≠ pl a b (reps k)[j]!.tr := by
  obtain ⟨m,hm,P⟩ := Array.any_eq_true.mp h
  simp only [Bool.and_eq_true_iff,beq_iff_eq] at P
  have T := Array.all_eq_true.mp (checks k) m hm
  generalize hf : (factors k)[m] = f at P T
  obtain ⟨I,J,u,v,c,t⟩ := f
  change I = i ∧ J = j at P
  obtain ⟨rfl,rfl⟩ := P
  change check k (I,J,u,v,c,t) = true at T
  simp only [check,Bool.and_eq_true_iff,decide_eq_true_eq] at T
  have E := poly_eq a b _ _ T.2
  rw [pl_append,negative_sound,←sub_eq_add_neg,pl_mul,pl_mul,evalF] at E
  have delta : pl a b [(1,0,1),(0,0,-1)] = (a:K)-1 := by
    norm_num [pl,mon,Units.val_mul,zpow_ofNat,Units.val_pow_eq_pow_val]
    ring
  have hC : (c:K) ≠ 0 := by
    rcases T.1 with rfl|rfl|rfl|rfl <;> norm_num [h3]
  have non : pl a b [(u,v,c)] ≠ 0 := by
    simpa [pl,mon,Units.val_mul] using
      mul_ne_zero hC (mul_ne_zero (Units.ne_zero (a^u)) (Units.ne_zero (b^v)))
  rw [delta] at E
  intro Q
  rw [Q,sub_self] at E
  exact (mul_ne_zero (mul_ne_zero non (sub_ne_zero.mpr pivot)) (nz t)) E.symm

theorem chart_cycle (k : Fin 3) (d3 : DLS G 3 = ⊥) (x y : G)
    (p : orderOf (QuotientGroup.mk' (LS G 2) (portC x y)) = 3)
    (μ : G →* Kˣ) (τ : G → K) (co : RibbonStationaryChart.Aff μ τ)
    (pivot : (μ x:K) ≠ 1) (h3 : (3:K) ≠ 0)
    (nz : ∀ t, F k t (μ x:K) (μ y:K) ≠ 0)
    (tx : τ x=0) (ty : τ y=1) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  apply RibbonD3ChartCycles.from_chart d3 x y (k3 k)
  intro i j e
  have pi := position k i
  have pj := position k j
  have D : smallGaps 3 (k3 k) i.val j.val := by
    have A := pi.1
    have B := pj.1
    unfold inside at A B
    unfold smallGaps
    dsimp only at A B
    omega
  have U := lowKey_eq x y (k3 k) p D e
  have HT := congrArg (fun q => (((bank k).find? fun r => r.1 == q).map Prod.snd).getD []) U
  change tags k (low (k3 k) i.val) = tags k (low (k3 k) j.val) at HT
  have hi := pi.2
  have hj := pj.2
  rw [←HT] at hj
  have si := ((RibbonD3Field.charts_shape (k3 k)).2.2 i).2
  have sj := ((RibbonD3Field.charts_shape (k3 k)).2.2 j).2
  change (reps k)[(mp k)[i.val]!]! = _ at si
  change (reps k)[(mp k)[j.val]!]! = _ at sj
  by_cases N : (mp k)[i.val]! = (mp k)[j.val]!
  · rw [←si,←sj,N]
  · have vv := RibbonD3FieldPoint.affine_collision μ τ co x y tx ty (k3 k) i.val j.val e
    rw [←RibbonD3Field.label_eval _ _ (RibbonD3Field.raw (RibbonD3Field.chart (k3 k)) i.val),
      ←RibbonD3Field.label_eval _ _ (RibbonD3Field.raw (RibbonD3Field.chart (k3 k)) j.val),←si,←sj] at vv
    have eqv := congrArg (fun x : Bool × Kˣ × K => x.2.2) vv
    change pl (μ x) (μ y) (reps k)[(mp k)[i.val]!]!.tr =
        pl (μ x) (μ y) (reps k)[(mp k)[j.val]!]!.tr at eqv
    exfalso
    rcases lt_or_gt_of_ne N with I|J
    · exact factor_nonzero k _ _ pivot h3 nz _ _ (withinTag k _ _ _ hi hj I) eqv
    · exact factor_nonzero k _ _ pivot h3 nz _ _ (withinTag k _ _ _ hj hi J) eqv.symm

private theorem select (a b : K) (ha : a ≠ 1) (h2 : (2:K) ≠ 0) (h3 : (3:K) ≠ 0) :
    ∃ k : Fin 3, ∀ t : Fin 3, F k t a b ≠ 0 := by
  by_contra! H
  have h0 : a*b+a+b=0 ∨ a*b-2*a+b=0 := by
    obtain ⟨s,hs⟩ := H 0
    fin_cases s <;> simp_all [F]
  have h4 : a*b+b-2=0 ∨ a*b+b+1=0 := by
    obtain ⟨s,hs⟩ := H 2
    fin_cases s <;> simp_all [F]
  have h1 : 2*a*b-a-1=0 ∨ a*b+a+1=0 := by
    obtain ⟨s,hs⟩ := H 1
    fin_cases s <;> simp_all [F]
  rcases h0 with hs|hs <;> rcases h4 with ht|ht
  · have aa : a = -2 := by linear_combination hs-ht
    rw [aa] at ht h1
    have bb : b = -2 := by linear_combination -ht
    rw [bb] at h1
    rcases h1 with hw|hw
    · have h9 : (3:K)*(3:K)=0 := by linear_combination hw
      exact mul_ne_zero h3 h3 h9
    · apply h3
      linear_combination hw
  · exact ha (by linear_combination hs-ht)
  · have z : (2:K)*(a-1)=0 := by linear_combination ht-hs
    exact (mul_ne_zero h2 (sub_ne_zero.mpr ha)) z
  · have aa : 2*a+1=0 := by linear_combination ht-hs
    have bb : b = -2 := by linear_combination 2*ht-aa*b
    rw [bb] at h1
    rcases h1 with hw|hw
    · apply h3
      linear_combination 2*hw+5*aa
    · apply h3
      linear_combination 2*hw+aa

theorem projected_three_normalized (d3 : DLS G 3 = ⊥) (x y : G)
    (p : orderOf (QuotientGroup.mk' (LS G 2) (portC x y)) = 3)
    (μ : G →* Kˣ) (τ : G → K) (co : RibbonStationaryChart.Aff μ τ)
    (pivot : (μ x:K) ≠ 1) (h2 : (2:K) ≠ 0) (h3 : (3:K) ≠ 0)
    (tx : τ x=0) (ty : τ y=1) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  obtain ⟨k,nz⟩ := select (μ x:K) (μ y:K) pivot h2 h3
  exact chart_cycle k d3 x y p μ τ co pivot h3 nz tx ty

#print axioms projected_three_normalized
end RibbonD3Mixed3
