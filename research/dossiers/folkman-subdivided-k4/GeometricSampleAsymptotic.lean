import GeometricGridResolution
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace RobustFolkman.GeometricGap
open Filter Asymptotics
open scoped Topology

theorem exp_logsquare_sub_rpow_tends_zero (C a η : ℝ) (ap : 0<a) (ep : 0<η) :
    Tendsto (fun x : ℝ => Real.exp (C*(Real.log x)^2-a*x^η)) atTop (𝓝 0) := by
  have h : (fun x : ℝ => C*(Real.log x)^2) =o[atTop] (fun x : ℝ => x^η) := by
    have e := isLittleO_log_rpow_rpow_atTop (2:ℝ) ep
    simp only [Real.rpow_two] at e
    exact e.const_mul_left C
  have small : ∀ᶠ x : ℝ in atTop, C*(Real.log x)^2≤(a/2)*x^η := by
    filter_upwards [h.bound (show 0<a/2 by positivity),eventually_ge_atTop (0:ℝ)] with x hx x0
    change ‖C*(Real.log x)^2‖≤a/2*‖x^η‖ at hx
    rw [Real.norm_eq_abs,Real.norm_of_nonneg (Real.rpow_nonneg x0 _)] at hx
    exact (le_abs_self _).trans hx
  have t : Tendsto (fun x : ℝ => -(a/2)*x^η) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (show -(a/2)<0 by linarith only [ap])).2 (tendsto_rpow_atTop ep)
  apply Real.tendsto_exp_atBot.comp
  exact tendsto_atBot_mono' atTop (small.mono (fun x hx => by linarith only [hx])) t

/-- Uniform scalar envelope for the finite-sample tail. Its dimension
may grow logarithmically and its expected degree only polynomially. -/
theorem spherical_tail_eventually_small (C c η ε : ℝ) (C0 : 0<C) (cp : 0<c)
    (ep : 0<η) (εp : 0<ε) :
    ∃ H : ℝ, Real.exp 1≤H ∧ ∀ N≥H, ∀ n L : ℕ, ∀ q : ℝ,
      (n:ℝ)≤C*Real.log N → (L:ℝ)≤N → 1/(8*(2:ℝ)^n)≤q →
      c*N^η≤(L:ℝ)*q →
      let D := Fintype.card (GridCode (n+3) (gridResolution n 20))
      ((2*(D:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000))/(q/100) +
        (L:ℝ)*Real.exp (-(L:ℝ)*q/1000) ≤ ε := by
  let A := (C+3)*(4*C+34)+2*C+2
  have A0 : 0<A := by dsimp [A]; positivity
  have lim := exp_logsquare_sub_rpow_tends_zero A (c/1000000) η (by positivity) ep
  have hw : ∀ᶠ x : ℝ in atTop,
      Real.exp (A*(Real.log x)^2-(c/1000000)*x^η)<ε/4001 :=
    lim.eventually (gt_mem_nhds (show (0:ℝ)<ε/4001 by positivity))
  obtain ⟨H,hH⟩ := eventually_atTop.1 hw
  refine ⟨max (Real.exp 1) H,le_max_left _ _,?_⟩
  intro N NH n L q nB LB qB day D
  have e1 : Real.exp 1≤N := (le_max_left _ _).trans NH
  have Np : 0<N := (Real.exp_pos _).trans_le e1
  let y := Real.log N
  have y1 : 1≤y := by
    have h := Real.log_le_log (Real.exp_pos 1) e1
    rwa [Real.log_exp] at h
  have y2 : y≤y^2 := by nlinarith only [mul_nonneg (by linarith only [y1] : 0≤y) (sub_nonneg.mpr y1)]
  have l2 : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
    norm_num at h
    exact h
  have l0 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have Dexp : (D:ℝ)≤Real.exp (((C+3)*(4*C+34))*y^2) := by
    have dl := grid_log_card_bound n 20
    change Real.log (D:ℝ)≤_ at dl
    have f : ((n+3:ℕ):ℝ)≤(C+3)*y := by
      push_cast
      change (n:ℝ)+3 ≤ _
      nlinarith only [nB,y1]
    have g : ((20+4*n+14:ℕ):ℝ)≤(4*C+34)*y := by
      push_cast
      change 20+4*(n:ℝ)+14 ≤ _
      nlinarith only [nB,y1]
    have z := mul_le_mul f g (by positivity) (by positivity : 0≤(C+3)*y)
    have zl := mul_le_mul z l2 l0 (by positivity : 0≤((C+3)*y)*((4*C+34)*y))
    have dp : 0<(D:ℝ) := by dsimp [D]; exact_mod_cast Fintype.card_pos (α:=GridCode (n+3) (gridResolution n 20))
    rw [←Real.exp_log dp]
    apply Real.exp_le_exp.2
    exact dl.trans (zl.trans_eq (by ring))
  have qi : 1/q≤8*Real.exp (C*y) := by
    have qp : 0<q := (by positivity : 0<1/(8*(2:ℝ)^n)).trans_le qB
    have h := one_div_le_one_div_of_le (by positivity : 0<1/(8*(2:ℝ)^n)) qB
    rw [one_div_one_div] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    rw [←Real.exp_log (by norm_num : 0<(2:ℝ)),←Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    exact (mul_le_of_le_one_right (Nat.cast_nonneg n) l2).trans nB
  let U := (C+3)*(4*C+34)*y^2
  let V := C*y
  let T := -(c/1000000)*N^η
  have f : (2*(D:ℝ)+3*(L:ℝ))≤5*Real.exp U := by
    have LL : (L:ℝ)≤Real.exp U := LB.trans (by
      have cn : 1≤(C+3)*(4*C+34) := by nlinarith only [C0,sq_nonneg C]
      have hn : y≤U := y2.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right cn (sq_nonneg y))
      calc
        N = Real.exp y := (Real.exp_log Np).symm
        _ ≤ _ := Real.exp_le_exp.2 hn)
    linarith only [Dexp,LL]
  have su : U+V≤A*y^2 := by
    dsimp [U,V,A]
    have h := mul_le_mul_of_nonneg_left y2 C0.le
    have z := mul_nonneg C0.le (sq_nonneg y)
    nlinarith only [h,sq_nonneg y,z]
  have sy : y≤A*y^2 := by
    have h : 1≤A := by dsimp [A]; nlinarith only [C0,sq_nonneg C]
    exact y2.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h (sq_nonneg y))
  have ex1 : Real.exp (-(L:ℝ)*q/1000000)≤Real.exp T :=
    Real.exp_le_exp.2 (by dsimp [T]; linarith only [day])
  have ex2 : Real.exp (-(L:ℝ)*q/1000)≤Real.exp T :=
    Real.exp_le_exp.2 (by
      dsimp [T]
      have w := mul_nonneg cp.le (Real.rpow_nonneg Np.le η)
      linarith only [day,w])
  have Nexp : N=Real.exp y := (Real.exp_log Np).symm
  have qp : 0<q := (by positivity : 0<1/(8*(2:ℝ)^n)).trans_le qB
  have f1 : ((2*(D:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000))/(q/100) ≤
      4000*Real.exp (A*y^2+T) := by
    have h := mul_le_mul f ex1 (Real.exp_nonneg _) (by positivity)
    have hh := mul_le_mul h (mul_le_mul_of_nonneg_left qi (by norm_num))
      (by positivity : 0≤100*(1/q)) (by positivity)
    calc
      _ = ((2*(D:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000))*(100*(1/q)) := by ring
      _ ≤ (5*Real.exp U*Real.exp T)*(100*(8*Real.exp V)) := hh
      _ = 4000*Real.exp (U+V+T) := by rw [Real.exp_add,Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (add_le_add_left su _)) (by norm_num)
  have f2 : (L:ℝ)*Real.exp (-(L:ℝ)*q/1000)≤Real.exp (A*y^2+T) := by
    have h := mul_le_mul LB ex2 (Real.exp_nonneg _) Np.le
    rw [Nexp,←Real.exp_add] at h
    exact h.trans (Real.exp_le_exp.2 (add_le_add_left sy _))
  have ht := hH N ((le_max_right _ _).trans NH)
  have hEq : A*y^2+T=A*(Real.log N)^2-(c/1000000)*N^η := by dsimp [T,y]; ring
  rw [←hEq] at ht
  linarith only [f1,f2,ht]

#print axioms exp_logsquare_sub_rpow_tends_zero
#print axioms spherical_tail_eventually_small
end RobustFolkman.GeometricGap
