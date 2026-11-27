import GeometricPopulationPower
import GeometricUniformSphere
import GeometricHeightDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace RobustFolkman.GeometricGap
open MeasureTheory Finset WithLp
open scoped InnerProductSpace
abbrev GridSphere (d : ℕ) := UnitSphere (EuclideanSpace ℝ (Fin d))
abbrev GridCode (d m : ℕ) := Fin d → Fin (2*m+1)

theorem grid_coord_abs {d : ℕ} (x : GridSphere d) (i : Fin d) :
    |ofLp x.val i|≤1 := by
  have xn : ‖x.val‖=1 := by simpa using x.property
  have h := PiLp.norm_apply_le x.val i
  simpa [Real.norm_eq_abs,xn] using h

noncomputable def gridCode (d m : ℕ) (x : GridSphere d) (i : Fin d) : Fin (2*m+1) :=
  ⟨⌊(m:ℝ)*(ofLp x.val i+1)⌋₊, by
    have h : (m:ℝ)*(ofLp x.val i+1)≤((2*m:ℕ):ℝ) := by
      push_cast
      have u := mul_le_mul_of_nonneg_left (abs_le.mp (grid_coord_abs x i)).2 (show 0≤(m:ℝ) by positivity)
      nlinarith only [u]
    simpa only [Nat.floor_natCast,Nat.lt_succ_iff] using Nat.floor_le_floor h⟩

theorem gridCode_measurable (d m : ℕ) : Measurable (gridCode d m) := by
  apply Measurable.of_eval
  intro i
  have a : Measurable (fun x : GridSphere d => ofLp x.val i) :=
    ((measurable_pi_apply i).comp (PiLp.volume_preserving_ofLp (Fin d)).measurable).comp
      measurable_subtype_coe
  have f : Measurable (fun x : GridSphere d => ⌊(m:ℝ)*(ofLp x.val i+1)⌋₊) :=
    Nat.measurable_floor.comp (measurable_const.mul (a.add_const 1))
  apply measurable_to_countable'
  intro b
  have e : (fun x => gridCode d m x i) ⁻¹' {b} =
      (fun x : GridSphere d => ⌊(m:ℝ)*(ofLp x.val i+1)⌋₊) ⁻¹' {b.val} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    exact ⟨fun h => congrArg Fin.val h,fun h => Fin.ext h⟩
  rw [e]
  exact f (measurableSet_singleton _)

theorem grid_code_diameter (d m : ℕ) (mp : 0<m) (x y : GridSphere d)
    (eq : gridCode d m x=gridCode d m y) :
    ‖x.val-y.val‖≤Real.sqrt (d:ℝ)/(m:ℝ) := by
  have mm : 0<(m:ℝ) := by exact_mod_cast mp
  have b (i : Fin d) : |ofLp x.val i-ofLp y.val i|≤1/(m:ℝ) := by
    have f := congrArg (fun e : GridCode d m => (e i).val) eq
    let u := (m:ℝ)*(ofLp x.val i+1)
    let v := (m:ℝ)*(ofLp y.val i+1)
    change ⌊u⌋₊=⌊v⌋₊ at f
    have u0 : 0≤u := mul_nonneg mm.le
      (by linarith only [(abs_le.mp (grid_coord_abs x i)).1])
    have v0 : 0≤v := mul_nonneg mm.le
      (by linarith only [(abs_le.mp (grid_coord_abs y i)).1])
    have ul := Nat.floor_le u0
    have uh := Nat.lt_floor_add_one u
    have vl := Nat.floor_le v0
    have vh := Nat.lt_floor_add_one v
    rw [f] at ul uh
    apply abs_le.mpr
    constructor
    · apply (neg_le.mpr ((le_div_iff₀ mm).2 ?_))
      dsimp [u,v] at *
      nlinarith only [ul,vh]
    · apply (le_div_iff₀ mm).2
      dsimp [u,v] at *
      nlinarith only [vl,uh]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤Real.sqrt (d:ℝ)/(m:ℝ))).1
  rw [EuclideanSpace.real_norm_sq_eq,div_pow,Real.sq_sqrt (by positivity)]
  have b' (i : Fin d) : (ofLp (x.val-y.val) i)^2≤(1/(m:ℝ))^2 := by
    change (ofLp x.val i-ofLp y.val i)^2≤_
    rw [←sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (b i)
  calc
    _ ≤ ∑ _ : Fin d, (1/(m:ℝ))^2 := Finset.sum_le_sum (fun i _ => b' i)
    _ = _ := by simp [div_pow, div_eq_mul_inv]

#print axioms grid_code_diameter
end RobustFolkman.GeometricGap
