import Ribbon6Chart

namespace Ribbon6
open Ribbon5Bridge
variable {G : Type*} [Group G]
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

theorem mate_0 (x y : G) (nz : residue x y ≠ 1) :
    pathAt x y wc 0 ≠ pathAt x y wc 32 := by
  let k : G := 1
  have e : (pathAt x y wc 0).2⁻¹ * (pathAt x y wc 32).2 = k*(residue x y)*k⁻¹ := by
    norm_num [pathAt,run,start,action,wc,residue,U,V,k] <;> group
  intro h
  have e' : k*(residue x y)*k⁻¹=1 := by
    rw [← e, congrArg Prod.snd h, inv_mul_cancel]
  apply nz
  have h' := congrArg (fun g => k⁻¹*g*k) e'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at h' ⊢
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using h'

theorem mate_1 (x y : G) (nz : residue x y ≠ 1) :
    pathAt x y wc 1 ≠ pathAt x y wc 33 := by
  let k : G := 1
  have e : (pathAt x y wc 1).2⁻¹ * (pathAt x y wc 33).2 = k*(residue x y)*k⁻¹ := by
    norm_num [pathAt,run,start,action,wc,residue,U,V,k] <;> group
  intro h
  have e' : k*(residue x y)*k⁻¹=1 := by
    rw [← e, congrArg Prod.snd h, inv_mul_cancel]
  apply nz
  have h' := congrArg (fun g => k⁻¹*g*k) e'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at h' ⊢
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using h'

theorem mate_2 (x y : G) (nz : residue x y ≠ 1) :
    pathAt x y wc 2 ≠ pathAt x y wc 34 := by
  let k : G := y
  have e : (pathAt x y wc 2).2⁻¹ * (pathAt x y wc 34).2 = k*(residue x y)*k⁻¹ := by
    norm_num [pathAt,run,start,action,wc,residue,U,V,k] <;> group
  intro h
  have e' : k*(residue x y)*k⁻¹=1 := by
    rw [← e, congrArg Prod.snd h, inv_mul_cancel]
  apply nz
  have h' := congrArg (fun g => k⁻¹*g*k) e'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at h' ⊢
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using h'

theorem mate_3 (x y : G) (nz : residue x y ≠ 1) :
    pathAt x y wc 3 ≠ pathAt x y wc 35 := by
  let k : G := y
  have e : (pathAt x y wc 3).2⁻¹ * (pathAt x y wc 35).2 = k*(residue x y)*k⁻¹ := by
    norm_num [pathAt,run,start,action,wc,residue,U,V,k] <;> group
  intro h
  have e' : k*(residue x y)*k⁻¹=1 := by
    rw [← e, congrArg Prod.snd h, inv_mul_cancel]
  apply nz
  have h' := congrArg (fun g => k⁻¹*g*k) e'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at h' ⊢
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using h'

theorem mate_4 (x y : G) (nz : residue x y ≠ 1) :
    pathAt x y wc 4 ≠ pathAt x y wc 36 := by
  let k : G := x⁻¹*y
  have e : (pathAt x y wc 4).2⁻¹ * (pathAt x y wc 36).2 = k*(residue x y)*k⁻¹ := by
    norm_num [pathAt,run,start,action,wc,residue,U,V,k] <;> group
  intro h
  have e' : k*(residue x y)*k⁻¹=1 := by
    rw [← e, congrArg Prod.snd h, inv_mul_cancel]
  apply nz
  have h' := congrArg (fun g => k⁻¹*g*k) e'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at h' ⊢
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using h'

theorem mate_28 (x y : G) (nz : residue x y ≠ 1) :
    pathAt x y wc 28 ≠ pathAt x y wc 60 := by
  let k : G := x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹
  have e : (pathAt x y wc 28).2⁻¹ * (pathAt x y wc 60).2 = k*((residue x y)⁻¹)*k⁻¹ := by
    norm_num [pathAt,run,start,action,wc,residue,U,V,k] <;> group
  intro h
  have e' : k*((residue x y)⁻¹)*k⁻¹=1 := by
    rw [← e, congrArg Prod.snd h, inv_mul_cancel]
  apply nz
  apply inv_eq_one.mp
  have h' := congrArg (fun g => k⁻¹*g*k) e'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at h' ⊢
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using h'

theorem mate_29 (x y : G) (nz : residue x y ≠ 1) :
    pathAt x y wc 29 ≠ pathAt x y wc 61 := by
  let k : G := y⁻¹*x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹
  have e : (pathAt x y wc 29).2⁻¹ * (pathAt x y wc 61).2 = k*((residue x y)⁻¹)*k⁻¹ := by
    norm_num [pathAt,run,start,action,wc,residue,U,V,k] <;> group
  intro h
  have e' : k*((residue x y)⁻¹)*k⁻¹=1 := by
    rw [← e, congrArg Prod.snd h, inv_mul_cancel]
  apply nz
  apply inv_eq_one.mp
  have h' := congrArg (fun g => k⁻¹*g*k) e'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at h' ⊢
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using h'

theorem mate_30 (x y : G) (nz : residue x y ≠ 1) :
    pathAt x y wc 30 ≠ pathAt x y wc 62 := by
  let k : G := y⁻¹*x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹
  have e : (pathAt x y wc 30).2⁻¹ * (pathAt x y wc 62).2 = k*((residue x y)⁻¹)*k⁻¹ := by
    norm_num [pathAt,run,start,action,wc,residue,U,V,k] <;> group
  intro h
  have e' : k*((residue x y)⁻¹)*k⁻¹=1 := by
    rw [← e, congrArg Prod.snd h, inv_mul_cancel]
  apply nz
  apply inv_eq_one.mp
  have h' := congrArg (fun g => k⁻¹*g*k) e'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at h' ⊢
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using h'

theorem mate_31 (x y : G) (nz : residue x y ≠ 1) :
    pathAt x y wc 31 ≠ pathAt x y wc 63 := by
  let k : G := x*y⁻¹*x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹
  have e : (pathAt x y wc 31).2⁻¹ * (pathAt x y wc 63).2 = k*((residue x y)⁻¹)*k⁻¹ := by
    norm_num [pathAt,run,start,action,wc,residue,U,V,k] <;> group
  intro h
  have e' : k*((residue x y)⁻¹)*k⁻¹=1 := by
    rw [← e, congrArg Prod.snd h, inv_mul_cancel]
  apply nz
  apply inv_eq_one.mp
  have h' := congrArg (fun g => k⁻¹*g*k) e'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at h' ⊢
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using h'
theorem mate_sep (x y : G) (nz : residue x y ≠ 1) (i j : Nat) (m : same i j) :
    pathAt x y wc i ≠ pathAt x y wc j := by
  rcases m with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact mate_0 x y nz
  · exact mate_1 x y nz
  · exact mate_2 x y nz
  · exact mate_3 x y nz
  · exact mate_4 x y nz
  · exact mate_28 x y nz
  · exact mate_29 x y nz
  · exact mate_30 x y nz
  · exact mate_31 x y nz

end Ribbon6
