import RibbonDerived3Algebra
import RibbonDerivedTwoClose

namespace RibbonStationaryWords
open Ribbon5Bridge HaarClass4Structure HaarUniversal36
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem derived_of_abel {g : G} (h : Abelianization.of g=1) : g∈LS G 1 := by
  change g∈(⊤ : Subgroup G).lowerCentralSeries 1
  rw [Subgroup.top_lowerCentralSeries_one,← Abelianization.ker_of]
  exact h

def w0 : Array P := #[0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,1,2,0,0,2,0,0,2,1,2,1,1,2,1,2]

private theorem free_0 (x y : G) :
    pathAt x y w0 32 = (false,(x*x*y) * ⁅(y*x⁻¹*x⁻¹*y⁻¹*x*x),(y⁻¹*x⁻¹*x⁻¹*y*y*x*x*y⁻¹)⁆ * (x*x*y)⁻¹) := by
  norm_num [pathAt,run,start,action,w0,commutatorElement_def] <;> group

private theorem residue_0 (x y : G) :
    (pathAt x y w0 32).2 ∈ RibbonDerived3.DLS G 1 := by
  have A : (y*x⁻¹*x⁻¹*y⁻¹*x*x) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (v*u⁻¹*u⁻¹*v⁻¹*u*u)=1
    calc
      _ = u*u*u⁻¹*u⁻¹*v*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have B : (y⁻¹*x⁻¹*x⁻¹*y*y*x*x*y⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (v⁻¹*u⁻¹*u⁻¹*v*v*u*u*v⁻¹)=1
    calc
      _ = u*u*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have H : ⁅(y*x⁻¹*x⁻¹*y⁻¹*x*x),(y⁻¹*x⁻¹*x⁻¹*y*y*x*x*y⁻¹)⁆ ∈ RibbonDerived3.DLS G 1 :=
    Subgroup.commutator_mem_commutator A B
  rw [free_0]
  exact (inferInstance : (RibbonDerived3.DLS G 1).Normal).conj_mem _ H _

def w1 : Array P := #[0,0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,1,2]

private theorem free_1 (x y : G) :
    pathAt x y w1 32 = (false,(x) * ⁅(x*y*y*x⁻¹*y⁻¹*y⁻¹),(x⁻¹*y*y*x*x*y⁻¹*y⁻¹*x⁻¹)⁆ * (x)⁻¹) := by
  norm_num [pathAt,run,start,action,w1,commutatorElement_def] <;> group

private theorem residue_1 (x y : G) :
    (pathAt x y w1 32).2 ∈ RibbonDerived3.DLS G 1 := by
  have A : (x*y*y*x⁻¹*y⁻¹*y⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u*v*v*u⁻¹*v⁻¹*v⁻¹)=1
    calc
      _ = u*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have B : (x⁻¹*y*y*x*x*y⁻¹*y⁻¹*x⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u⁻¹*v*v*u*u*v⁻¹*v⁻¹*u⁻¹)=1
    calc
      _ = u*u*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have H : ⁅(x*y*y*x⁻¹*y⁻¹*y⁻¹),(x⁻¹*y*y*x*x*y⁻¹*y⁻¹*x⁻¹)⁆ ∈ RibbonDerived3.DLS G 1 :=
    Subgroup.commutator_mem_commutator A B
  rw [free_1]
  exact (inferInstance : (RibbonDerived3.DLS G 1).Normal).conj_mem _ H _

def w2 : Array P := #[0,0,2,0,0,2,1,2,1,1,2,1,2,0,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,1,2]

private theorem free_2 (x y : G) :
    pathAt x y w2 32 = (false,(x) * ⁅(x*y*y*x⁻¹*y⁻¹*y⁻¹),(x⁻¹*y*x*y*x*y⁻¹*y⁻¹*x⁻¹)⁆ * (x)⁻¹) := by
  norm_num [pathAt,run,start,action,w2,commutatorElement_def] <;> group

private theorem residue_2 (x y : G) :
    (pathAt x y w2 32).2 ∈ RibbonDerived3.DLS G 1 := by
  have A : (x*y*y*x⁻¹*y⁻¹*y⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u*v*v*u⁻¹*v⁻¹*v⁻¹)=1
    calc
      _ = u*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have B : (x⁻¹*y*x*y*x*y⁻¹*y⁻¹*x⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u⁻¹*v*u*v*u*v⁻¹*v⁻¹*u⁻¹)=1
    calc
      _ = u*u*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have H : ⁅(x*y*y*x⁻¹*y⁻¹*y⁻¹),(x⁻¹*y*x*y*x*y⁻¹*y⁻¹*x⁻¹)⁆ ∈ RibbonDerived3.DLS G 1 :=
    Subgroup.commutator_mem_commutator A B
  rw [free_2]
  exact (inferInstance : (RibbonDerived3.DLS G 1).Normal).conj_mem _ H _

def w3 : Array P := #[0,0,2,0,2,1,1,2,0,2,0,2,1,2,0,2,1,2,1,1,2,0,2,0,2,0,2,1,2,1,1,2]

private theorem free_3 (x y : G) :
    pathAt x y w3 32 = (false,(x*x*y*x⁻¹) * ⁅(x⁻¹*y*x*y⁻¹),(x*y⁻¹*x⁻¹*x⁻¹*y*x)⁆ * (x*x*y*x⁻¹)⁻¹) := by
  norm_num [pathAt,run,start,action,w3,commutatorElement_def] <;> group

private theorem residue_3 (x y : G) :
    (pathAt x y w3 32).2 ∈ RibbonDerived3.DLS G 1 := by
  have A : (x⁻¹*y*x*y⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u⁻¹*v*u*v⁻¹)=1
    calc
      _ = u*u⁻¹*v*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have B : (x*y⁻¹*x⁻¹*x⁻¹*y*x) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u*v⁻¹*u⁻¹*u⁻¹*v*u)=1
    calc
      _ = u*u*u⁻¹*u⁻¹*v*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have H : ⁅(x⁻¹*y*x*y⁻¹),(x*y⁻¹*x⁻¹*x⁻¹*y*x)⁆ ∈ RibbonDerived3.DLS G 1 :=
    Subgroup.commutator_mem_commutator A B
  rw [free_3]
  exact (inferInstance : (RibbonDerived3.DLS G 1).Normal).conj_mem _ H _

def wlong0 : Array P := #[0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,1,2,0,0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,2,1,1,2,0,2,0,0,2,1,1,2,1,1,2,0,2,0,0,2,0,2,1,1,2,1,1,2]

private theorem actual_0 (x y : G) : pathAt x y wlong0 64 =
    (false,(pathAt x y w0 32).2 * ((x*x*y*y*x⁻¹*x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*x⁻¹)⁻¹*(pathAt x y w0 32).2*(x*x*y*y*x⁻¹*x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*x⁻¹))⁻¹) := by
  norm_num [pathAt,run,start,action,wlong0,w0] <;> group

private theorem bmem_0 (x y : G) : (x*x*y*y*x⁻¹*x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*x⁻¹) ∈ LS G 1 := by
  apply derived_of_abel
  simp only [map_mul,map_inv]
  let u := Abelianization.of x
  let v := Abelianization.of y
  change (u*u*v*v*u⁻¹*u⁻¹*v⁻¹*u*u*v⁻¹*u⁻¹*u⁻¹)=1
  calc
    _ = u*u*u*u*u⁻¹*u⁻¹*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
    _ = 1 := by group

def wlong1 : Array P := #[0,0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,1,2,0,2,0,0,2,0,2,1,1,2,1,1,2,0,0,2,0,2,1,1,2,0,2,0,0,2,1,1,2,1,1,2]

private theorem actual_1 (x y : G) : pathAt x y wlong1 64 =
    (false,(pathAt x y w1 32).2 * ((x*x*y*y*x⁻¹*y⁻¹*y⁻¹*x⁻¹)⁻¹*(pathAt x y w1 32).2*(x*x*y*y*x⁻¹*y⁻¹*y⁻¹*x⁻¹))⁻¹) := by
  norm_num [pathAt,run,start,action,wlong1,w1] <;> group

private theorem bmem_1 (x y : G) : (x*x*y*y*x⁻¹*y⁻¹*y⁻¹*x⁻¹) ∈ LS G 1 := by
  apply derived_of_abel
  simp only [map_mul,map_inv]
  let u := Abelianization.of x
  let v := Abelianization.of y
  change (u*u*v*v*u⁻¹*v⁻¹*v⁻¹*u⁻¹)=1
  calc
    _ = u*u*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
    _ = 1 := by group

def wlong2 : Array P := #[0,0,2,0,0,2,1,2,1,1,2,1,2,0,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,1,2,0,2,0,0,2,0,2,1,1,2,1,1,2,0,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,1,2]

private theorem actual_2 (x y : G) : pathAt x y wlong2 64 =
    (false,(pathAt x y w2 32).2 * ((x*x*y*y*x⁻¹*y⁻¹*y⁻¹*x⁻¹)⁻¹*(pathAt x y w2 32).2*(x*x*y*y*x⁻¹*y⁻¹*y⁻¹*x⁻¹))⁻¹) := by
  norm_num [pathAt,run,start,action,wlong2,w2] <;> group

private theorem bmem_2 (x y : G) : (x*x*y*y*x⁻¹*y⁻¹*y⁻¹*x⁻¹) ∈ LS G 1 := by
  apply derived_of_abel
  simp only [map_mul,map_inv]
  let u := Abelianization.of x
  let v := Abelianization.of y
  change (u*u*v*v*u⁻¹*v⁻¹*v⁻¹*u⁻¹)=1
  calc
    _ = u*u*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
    _ = 1 := by group

def wlong3 : Array P := #[0,0,2,0,2,1,1,2,0,2,0,2,1,2,0,2,1,2,1,1,2,0,2,0,2,0,2,1,2,1,1,2,0,0,2,0,2,1,2,0,2,1,2,1,2,0,0,2,1,2,1,1,2,0,0,2,0,2,1,2,1,2,1,2]

private theorem actual_3 (x y : G) : pathAt x y wlong3 64 =
    (false,(pathAt x y w3 32).2 * ((x*x*y*x⁻¹*x⁻¹*y*x*y⁻¹*x*y⁻¹*x⁻¹*x⁻¹)⁻¹*(pathAt x y w3 32).2*(x*x*y*x⁻¹*x⁻¹*y*x*y⁻¹*x*y⁻¹*x⁻¹*x⁻¹))⁻¹) := by
  norm_num [pathAt,run,start,action,wlong3,w3] <;> group

private theorem bmem_3 (x y : G) : (x*x*y*x⁻¹*x⁻¹*y*x*y⁻¹*x*y⁻¹*x⁻¹*x⁻¹) ∈ LS G 1 := by
  apply derived_of_abel
  simp only [map_mul,map_inv]
  let u := Abelianization.of x
  let v := Abelianization.of y
  change (u*u*v*u⁻¹*u⁻¹*v*u*v⁻¹*u*v⁻¹*u⁻¹*u⁻¹)=1
  calc
    _ = u*u*u*u*u⁻¹*u⁻¹*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
    _ = 1 := by group

theorem conj_of_commute {g z : G} (h : Commute g z) : z⁻¹*g*z=g := by
  rw [mul_assoc,h.eq,inv_mul_cancel_left]

theorem central (m : RibbonDerivedTwo.D2 G) {g z : G}
    (hg : g ∈ RibbonDerived3.DLS G 1) (hz : z ∈ LS G 1) : Commute g z := by
  have H : RibbonDerived3.DLS G 1 ≤ Subgroup.centralizer ({z}:Set G) := by
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr (m a ha b hb z hz).eq
  exact Subgroup.mem_centralizer_singleton_iff.mp (H hg)

theorem long_close_0 (m : RibbonDerivedTwo.D2 G) (x y : G) :
    pathAt x y wlong0 64 = pathAt x y wlong0 0 := by
  have h := conj_of_commute (central m (residue_0 x y) (bmem_0 x y))
  rw [actual_0,h,mul_inv_cancel]
  rfl

theorem long_close_1 (m : RibbonDerivedTwo.D2 G) (x y : G) :
    pathAt x y wlong1 64 = pathAt x y wlong1 0 := by
  have h := conj_of_commute (central m (residue_1 x y) (bmem_1 x y))
  rw [actual_1,h,mul_inv_cancel]
  rfl

theorem long_close_2 (m : RibbonDerivedTwo.D2 G) (x y : G) :
    pathAt x y wlong2 64 = pathAt x y wlong2 0 := by
  have h := conj_of_commute (central m (residue_2 x y) (bmem_2 x y))
  rw [actual_2,h,mul_inv_cancel]
  rfl

theorem long_close_3 (m : RibbonDerivedTwo.D2 G) (x y : G) :
    pathAt x y wlong3 64 = pathAt x y wlong3 0 := by
  have h := conj_of_commute (central m (residue_3 x y) (bmem_3 x y))
  rw [actual_3,h,mul_inv_cancel]
  rfl

end RibbonStationaryWords
#print axioms RibbonStationaryWords.long_close_0
