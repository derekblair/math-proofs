import RibbonMetaHeadline

namespace RibbonAffine
open Ribbon5Bridge HaarClass4Structure RibbonMeta
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem derived_of_abel {g : G} (h : Abelianization.of g=1) : g∈LS G 1 := by
  change g∈(⊤ : Subgroup G).lowerCentralSeries 1
  rw [Subgroup.top_lowerCentralSeries_one,← Abelianization.ker_of]
  exact h

def w0 : Array P := #[0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,1,2,0,0,2,0,0,2,1,2,1,1,2,1,2]

private theorem free_0 (x y : G) :
    pathAt x y w0 32 = (false,(x*x*y) * ⁅(y*x⁻¹*x⁻¹*y⁻¹*x*x),(y⁻¹*x⁻¹*x⁻¹*y*y*x*x*y⁻¹)⁆ * (x*x*y)⁻¹) := by
  norm_num [pathAt,run,start,action,w0,commutatorElement_def] <;> group

private theorem close_0 (m : Meta G) (x y : G) :
    pathAt x y w0 32 = pathAt x y w0 0 := by
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
  rw [free_0,(m _ A _ B).commutator_eq,mul_one,mul_inv_cancel]
  rfl

def w1 : Array P := #[0,0,2,0,2,1,2,1,2,1,2,0,0,2,0,2,1,2,0,2,1,2,1,2,0,0,2,1,2,1,1,2]

private theorem free_1 (x y : G) :
    pathAt x y w1 32 = (false,(x) * ⁅(x*y*x⁻¹*y⁻¹),(x⁻¹*y*y*x*y⁻¹*x*y⁻¹*x⁻¹)⁆ * (x)⁻¹) := by
  norm_num [pathAt,run,start,action,w1,commutatorElement_def] <;> group

private theorem close_1 (m : Meta G) (x y : G) :
    pathAt x y w1 32 = pathAt x y w1 0 := by
  have A : (x*y*x⁻¹*y⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u*v*u⁻¹*v⁻¹)=1
    calc
      _ = u*u⁻¹*v*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have B : (x⁻¹*y*y*x*y⁻¹*x*y⁻¹*x⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u⁻¹*v*v*u*v⁻¹*u*v⁻¹*u⁻¹)=1
    calc
      _ = u*u*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
      _ = 1 := by group
  rw [free_1,(m _ A _ B).commutator_eq,mul_one,mul_inv_cancel]
  rfl

def w2 : Array P := #[0,0,2,1,1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2]

private theorem free_2 (x y : G) :
    pathAt x y w2 32 = (false,(x) * ⁅(x*y⁻¹*y⁻¹*x⁻¹*y*y),(x⁻¹*y⁻¹*x*y⁻¹*x*y*y*x⁻¹)⁆ * (x)⁻¹) := by
  norm_num [pathAt,run,start,action,w2,commutatorElement_def] <;> group

private theorem close_2 (m : Meta G) (x y : G) :
    pathAt x y w2 32 = pathAt x y w2 0 := by
  have A : (x*y⁻¹*y⁻¹*x⁻¹*y*y) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u*v⁻¹*v⁻¹*u⁻¹*v*v)=1
    calc
      _ = u*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have B : (x⁻¹*y⁻¹*x*y⁻¹*x*y*y*x⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u⁻¹*v⁻¹*u*v⁻¹*u*v*v*u⁻¹)=1
    calc
      _ = u*u*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
      _ = 1 := by group
  rw [free_2,(m _ A _ B).commutator_eq,mul_one,mul_inv_cancel]
  rfl

def w3 : Array P := #[0,0,2,0,0,2,1,2,1,1,2,1,2,0,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,1,2]

private theorem free_3 (x y : G) :
    pathAt x y w3 32 = (false,(x) * ⁅(x*y*y*x⁻¹*y⁻¹*y⁻¹),(x⁻¹*y*x*y*x*y⁻¹*y⁻¹*x⁻¹)⁆ * (x)⁻¹) := by
  norm_num [pathAt,run,start,action,w3,commutatorElement_def] <;> group

private theorem close_3 (m : Meta G) (x y : G) :
    pathAt x y w3 32 = pathAt x y w3 0 := by
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
  rw [free_3,(m _ A _ B).commutator_eq,mul_one,mul_inv_cancel]
  rfl

def w4 : Array P := #[0,0,2,0,0,2,1,2,1,2,0,2,1,2,1,1,2,0,2,0,2,0,2,0,2,1,2,1,1,2,1,2]

private theorem free_4 (x y : G) :
    pathAt x y w4 32 = (false,(x*x*y) * ⁅(y*x⁻¹*y⁻¹*x),(y⁻¹*x⁻¹*x⁻¹*y*x*y*x*y⁻¹)⁆ * (x*x*y)⁻¹) := by
  norm_num [pathAt,run,start,action,w4,commutatorElement_def] <;> group

private theorem close_4 (m : Meta G) (x y : G) :
    pathAt x y w4 32 = pathAt x y w4 0 := by
  have A : (y*x⁻¹*y⁻¹*x) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (v*u⁻¹*v⁻¹*u)=1
    calc
      _ = u*u⁻¹*v*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have B : (y⁻¹*x⁻¹*x⁻¹*y*x*y*x*y⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (v⁻¹*u⁻¹*u⁻¹*v*u*v*u*v⁻¹)=1
    calc
      _ = u*u*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
      _ = 1 := by group
  rw [free_4,(m _ A _ B).commutator_eq,mul_one,mul_inv_cancel]
  rfl

def w5 : Array P := #[0,0,2,0,2,1,1,2,0,2,0,2,1,2,0,2,1,2,1,1,2,0,2,0,2,0,2,1,2,1,1,2]

private theorem free_5 (x y : G) :
    pathAt x y w5 32 = (false,(x*x*y*x⁻¹) * ⁅(x⁻¹*y*x*y⁻¹),(x*y⁻¹*x⁻¹*x⁻¹*y*x)⁆ * (x*x*y*x⁻¹)⁻¹) := by
  norm_num [pathAt,run,start,action,w5,commutatorElement_def] <;> group

private theorem close_5 (m : Meta G) (x y : G) :
    pathAt x y w5 32 = pathAt x y w5 0 := by
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
  rw [free_5,(m _ A _ B).commutator_eq,mul_one,mul_inv_cancel]
  rfl

def w6 : Array P := #[0,0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,1,2]

private theorem free_6 (x y : G) :
    pathAt x y w6 32 = (false,(x) * ⁅(x*y*y*x⁻¹*y⁻¹*y⁻¹),(x⁻¹*y*y*x*x*y⁻¹*y⁻¹*x⁻¹)⁆ * (x)⁻¹) := by
  norm_num [pathAt,run,start,action,w6,commutatorElement_def] <;> group

private theorem close_6 (m : Meta G) (x y : G) :
    pathAt x y w6 32 = pathAt x y w6 0 := by
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
  rw [free_6,(m _ A _ B).commutator_eq,mul_one,mul_inv_cancel]
  rfl

def w7 : Array P := #[0,0,2,1,2,1,2,0,2,1,2,1,1,2,0,2,0,2,0,2,0,2,1,2,1,1,2,1,2,0,0,2]

private theorem free_7 (x y : G) :
    pathAt x y w7 32 = (false,(x) * ⁅(x*y⁻¹*x⁻¹*y),(x⁻¹*y⁻¹*y⁻¹*x*y*x*y*x⁻¹)⁆ * (x)⁻¹) := by
  norm_num [pathAt,run,start,action,w7,commutatorElement_def] <;> group

private theorem close_7 (m : Meta G) (x y : G) :
    pathAt x y w7 32 = pathAt x y w7 0 := by
  have A : (x*y⁻¹*x⁻¹*y) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u*v⁻¹*u⁻¹*v)=1
    calc
      _ = u*u⁻¹*v*v⁻¹ := by ac_rfl
      _ = 1 := by group
  have B : (x⁻¹*y⁻¹*y⁻¹*x*y*x*y*x⁻¹) ∈ LS G 1 := by
    apply derived_of_abel
    simp only [map_mul,map_inv]
    let u := Abelianization.of x
    let v := Abelianization.of y
    change (u⁻¹*v⁻¹*v⁻¹*u*v*u*v*u⁻¹)=1
    calc
      _ = u*u*u⁻¹*u⁻¹*v*v*v⁻¹*v⁻¹ := by ac_rfl
      _ = 1 := by group
  rw [free_7,(m _ A _ B).commutator_eq,mul_one,mul_inv_cancel]
  rfl

def word : Fin 8 → Array P := ![w0,w1,w2,w3,w4,w5,w6,w7]
theorem size_word (k : Fin 8) : (word k).size=32 := by fin_cases k <;> decide
theorem close_word (m : Meta G) (x y : G) (k : Fin 8) :
    pathAt x y (word k) 32=pathAt x y (word k) 0 := by
  fin_cases k
  · exact close_0 m x y
  · exact close_1 m x y
  · exact close_2 m x y
  · exact close_3 m x y
  · exact close_4 m x y
  · exact close_5 m x y
  · exact close_6 m x y
  · exact close_7 m x y

end RibbonAffine
#print axioms RibbonAffine.close_word
