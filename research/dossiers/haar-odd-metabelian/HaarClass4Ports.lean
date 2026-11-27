import HaarClass4Data

namespace HaarClass4Ports

open scoped commutatorElement
open HaarClass4Data HaarClass4Structure HaarClass4Normal

variable {G : Type*} [Group G]

def portC (x y : G) := ⁅x⁻¹,y⁻¹⁆
def portU (x y : G) := ⁅portC x y,x⁆
def portV (x y : G) := ⁅portC x y,y⁆

theorem ports_xy (x y : G) : x*y=y*x*portC x y := by
  simp only [portC,commutatorElement_def,inv_inv]
  group

theorem next_layer {n : ℕ} {x : G} (hx : x∈LS G n) (y : G) :
    ⁅x,y⁆ ∈ LS G (n+1) :=
  Subgroup.commutator_mem_commutator hx (Subgroup.mem_top y)

theorem layer_c (x y : G) : portC x y ∈ LS G 1 := next_layer (Subgroup.mem_top x⁻¹) y⁻¹
theorem layer_u (x y : G) : portU x y ∈ LS G 2 := next_layer (layer_c x y) x
theorem layer_v (x y : G) : portV x y ∈ LS G 2 := next_layer (layer_c x y) y

def make (h : LS G 4=⊥) (x y : G) : Data G := by
  let c := portC x y
  let u := portU x y
  let v := portV x y
  let a := ⁅u,x⁆
  let b := ⁅u,y⁆
  let b' := ⁅v,x⁆
  let d := ⁅v,y⁆
  have hcu : Commute c u := comm_of_layers h (layer_c x y) (layer_u x y)
  have hcv : Commute c v := comm_of_layers h (layer_c x y) (layer_v x y)
  have huv : Commute u v := layer3_comm h (layer_u x y) (layer_v x y)
  have ha := center_in_layer4 h (next_layer (layer_u x y) x)
  have hb := center_in_layer4 h (next_layer (layer_u x y) y)
  have hb' := center_in_layer4 h (next_layer (layer_v x y) x)
  have hd := center_in_layer4 h (next_layer (layer_v x y) y)
  have ux : u*x=x*u*a := right_of_left rfl ha
  have uy : u*y=y*u*b := right_of_left rfl hb
  have vx : v*x=x*v*b' := right_of_left rfl hb'
  have vy : v*y=y*v*d := right_of_left rfl hd
  have cx : c*x=x*c*(u*a) := corrected rfl hcu ux ha
  have cy : c*y=y*c*(v*d) := corrected rfl hcv vy hd
  have B : b=b' := middle_eq x y c u v a b b' d hcu hcv huv ha hb hb' hd
    (ports_xy x y) cx cy uy vx
  exact ⟨x,y,c,u,v,a,b,d,huv,hcu,hcv,ha,hb,hd,ports_xy x y,cx,cy,ux,uy,
    by rw [B]; exact vx,vy⟩

theorem tail_layers (h : LS G 4=⊥) (x y : G) :
    (make h x y).a∈LS G 3 ∧ (make h x y).b∈LS G 3 ∧ (make h x y).d∈LS G 3 :=
  ⟨next_layer (layer_u x y) x,next_layer (layer_u x y) y,next_layer (layer_v x y) y⟩

end HaarClass4Ports

#print axioms HaarClass4Ports.make
