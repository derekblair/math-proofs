import Ribbon7AuxDefs
import HaarClass3Collector64
import HaarClass3Separation64

namespace Ribbon7Aux
open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass3Collector64 HaarClass3Table
open HaarClass3Separation64 (eval)
variable {G : Type*} [Group G]
def lettersH : Array (Bool × Fin 3) := #[(false,1),(true,2),(true,1),(true,1),(false,2),(false,1),(false,2),(true,1),(true,2),(false,1),(false,2),(true,1),(true,2),(false,1)]
def lettersD : Array (Bool × Fin 3) := #[(true,1),(true,1),(false,2),(false,2),(false,1),(true,2),(true,1),(true,2),(false,1),(false,1),(true,2),(true,1),(true,2),(false,1),(false,1),(false,2),(true,1),(false,2),(true,1),(true,2),(false,1),(false,1),(true,2),(true,1),(true,1),(false,2),(false,1),(false,2)]
def initial : Coord := (0,0,0,0,0)

def normal (w : Array (Bool × Fin 3)) : Nat → Coord
  | 0 => initial
  | n+1 => move w[n]!.1 w[n]!.2 (normal w n)

def letters (x y : G) (w : Array (Bool × Fin 3)) : Nat → G
  | 0 => 1
  | n+1 => letters x y w n *
      (if w[n]!.1 then HaarHalfCollision.port x y w[n]!.2
       else (HaarHalfCollision.port x y w[n]!.2)⁻¹)

private theorem u_central (x y : G) (nil : LS G 3=⊥) (g : G) : Commute (portU x y) g :=
  (Subgroup.mem_center_iff.mp ((Subgroup.commutator_top_right_eq_bot_iff_le_center.mp nil) (layer_u x y)) g).symm
private theorem v_central (x y : G) (nil : LS G 3=⊥) (g : G) : Commute (portV x y) g :=
  (Subgroup.mem_center_iff.mp ((Subgroup.commutator_top_right_eq_bot_iff_le_center.mp nil) (layer_v x y)) g).symm

private theorem cx (x y : G) (nil : LS G 3=⊥) :
    portC x y*x=x*portC x y*portU x y := by
  calc
    _ = portU x y*(x*portC x y) := by simp only [portU,commutatorElement_def]; group
    _ = _ := (u_central x y nil (x*portC x y)).eq

private theorem cy (x y : G) (nil : LS G 3=⊥) :
    portC x y*y=y*portC x y*portV x y := by
  calc
    _ = portV x y*(y*portC x y) := by simp only [portV,commutatorElement_def]; group
    _ = _ := (v_central x y nil (y*portC x y)).eq

theorem collect (x y : G) (nil : LS G 3=⊥) (w : Array (Bool×Fin 3)) (N : Nat)
    (valid : ∀ n<N, w[n]!.2=2 → Range (normal w n).1) :
    letters x y w N=eval x y (normal w N) := by
  induction N with
  | zero => simp [letters,normal,initial,eval,HaarClass3Collect.norm]
  | succ n ih =>
    rw [letters,ih (fun j hj => valid j (by omega)),normal]
    exact (norm_move x y _ _ _ (u_central x y nil) (v_central x y nil)
      (ports_xy x y) (cx x y nil) (cy x y nil) _ _ _ (valid n (by omega))).symm

instance (n : ℤ) : Decidable (Range n) := by unfold Range; infer_instance
private theorem validH : ∀ n : Fin 14, lettersH[n.val]!.2=2 → Range (normal lettersH n.val).1 := by decide +kernel
private theorem validD : ∀ n : Fin 28, lettersD[n.val]!.2=2 → Range (normal lettersD n.val).1 := by decide +kernel

private theorem endH : normal lettersH 14 = (0,0,0,-1,2) := by decide +kernel
private theorem endD : normal lettersD 28 = (0,0,0,1,-2) := by decide +kernel

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem evalH (x y : G) : letters x y lettersH 14=h x y := by
  norm_num [letters,lettersH,HaarHalfCollision.port,h,q,commutatorElement_def,pow_two]
  group

theorem evalD (x y : G) : letters x y lettersD 28=delta x y := by
  norm_num [letters,lettersD,HaarHalfCollision.port,delta]

theorem h_normal (x y : G) (nil : LS G 3=⊥) : h x y=(portU x y)⁻¹*(portV x y)^2 := by
  rw [←evalH,collect x y nil lettersH 14 (fun n hn => validH ⟨n,hn⟩),endH]
  norm_num [eval,HaarClass3Collect.norm]

theorem delta_normal (x y : G) (nil : LS G 3=⊥) :
    delta x y=portU x y*((portV x y)^2)⁻¹ := by
  rw [←evalD,collect x y nil lettersD 28 (fun n hn => validD ⟨n,hn⟩),endD]
  simp [eval,HaarClass3Collect.norm,zpow_neg]

theorem delta_eq_inv (x y : G) (nil : LS G 3=⊥) : delta x y=(h x y)⁻¹ := by
  rw [delta_normal x y nil,h_normal x y nil,mul_inv_rev,inv_inv]
  exact ((u_central x y nil (portV x y)).pow_right 2).inv_right.eq

theorem h_central_class3 (x y : G) (nil : LS G 3=⊥) (g : G) : Commute (h x y) g := by
  rw [h_normal x y nil]
  exact (u_central x y nil g).inv_left.mul_left ((v_central x y nil g).pow_left 2)

end Ribbon7Aux
#print axioms Ribbon7Aux.delta_eq_inv
