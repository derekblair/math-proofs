import Ribbon8AltBChart

namespace Ribbon8AltB
open Ribbon5Bridge Ribbon8Free HaarUniversal36
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem a_end (x y : G) : pathAt x y wa 32=(false,R x y) := by
  norm_num [pathAt,run,start,action,wa,la,R,U,V,lu,lv,ev,letter] <;> group

theorem w_end (x y : G) : pathAt x y ww 64=(false,Z x y) := by
  norm_num [pathAt,run,start,action,ww,lw,R,Z,U,V,lu,lv,ev,letter,commutatorElement_def] <;> group

theorem t_end (x y : G) :
    pathAt x y wt 128=(false,Z x y*(U x y)⁻¹*(Z x y)⁻¹*U x y) := by
  norm_num [pathAt,run,start,action,wt,lt,R,Z,U,V,lu,lv,ev,letter,commutatorElement_def] <;> group

theorem u_layer (x y : G) : U x y∈L G 1 := by
  change U x y∈(⊤:Subgroup G).lowerCentralSeries 1
  rw [Subgroup.top_lowerCentralSeries_one,← Abelianization.ker_of]
  change Abelianization.of (U x y)=1
  simp only [U,lu,ev,letter,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,map_mul,map_inv,mul_one]
  let X := Abelianization.of x
  let Y := Abelianization.of y
  calc
    _ = (X*X*X*X⁻¹*X⁻¹*X⁻¹)*(Y*Y*Y*Y⁻¹*Y⁻¹*Y⁻¹) := by dsimp [X,Y]; ac_rfl
    _ = 1 := by group
private def twist (x y : G) := y*y*x

theorem r_conjugate (x y : G) :
    R x y=twist x y * (Ribbon6.residue y⁻¹ x) * (twist x y)⁻¹ := by
  norm_num [R,U,V,lu,lv,ev,letter,twist,Ribbon6.residue,Ribbon6.U,Ribbon6.V] <;> group

theorem r_layer (x y : G) : R x y∈L G 4 := by
  rw [r_conjugate]
  exact (inferInstance : (L G 4).Normal).conj_mem _ (Ribbon6.residue_layer y⁻¹ x) _

theorem z_conjugate (x y : G) :
    Z x y=(U x y)⁻¹*⁅U x y,R x y⁆*U x y := by
  simp only [Z,R,commutatorElement_def]
  group

theorem z_layer (x y : G) : Z x y∈L G 6 := by
  have E : ⁅U x y,R x y⁆∈L G 6 := by
    rw [←commutatorElement_inv]
    exact (L G 6).inv_mem (Ribbon7.comm_mem 4 (r_layer x y) (u_layer x y))
  rw [z_conjugate]
  simpa only [inv_inv] using (inferInstance : (L G 6).Normal).conj_mem _ E (U x y)⁻¹

theorem commute (nil : L G 8=⊥) (x y : G) : Commute (Z x y) (U x y) :=
  commutatorElement_eq_one_iff_commute.mp
    (Subgroup.mem_bot.mp (nil ▸ Ribbon7.comm_mem 6 (z_layer x y) (u_layer x y)))

theorem t_close (nil : L G 8=⊥) (x y : G) : pathAt x y wt 128=pathAt x y wt 0 := by
  rw [t_end,(commute nil x y).inv_right.eq,mul_inv_cancel_right,inv_mul_cancel]
  rfl

end Ribbon8AltB
#print axioms Ribbon8AltB.r_layer
#print axioms Ribbon8AltB.t_close
