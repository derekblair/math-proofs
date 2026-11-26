import Ribbon8SmallRank
import Ribbon7AuxCollect

namespace Ribbon8Small
open Ribbon5Bridge HaarClass3Table HaarClass3Collector64 HaarClass4Ports HaarClass4Structure
open HaarClass3Separation64 (eval)
open scoped commutatorElement
variable {G : Type*} [Group G]

abbrev State := Bool × Coord

def Push (s : State) (p : P) : State :=
  if p=2 then (!s.1,s.2)
  else (s.1,move (decide (p=0)) (if s.1 then 2 else 1) s.2)

def Vert (x y : G) (s : State) : Bool × G := (s.1,eval x y s.2)

theorem central_u (x y : G) (nil : LS G 3=⊥) (g : G) : Commute (portU x y) g :=
  (Subgroup.mem_center_iff.mp ((Subgroup.commutator_top_right_eq_bot_iff_le_center.mp nil) (layer_u x y)) g).symm
theorem central_v (x y : G) (nil : LS G 3=⊥) (g : G) : Commute (portV x y) g :=
  (Subgroup.mem_center_iff.mp ((Subgroup.commutator_top_right_eq_bot_iff_le_center.mp nil) (layer_v x y)) g).symm

theorem cx (x y : G) (nil : LS G 3=⊥) :
    portC x y*x=x*portC x y*portU x y := by
  calc
    _ = portU x y*(x*portC x y) := by simp only [portU,commutatorElement_def]; group
    _ = _ := (central_u x y nil (x*portC x y)).eq

theorem cy (x y : G) (nil : LS G 3=⊥) :
    portC x y*y=y*portC x y*portV x y := by
  calc
    _ = portV x y*(y*portC x y) := by simp only [portV,commutatorElement_def]; group
    _ = _ := (central_v x y nil (y*portC x y)).eq

theorem moveC (x y : G) (nil : LS G 3=⊥) (s : State) (p : P) (r : Range s.2.1) :
    Vert x y (Push s p)=action x y (Vert x y s) p := by
  rcases s with ⟨b,z⟩
  have eq (s : Bool) (j : Fin 3) :
      eval x y (move s j z)=eval x y z*
      (if s then HaarHalfCollision.port x y j else (HaarHalfCollision.port x y j)⁻¹) :=
    norm_move x y _ _ _ (central_u x y nil) (central_v x y nil)
      (ports_xy x y) (cx x y nil) (cy x y nil) s j z (fun _ => r)
  cases b <;> fin_cases p <;>
    simp [Vert,Push,action,HaarHalfCollision.port,eq]

theorem chartSound (x y : G) (nil : LS G 3=⊥) (w : Array P) (rows : Array State)
    (base : rows[0]! = (false,0,0,0,0,0))
    (step : ∀ i<w.size, Push rows[i]! w[i]! = rows[i+1]!)
    (range : ∀ i<w.size, Range rows[i]!.2.1) :
    ∀ i≤w.size, pathAt x y w i=Vert x y rows[i]! := by
  intro i
  induction i with
  | zero => intro _; simp [pathAt,run,start,Vert,base,eval,HaarClass3Collect.norm]
  | succ i ih =>
    intro hi
    have hor : i<w.size := by omega
    rw [pathAt_next x y w hor,ih (by omega),←step i hor,moveC x y nil _ _ (range i hor)]

def mon (c u v : G) (a b d : ℤ) : G := c^a*u^b*v^d

theorem mon_add (c u v : G) (cu : Commute c u) (cv : Commute c v) (uv : Commute u v)
    (a b d a' b' d' : ℤ) :
    mon c u v a b d * mon c u v a' b' d' = mon c u v (a+a') (b+b') (d+d') :=
  HaarClass4Powers.tail_mul c u v cu cv uv a b d a' b' d'

theorem diff_one (x y : G) (nil : LS G 3=⊥)
    (p q : Coord) (i : p.1=q.1) (j : p.2.1=q.2.1)
    (h : eval x y p = eval x y q) :
    mon (portC x y) (portU x y) (portV x y)
      (q.2.2.1-p.2.2.1) (q.2.2.2.1-p.2.2.2.1) (q.2.2.2.2-p.2.2.2.2)=1 := by
  let c := portC x y
  let u := portU x y
  let v := portV x y
  have E : mon c u v p.2.2.1 p.2.2.2.1 p.2.2.2.2 =
      mon c u v q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
    simp only [eval,HaarClass3Collect.norm,mul_assoc] at h
    rw [i,j] at h
    simpa only [mon,mul_assoc] using (mul_left_cancel (mul_left_cancel h))
  have T := mon_add c u v (central_u x y nil c).symm (central_v x y nil c).symm
    (central_u x y nil v) p.2.2.1 p.2.2.2.1 p.2.2.2.2
      (q.2.2.1-p.2.2.1) (q.2.2.2.1-p.2.2.2.1) (q.2.2.2.2-p.2.2.2.2)
  rw [show p.2.2.1+(q.2.2.1-p.2.2.1)=q.2.2.1 by omega,
      show p.2.2.2.1+(q.2.2.2.1-p.2.2.2.1)=q.2.2.2.1 by omega,
      show p.2.2.2.2+(q.2.2.2.2-p.2.2.2.2)=q.2.2.2.2 by omega,←E] at T
  exact mul_left_cancel (T.trans (mul_one _).symm)

theorem reverse_one (c u v : G) (cu : Commute c u) (cv : Commute c v) (uv : Commute u v)
    {a b d : ℤ} (h : mon c u v a b d = 1) : mon c u v (-a) (-b) (-d) = 1 := by
  have E := mon_add c u v cu cv uv (-a) (-b) (-d) a b d
  rw [h,mul_one] at E
  simpa [mon] using E

theorem reduce_pow (g : G) (p : Nat) (h : g^p=1) (a : ℤ) : g^a=g^(a%(p:ℤ)) := by
  have E : a = (p:ℤ)*(a/(p:ℤ))+a%(p:ℤ) := (Int.mul_ediv_add_emod _ _).symm
  calc
    _ = g^((p:ℤ)*(a/(p:ℤ))+a%(p:ℤ)) := congrArg (fun k : ℤ => g^k) E
    _ = _ := by rw [zpow_add,zpow_mul,zpow_natCast,h,one_zpow,one_mul]

end Ribbon8Small
#print axioms Ribbon8Small.chartSound
#print axioms Ribbon8Small.diff_one
