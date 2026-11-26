import HaarClass4Powers

namespace HaarClass4Normal
open HaarClass4CollectCore HaarClass4Powers HaarClass4Table

variable {G : Type*} [Group G]

structure Data (G : Type*) [Group G] where
  x : G
  y : G
  c : G
  u : G
  v : G
  a : G
  b : G
  d : G
  huv : Commute u v
  hcu : Commute c u
  hcv : Commute c v
  ca : Central a
  cb : Central b
  cd : Central d
  xy : x*y=y*x*c
  cx : c*x=x*c*(u*a)
  cy : c*y=y*c*(v*d)
  ux : u*x=x*u*a
  uy : u*y=y*u*b
  vx : v*x=x*v*b
  vy : v*y=y*v*d

variable (M : Data G)

def tail (a b d : ℤ) := M.a^a * M.b^b * M.d^d
def mid (c u v : ℤ) := M.c^c * M.u^u * M.v^v
def eval (r : Row) : G := M.y^r.j * M.x^r.i * (mid M r.c r.u r.v * tail M r.a r.b r.d)

theorem tail_center (a b d : ℤ) : Central (tail M a b d) :=
  central_mul (central_mul (central_pow M.ca a) (central_pow M.cb b)) (central_pow M.cd d)

theorem tail_add (a b d a' b' d' : ℤ) :
    tail M a b d * tail M a' b' d' = tail M (a+a') (b+b') (d+d') :=
  tail_mul M.a M.b M.d (M.ca M.b) (M.ca M.d) (M.cb M.d) a b d a' b' d'

theorem mid_add (c u v c' u' v' : ℤ) :
    mid M c u v * mid M c' u' v' = mid M (c+c') (u+u') (v+v') :=
  tail_mul M.c M.u M.v M.hcu M.hcv M.huv c u v c' u' v'

theorem eval_x (r : Row) : eval M (rightX r) = eval M r * M.x := by
  have z := move_right M.x M.c M.u M.v M.a M.b M.hcu M.ca M.cb M.cx M.ux M.vx r.c r.u r.v
  have p := tail_center M r.a r.b r.d M.x
  calc
    eval M (rightX r) = (M.y^r.j * M.x^r.i) *
        (M.x * (mid M r.c (r.u+r.c) r.v) * (tail M (r.u+r.c) r.v 0 * tail M r.a r.b r.d)) := by
      rw [tail_add]
      simp only [eval,rightX,zpow_add_one,mul_assoc]
      rw [show r.a+r.u+r.c=r.u+r.c+r.a by omega,add_comm r.b r.v,zero_add]
    _ = M.y^r.j*M.x^r.i*((mid M r.c r.u r.v * M.x)*tail M r.a r.b r.d) := by
      have E : mid M r.c r.u r.v * M.x =
          M.x * mid M r.c (r.u+r.c) r.v * tail M (r.u+r.c) r.v 0 := by
        simpa [mid,tail] using z
      rw [E]
      simp only [mul_assoc]
    _ = eval M r * M.x := by
      simp only [eval,mul_assoc]
      rw [← p.eq]

theorem eval_y (r : Row) (iok : r.i= -2 ∨ r.i= -1 ∨ r.i=0 ∨ r.i=1) :
    eval M (rightY r) = eval M r * M.y := by
  have z := move_right_y M.y M.c M.u M.v M.b M.d M.hcv M.huv M.cb M.cd M.cy M.uy M.vy r.c r.u r.v
  have u : mid M r.c r.u r.v * M.y =
      M.y * mid M r.c r.u (r.v+r.c) * tail M 0 r.u (r.v+r.c) := by
    simpa [mid,tail] using z
  have p := tail_center M r.a r.b r.d M.y
  have w := x_to_y M.x M.y M.c M.u M.a M.hcu M.ca M.xy M.cx M.ux r.i iok
  let m := mid M r.c r.u (r.v+r.c)
  let t := tail M 0 r.u (r.v+r.c)
  let T := tail M r.a r.b r.d
  have c0 : Commute (tail M (tet r.i) 0 0) m := tail_center M _ _ _ _
  calc
    eval M (rightY r) =
      (M.y^r.j * M.y) * M.x^r.i *
        ((mid M r.i (tri r.i) 0 * m) * (tail M (tet r.i) 0 0 * t * T)) := by
      rw [show m = mid M r.c r.u (r.v+r.c) from rfl]
      rw [mid_add]
      unfold t T
      rw [tail_add,tail_add]
      simp only [eval,rightY,zpow_add_one,mul_assoc,zero_add,add_zero]
      rw [add_comm r.c r.i,add_comm r.u (tri r.i),add_comm r.a (tet r.i),add_comm r.b r.u,
        show r.d+r.v+r.c=r.v+r.c+r.d by omega]
    _ = M.y^r.j*((M.x^r.i*M.y)*m*(t*T)) := by
      rw [mul_assoc (tail M (tet r.i) 0 0) t,← mul_assoc (mid M r.i (tri r.i) 0 * m),
        mul_assoc (mid M r.i (tri r.i) 0),← c0.eq]
      rw [w]
      simp only [mid,tail,zpow_zero,mul_one,mul_assoc]
    _ = M.y^r.j*M.x^r.i*((M.y*m*t)*T) := by simp only [mul_assoc]
    _ = eval M r * M.y := by
      rw [← u]
      simp only [eval,T,mul_assoc]
      rw [← p.eq]

end HaarClass4Normal

#print axioms HaarClass4Normal.eval_x
#print axioms HaarClass4Normal.eval_y
