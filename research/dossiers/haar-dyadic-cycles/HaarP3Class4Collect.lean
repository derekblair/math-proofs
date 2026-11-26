import HaarClass4Normal
import HaarHalfCollision

namespace HaarP3Class4Collect
open HaarClass4Table HaarClass4Normal HaarClass4Powers HaarClass4CollectCore
variable {G : Type*} [Group G]

def range4 (i : ℤ) : Prop := i= -2 ∨ i= -1 ∨ i=0 ∨ i=1 ∨ i=2
instance (i : ℤ) : Decidable (range4 i) := by unfold range4; infer_instance

theorem x_to_yPlus (x y c u A : G) (hcu : Commute c u) (hA : Central A)
    (xy : x*y=y*x*c) (cx : c*x=x*c*(u*A)) (ux : u*x=x*u*A)
    (i : ℤ) (iok : range4 i) :
    x^i*y = y*(x^i*c^i*u^(tri i)*A^(tet i)) := by
  by_cases k : i=2
  · subst i
    have hx : (x*c)^(2:ℤ) = powForm x c u A 2 (tri 2) (tet 2) := by
      have h := pow_step x c u A hcu hA cx ux 1 0 0
      norm_num [powForm,tri,tet,zpow_two] at h ⊢
      simpa [pow_two,zpow_two] using h
    have hS : SemiconjBy y (x*c) x := by
      change y*(x*c)=x*y
      rw [xy,mul_assoc]
    have hZ := (hS.zpow_right (2:ℤ)).eq
    rw [hx] at hZ
    simpa [powForm,mul_assoc] using hZ.symm
  · exact x_to_y x y c u A hcu hA xy cx ux i (by rcases iok with h|h|h|h|h <;> tauto)

variable (M : Data G)

theorem eval_yPlus (r : Row) (iok : range4 r.i) :
    eval M (rightY r) = eval M r * M.y := by
  have z := move_right_y M.y M.c M.u M.v M.b M.d M.hcv M.huv M.cb M.cd M.cy M.uy M.vy r.c r.u r.v
  have u : mid M r.c r.u r.v * M.y =
      M.y * mid M r.c r.u (r.v+r.c) * tail M 0 r.u (r.v+r.c) := by
    simpa [mid,tail] using z
  have p := tail_center M r.a r.b r.d M.y
  have w := x_to_yPlus M.x M.y M.c M.u M.a M.hcu M.ca M.xy M.cx M.ux r.i iok
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


def leftX (r : Row) : Row :=
  ⟨r.i-1,r.j,r.c,r.u-r.c,r.v,r.a-r.u,r.b-r.v,r.d⟩
def leftY (r : Row) : Row :=
  ⟨r.i,r.j-1,r.c-r.i,r.u-tri r.i,r.v-r.c+r.i,r.a-tet r.i,r.b-r.u+tri r.i,r.d-r.v⟩

theorem right_leftX (r : Row) : rightX (leftX r)=r := by
  cases r; simp [rightX,leftX]
theorem right_leftY (r : Row) : rightY (leftY r)=r := by
  cases r; simp [rightY,leftY] <;> ring

def move (pos : Bool) (port : Fin 3) (p : Row) : Row :=
  if port=0 then p else if port=1 then if pos then rightX p else leftX p
  else if pos then rightY p else leftY p

theorem step_eval (pos : Bool) (port : Fin 3) (p : Row)
    (h : port=2 → range4 p.i) :
    eval M (move pos port p) =
      eval M p*(if pos then HaarHalfCollision.port M.x M.y port else
        (HaarHalfCollision.port M.x M.y port)⁻¹) := by
  have hx := eval_x M (leftX p)
  rw [right_leftX] at hx
  have hy (h : range4 p.i) := eval_yPlus M (leftY p) h
  fin_cases port <;> cases pos
  · simp [move,HaarHalfCollision.port]
  · simp [move,HaarHalfCollision.port]
  · simpa [move,HaarHalfCollision.port] using eq_mul_inv_iff_mul_eq.mpr hx.symm
  · simpa [move,HaarHalfCollision.port] using eval_x M p
  · have hd := hy (h rfl)
    rw [right_leftY] at hd
    simpa [move,HaarHalfCollision.port] using eq_mul_inv_iff_mul_eq.mpr hd.symm
  · simpa [move,HaarHalfCollision.port] using eval_yPlus M p (h rfl)

end HaarP3Class4Collect
#print axioms HaarP3Class4Collect.step_eval
