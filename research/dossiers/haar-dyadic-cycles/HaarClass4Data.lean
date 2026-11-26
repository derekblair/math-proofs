import HaarClass4Structure

namespace HaarClass4Data
open scoped commutatorElement
open HaarClass4CollectCore HaarClass4Normal HaarClass4Structure

variable {G : Type*} [Group G]

def rc (t : G) : G →* G where
  toFun z := t⁻¹*z*t
  map_one' := by group
  map_mul' a b := by group

theorem rc_add (x y z : G) : rc (x*y) z = rc y (rc x z) := by
  change (x*y)⁻¹*z*(x*y) = y⁻¹*(x⁻¹*z*x)*y
  group

theorem rc_center {a : G} (h : Central a) (t : G) : rc t a = a := by
  change t⁻¹*a*t=a
  rw [mul_assoc,(h t).eq]
  group

theorem rc_eq {x z r : G} (h : z*x=x*r) : rc x z = r := by
  change x⁻¹*z*x=r
  rw [mul_assoc,h]
  group

theorem right_of_left {a b d : G} (h : ⁅a,b⁆=d) (hd : Central d) :
    a*b=b*a*d := by
  rw [← (hd (b*a)).eq,← h]
  simp only [commutatorElement_def]
  group

theorem corrected {c x u a : G} (h : ⁅c,x⁆=u) (hcu : Commute c u)
    (ux : u*x=x*u*a) (ha : Central a) : c*x=x*c*(u*a) := by
  have z : c*x=u*(x*c) := by rw [←h]; simp only [commutatorElement_def]; group
  rw [z,← mul_assoc,ux,mul_assoc (x*u) a,(ha c).eq]
  simp only [mul_assoc]
  rw [← mul_assoc u c,hcu.eq.symm]
  simp only [mul_assoc]

theorem middle_eq (x y c u v a b b' d : G)
    (hcu : Commute c u) (hcv : Commute c v) (huv : Commute u v)
    (ha : Central a) (hb : Central b) (hb' : Central b') (hd : Central d)
    (xy : x*y=y*x*c) (cx : c*x=x*c*(u*a)) (cy : c*y=y*c*(v*d))
    (uy : u*y=y*u*b) (vx : v*x=x*v*b') : b=b' := by
  have X : rc x c=c*u*a := rc_eq (by simpa only [mul_assoc] using cx)
  have Y : rc y c=c*v*d := rc_eq (by simpa only [mul_assoc] using cy)
  have U : rc y u=u*b := rc_eq (by simpa only [mul_assoc] using uy)
  have V : rc x v=v*b' := rc_eq (by simpa only [mul_assoc] using vx)
  have P : rc (x*y) c = c*v*d*(u*b)*a := by
    rw [rc_add,X,map_mul,map_mul,Y,U,rc_center ha]
  have Q : rc (y*x) c = c*u*a*(v*b')*d := by
    rw [rc_add,Y,map_mul,map_mul,X,V,rc_center hd]
  have R : rc c (rc (y*x) c) = rc (y*x) c := by
    simp only [Q,map_mul,rc_center ha,rc_center hb',rc_center hd]
    have cu : rc c u=u := rc_eq (by exact (hcu.symm).eq)
    have cv : rc c v=v := rc_eq (by exact (hcv.symm).eq)
    have cc : rc c c=c := rc_eq rfl
    rw [cu,cv,cc]
  have E : c*v*d*(u*b)*a = c*u*a*(v*b')*d := by
    rw [← P,←Q,xy,rc_add,R]
  have L : c*v*d*(u*b)*a = c*u*v*a*d*b := by
    simp only [mul_assoc]
    rw [← mul_assoc d u,(hd u).eq,mul_assoc u d,← mul_assoc v u,huv.eq.symm,mul_assoc u v,
      (hb a).eq,← mul_assoc d a,(hd a).eq]
    simp only [mul_assoc]
  have R' : c*u*a*(v*b')*d = c*u*v*a*d*b' := by
    simp only [mul_assoc]
    rw [← mul_assoc a v,(ha v).eq,mul_assoc v a,(hb' d).eq]
  exact mul_left_cancel (L.symm.trans (E.trans R'))

end HaarClass4Data

#print axioms HaarClass4Data.middle_eq
