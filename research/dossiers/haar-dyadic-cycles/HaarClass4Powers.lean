import HaarClass4CollectCore

namespace HaarClass4Powers
open HaarClass4CollectCore HaarClass4Table

variable {G : Type*} [Group G]

theorem central_mul {a b : G} (ha : Central a) (hb : Central b) : Central (a*b) :=
  fun g => (ha g).mul_left (hb g)

theorem central_pow {a : G} (ha : Central a) (n : ℤ) : Central (a^n) :=
  fun g => (ha g).zpow_left n

theorem tail_mul (c u v : G) (hcu : Commute c u) (hcv : Commute c v) (huv : Commute u v)
    (k a b k' a' b' : ℤ) :
    (c^k*u^a*v^b)*(c^k'*u^a'*v^b') = c^(k+k')*u^(a+a')*v^(b+b') := by
  simp only [zpow_add,mul_assoc]
  rw [← mul_assoc (v^b) (c^k'),((hcv.symm).zpow_zpow b k').eq,mul_assoc (c^k') (v^b),
    ← mul_assoc (u^a) (c^k'),((hcu.symm).zpow_zpow a k').eq,mul_assoc (c^k') (u^a),
    ← mul_assoc (v^b) (u^a'),((huv.symm).zpow_zpow b a').eq,mul_assoc (u^a') (v^b)]

def powForm (x c u A : G) (i a d : ℤ) := x^i * c^i * u^a * A^d

theorem pow_step (x c u A : G) (hcu : Commute c u) (hA : Central A)
    (cx : c*x=x*c*(u*A)) (ux : u*x=x*u*A) (i a d : ℤ) :
    powForm x c u A i a d * (x*c) = powForm x c u A (i+1) (a+i) (d+a+i) := by
  have h := move_right x c u (1:G) A 1 hcu hA (fun z => Commute.one_left z) cx ux
    (by simp) i a 0
  simp only [zpow_zero,mul_one] at h
  have hAd := (hA x).zpow_left d
  have hh := (((hA c).zpow_left (a+i)).mul_left ((hA c).zpow_left d)).eq
  calc
    powForm x c u A i a d * (x*c) = x^i * ((c^i*u^a)*x) * A^d * c := by
      simp only [powForm,mul_assoc]
      rw [← mul_assoc (A^d) x,hAd.eq,mul_assoc x]
    _ = x^i * (x*(c^i*u^(a+i))*A^(a+i)) * A^d * c := by rw [h]
    _ = (x^i*x) * ((c^i*u^(a+i)) * ((A^(a+i)*A^d)*c)) := by group
    _ = (x^i*x) * ((c^i*u^(a+i)) * (c*(A^(a+i)*A^d))) := by rw [hh]
    _ = powForm x c u A (i+1) (a+i) (d+a+i) := by
      simp only [powForm,zpow_add_one,mul_assoc]
      rw [← mul_assoc (u^(a+i)) c,((hcu.symm).zpow_left (a+i)).eq,mul_assoc c]
      have rep : A^(d+a+i)=A^(a+i)*A^d := by rw [show d+a+i=a+i+d by omega,zpow_add]
      rw [rep]

theorem four_powers (x c u A : G) (hcu : Commute c u) (hA : Central A)
    (cx : c*x=x*c*(u*A)) (ux : u*x=x*u*A) (i : ℤ)
    (iok : i= -2 ∨ i= -1 ∨ i=0 ∨ i=1) :
    (x*c)^i = powForm x c u A i (tri i) (tet i) := by
  have neg1 : (x*c)^(-1:ℤ) = powForm x c u A (-1) 1 0 := by
    apply mul_right_cancel (b:=x*c)
    have H := pow_step x c u A hcu hA cx ux (-1) 1 0
    norm_num [powForm] at H ⊢
    exact H.symm
  have neg2 : (x*c)^(-2:ℤ) = powForm x c u A (-2) 3 (-1) := by
    apply mul_right_cancel (b:=x*c)
    rw [← zpow_add_one]
    have H := pow_step x c u A hcu hA cx ux (-2) 3 (-1)
    norm_num at H ⊢
    simpa using neg1.trans H.symm
  rcases iok with rfl|rfl|rfl|rfl
  · norm_num [tri,tet]; simpa using neg2
  · norm_num [tri,tet]; simpa using neg1
  · norm_num [tri,tet,powForm]
  · norm_num [tri,tet,powForm]

theorem x_to_y (x y c u A : G) (hcu : Commute c u) (hA : Central A)
    (xy : x*y=y*x*c) (cx : c*x=x*c*(u*A)) (ux : u*x=x*u*A)
    (i : ℤ) (iok : i= -2 ∨ i= -1 ∨ i=0 ∨ i=1) :
    x^i*y = y*(x^i*c^i*u^(tri i)*A^(tet i)) := by
  have hS : SemiconjBy y (x*c) x := by
    change y*(x*c)=x*y
    rw [xy,mul_assoc]
  have hZ := (hS.zpow_right i).eq
  rw [four_powers x c u A hcu hA cx ux i iok] at hZ
  exact hZ.symm

end HaarClass4Powers

#print axioms HaarClass4Powers.four_powers
#print axioms HaarClass4Powers.x_to_y
