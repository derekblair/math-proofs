import GeometricPatternDet

namespace RobustFolkman.GeometricGap

def threeGramDet (a b c : ℝ) : ℝ := 1-a^2-b^2-c^2+2*a*b*c

/-- An explicit global supporting plane at the triangle corner on the
entire threshold cube. No local-maximizer or log-det theory is needed. -/
theorem triangle_det_corner_plane (t x y z : ℝ) (t0 : 0≤t) (tm : t≤1/4)
    (x0 : 0≤x) (y0 : 0≤y) (z0 : 0≤z)
    (x1 : x≤1-t) (y1 : y≤1-t) (z1 : z≤1-t) :
    threeGramDet (t+x) (t+y) (t+z) ≤
      threeGramDet t t t - 2*t*(1-t)*(x+y+z) := by
  have pxy : 2*x*y≤x^2+y^2 := by nlinarith only [sq_nonneg (x-y)]
  have pxz : 2*x*z≤x^2+z^2 := by nlinarith only [sq_nonneg (x-z)]
  have pyz : 2*y*z≤y^2+z^2 := by nlinarith only [sq_nonneg (y-z)]
  have pp : x*y+x*z+y*z≤x^2+y^2+z^2 := by linarith only [pxy,pxz,pyz]
  have a : 2*x*y*z ≤ (1-t)*(y^2+z^2) := by
    have i := mul_le_mul_of_nonneg_left pyz x0
    have j := mul_le_mul_of_nonneg_right x1 (show 0≤y^2+z^2 by positivity)
    nlinarith only [i,j]
  have b : 2*x*y*z ≤ (1-t)*(x^2+z^2) := by
    have i := mul_le_mul_of_nonneg_left pxz y0
    have j := mul_le_mul_of_nonneg_right y1 (show 0≤x^2+z^2 by positivity)
    nlinarith only [i,j]
  have c : 2*x*y*z ≤ (1-t)*(x^2+y^2) := by
    have i := mul_le_mul_of_nonneg_left pxy z0
    have j := mul_le_mul_of_nonneg_right z1 (show 0≤x^2+y^2 by positivity)
    nlinarith only [i,j]
  have e := mul_le_mul_of_nonneg_left pp (show 0≤2*t by positivity)
  have u := mul_le_mul_of_nonneg_right (show 4*t≤1 by linarith only [tm])
    (show 0≤x^2+y^2+z^2 by positivity)
  unfold threeGramDet
  nlinarith only [a,b,c,e,u]

/-- The lower bound on a small corner box uses just the nonnegative
mixed terms in the exact determinant expansion. -/
theorem triangle_det_corner_box_lower (t x y z w : ℝ)
    (t0 : 0≤t) (t1 : t≤1)
    (x0 : 0≤x) (y0 : 0≤y) (z0 : 0≤z)
    (x1 : x≤w) (y1 : y≤w) (z1 : z≤w) :
    threeGramDet t t t - (6*t*w+3*w^2) ≤ threeGramDet (t+x) (t+y) (t+z) := by
  have w0 : 0≤w := x0.trans x1
  have mx := pow_le_pow_left₀ x0 x1 2
  have my := pow_le_pow_left₀ y0 y1 2
  have mz := pow_le_pow_left₀ z0 z1 2
  have lin := mul_le_mul_of_nonneg_left (show x+y+z≤3*w by linarith only [x1,y1,z1])
    (show 0≤2*t by positivity)
  have relax : 0≤2*t^2*(x+y+z) := by positivity
  have rem : 0≤ 2*t*(x*y+x*z+y*z)+2*x*y*z := by positivity
  unfold threeGramDet
  nlinarith only [mx,my,mz,lin,relax,rem]

#print axioms triangle_det_corner_plane
#print axioms triangle_det_corner_box_lower
end RobustFolkman.GeometricGap
