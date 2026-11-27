import GeometricRootedSecond

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory

theorem rooted_rate_room (t X : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (Ee : Matrix (Fin 2) (Fin 2) ℝ)
    (Tr : Matrix (Fin 2⊕Unit) (Fin 2⊕Unit) ℝ) (Di : Matrix Four Four ℝ)
    (e : GramOptimal edgeCon t Ee) (tr : GramOptimal triangleCon t Tr)
    (d : GramOptimal diamondEdges t Di) (hx : edgeRateClosed t+capRate t<X) :
    patternRate Tr<2*X ∧ 2*patternRate Tr-patternRate Di<X := by
  let f := pageFactor t t
  have z : 0<1-t^2 := by
    have p := mul_pos (show 0<1-t by linarith only [ts]) (show 0<1+t by positivity)
    nlinarith only [p]
  have fp : 0<f := by
    have k := centered_less t0 (show t≤1/2 by linarith only [ts])
    dsimp [f,pageFactor]
    linarith only [k,ts]
  have detT : Tr.det=(1-t^2)*f := by
    change Tr.det=(1-t^2)*pageFactor t t
    have hh := page_opt_factor edgeCon edgeCon_sym (by decide) (0:Fin 2) 1 (by decide)
      (by simp [edgeCon]) t t0 ts Ee Tr e.1 e.2 tr.1 tr.2
    simpa only [edge_det_exact t t0 ts Ee e] using hh
  have detD := diamond_det_exact t t0 ts Di d
  have L : -(Real.log f)/2 = edgeRateClosed t+capRate t := by
    have eq := effective_cap_page t t0 (show t<1 by linarith only [ts])
    change f/(1-t^2)=_ at eq
    unfold edgeRateClosed capRate
    rw [←eq,Real.log_div fp.ne' z.ne']
    ring
  have logT : patternRate Tr = edgeRateClosed t + (-(Real.log f)/2) := by
    unfold patternRate edgeRateClosed
    rw [detT,Real.log_mul z.ne' fp.ne']
    ring
  have logD : patternRate Di = edgeRateClosed t + 2*(-(Real.log f)/2) := by
    unfold patternRate edgeRateClosed
    rw [detD,show pageFactor t t=f from rfl,
      Real.log_mul z.ne' (pow_ne_zero _ fp.ne'),Real.log_pow]
    ring
  have Cp : 0<capRate t := by
    unfold capRate
    have y0 : 0<t/(1+t) := by positivity
    have y1 : t/(1+t)<1 := (div_lt_iff₀ (by positivity : 0<1+t)).2 (by linarith)
    have w0 := mul_pos (show 0<1-t/(1+t) by linarith) (show 0<1+t/(1+t) by positivity)
    have w1 : 1-(t/(1+t))^2<1 := by nlinarith only [sq_pos_of_pos y0]
    linarith only [Real.log_neg (by nlinarith only [w0]) w1]
  constructor <;> linarith only [logT,logD,L,Cp,hx]

#print axioms rooted_rate_room
end RobustFolkman.GeometricGap
