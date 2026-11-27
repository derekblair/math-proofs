import Mathlib.Tactic

/-! Exact integer order inequalities for the seven residual five-orbit charts.
This file does not prove the chart cover, port matchings, graph lifting, or Sheehan theorem. -/
namespace SheehanFive
def pos (n b z : Int) : Int := 5 * (z % n) + b

theorem reducePos (n b z q : Int) (hlo : 0 ≤ z - q*n) (hhi : z-q*n<n) :
    pos n b z = 5*(z-q*n)+b := by
  unfold pos
  rw [← Int.sub_mul_emod_self_right z q n, Int.emod_eq_of_lt hlo hhi]

theorem chartP_0312 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : a ≤ x) (h1 : x ≤ n-1-a) :
    (pos n 0 (0) < pos n 0 ((1)*a)) ∧
    (pos n 0 ((1)*a) < pos n 4 ((1)*x)) ∧
    (pos n 4 ((1)*x) < pos n 4 ((1)*a+(1)*x)) := by
  have p0 := reducePos n 0 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((1)*x) (0) (by omega) (by omega)
  have p2 := reducePos n 4 ((1)*a+(1)*x) (0) (by omega) (by omega)
  have p3 := reducePos n 0 ((1)*a) (0) (by omega) (by omega)
  simp only [p0, p1, p2, p3]
  omega

theorem chartQ_402315 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : x=1) (h1 : x≤a-1) :
    (pos n 0 ((1)+(-1)*x) < pos n 4 (0)) ∧
    (pos n 4 (0) < pos n 1 ((-1)*a+(-1)*x)) ∧
    (pos n 1 ((-1)*a+(-1)*x) < pos n 0 ((1)+(-1)*a+(-1)*x)) ∧
    (pos n 0 ((1)+(-1)*a+(-1)*x) < pos n 4 ((-1)*a)) ∧
    (pos n 4 ((-1)*a) < pos n 1 ((-1)*x)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 1 ((-1)*a+(-1)*x) (-1) (by omega) (by omega)
  have p3 := reducePos n 0 ((1)+(-1)*a+(-1)*x) (-1) (by omega) (by omega)
  have p4 := reducePos n 0 ((1)+(-1)*x) (0) (by omega) (by omega)
  have p5 := reducePos n 1 ((-1)*x) (-1) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5]
  omega

theorem chartQ_023154 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : 2≤x) (h1 : x≤a-1) :
    (pos n 4 (0) < pos n 1 ((-1)*a+(-1)*x)) ∧
    (pos n 1 ((-1)*a+(-1)*x) < pos n 0 ((1)+(-1)*a+(-1)*x)) ∧
    (pos n 0 ((1)+(-1)*a+(-1)*x) < pos n 4 ((-1)*a)) ∧
    (pos n 4 ((-1)*a) < pos n 1 ((-1)*x)) ∧
    (pos n 1 ((-1)*x) < pos n 0 ((1)+(-1)*x)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 1 ((-1)*a+(-1)*x) (-1) (by omega) (by omega)
  have p3 := reducePos n 0 ((1)+(-1)*a+(-1)*x) (-1) (by omega) (by omega)
  have p4 := reducePos n 0 ((1)+(-1)*x) (-1) (by omega) (by omega)
  have p5 := reducePos n 1 ((-1)*x) (-1) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5]
  omega

theorem chartQ_305412 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : x=1-a) (h1 : 2≤a) :
    (pos n 0 ((1)+(-1)*a+(-1)*x) < pos n 4 (0)) ∧
    (pos n 4 (0) < pos n 1 ((-1)*x)) ∧
    (pos n 1 ((-1)*x) < pos n 0 ((1)+(-1)*x)) ∧
    (pos n 0 ((1)+(-1)*x) < pos n 4 ((-1)*a)) ∧
    (pos n 4 ((-1)*a) < pos n 1 ((-1)*a+(-1)*x)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 1 ((-1)*a+(-1)*x) (-1) (by omega) (by omega)
  have p3 := reducePos n 0 ((1)+(-1)*a+(-1)*x) (0) (by omega) (by omega)
  have p4 := reducePos n 0 ((1)+(-1)*x) (0) (by omega) (by omega)
  have p5 := reducePos n 1 ((-1)*x) (0) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5]
  omega

theorem chartQ_054123 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : 1-a<x) (h1 : x≤ -1) :
    (pos n 4 (0) < pos n 1 ((-1)*x)) ∧
    (pos n 1 ((-1)*x) < pos n 0 ((1)+(-1)*x)) ∧
    (pos n 0 ((1)+(-1)*x) < pos n 4 ((-1)*a)) ∧
    (pos n 4 ((-1)*a) < pos n 1 ((-1)*a+(-1)*x)) ∧
    (pos n 1 ((-1)*a+(-1)*x) < pos n 0 ((1)+(-1)*a+(-1)*x)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 1 ((-1)*a+(-1)*x) (-1) (by omega) (by omega)
  have p3 := reducePos n 0 ((1)+(-1)*a+(-1)*x) (-1) (by omega) (by omega)
  have p4 := reducePos n 0 ((1)+(-1)*x) (0) (by omega) (by omega)
  have p5 := reducePos n 1 ((-1)*x) (0) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5]
  omega

theorem chartR_054123 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : x=0) (h1 : y= -1) (h2 : 2≤a) :
    (pos n 4 (0) < pos n 1 ((-1)*y)) ∧
    (pos n 1 ((-1)*y) < pos n 4 ((1)*x+(-1)*y)) ∧
    (pos n 4 ((1)*x+(-1)*y) < pos n 4 ((-1)*a)) ∧
    (pos n 4 ((-1)*a) < pos n 1 ((-1)*a+(-1)*y)) ∧
    (pos n 1 ((-1)*a+(-1)*y) < pos n 4 ((-1)*a+(1)*x+(-1)*y)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 1 ((-1)*a+(-1)*y) (-1) (by omega) (by omega)
  have p3 := reducePos n 4 ((-1)*a+(1)*x+(-1)*y) (-1) (by omega) (by omega)
  have p4 := reducePos n 4 ((1)*x+(-1)*y) (0) (by omega) (by omega)
  have p5 := reducePos n 1 ((-1)*y) (0) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5]
  omega

theorem chartS_043512 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : x=0) (h1 : y=b-1) (h2 : 2≤b) :
    (pos n 3 (0) < pos n 1 ((-1)*b+(-1)*y)) ∧
    (pos n 1 ((-1)*b+(-1)*y) < pos n 3 ((-1)*b+(1)*x+(-1)*y)) ∧
    (pos n 3 ((-1)*b+(1)*x+(-1)*y) < pos n 3 ((-1)*b)) ∧
    (pos n 3 ((-1)*b) < pos n 1 ((-1)*y)) ∧
    (pos n 1 ((-1)*y) < pos n 3 ((1)*x+(-1)*y)) := by
  have p0 := reducePos n 3 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 1 ((-1)*y) (-1) (by omega) (by omega)
  have p2 := reducePos n 3 ((1)*x+(-1)*y) (-1) (by omega) (by omega)
  have p3 := reducePos n 3 ((-1)*b+(1)*x+(-1)*y) (-1) (by omega) (by omega)
  have p4 := reducePos n 1 ((-1)*b+(-1)*y) (-1) (by omega) (by omega)
  have p5 := reducePos n 3 ((-1)*b) (-1) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5]
  omega

theorem chartR_032451 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : x= -a) (h1 : y=b-1) (h2 : a<b) (h3 : 2*a+b-1<n) :
    (pos n 4 (0) < pos n 4 ((-1)*a+(1)*x+(-1)*y)) ∧
    (pos n 4 ((-1)*a+(1)*x+(-1)*y) < pos n 1 ((-1)*a+(-1)*y)) ∧
    (pos n 1 ((-1)*a+(-1)*y) < pos n 4 ((1)*x+(-1)*y)) ∧
    (pos n 4 ((1)*x+(-1)*y) < pos n 1 ((-1)*y)) ∧
    (pos n 1 ((-1)*y) < pos n 4 ((-1)*a)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 1 ((-1)*a+(-1)*y) (-1) (by omega) (by omega)
  have p3 := reducePos n 4 ((-1)*a+(1)*x+(-1)*y) (-1) (by omega) (by omega)
  have p4 := reducePos n 4 ((1)*x+(-1)*y) (-1) (by omega) (by omega)
  have p5 := reducePos n 1 ((-1)*y) (-1) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5]
  omega

theorem chartR_024153 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : x= -a) (h1 : y=b-1) (h2 : b<a) (h3 : 2≤b) (h4 : n<2*a+b-1) :
    (pos n 4 (0) < pos n 1 ((-1)*a+(-1)*y)) ∧
    (pos n 1 ((-1)*a+(-1)*y) < pos n 4 ((1)*x+(-1)*y)) ∧
    (pos n 4 ((1)*x+(-1)*y) < pos n 4 ((-1)*a)) ∧
    (pos n 4 ((-1)*a) < pos n 1 ((-1)*y)) ∧
    (pos n 1 ((-1)*y) < pos n 4 ((-1)*a+(1)*x+(-1)*y)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 1 ((-1)*a+(-1)*y) (-1) (by omega) (by omega)
  have p3 := reducePos n 4 ((-1)*a+(1)*x+(-1)*y) (-2) (by omega) (by omega)
  have p4 := reducePos n 4 ((1)*x+(-1)*y) (-1) (by omega) (by omega)
  have p5 := reducePos n 1 ((-1)*y) (-1) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5]
  omega

theorem chartT_20734651 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : a=1) (h1 : x= -1) (h2 : y= -1) :
    (pos n 2 ((-1)*a+(-1)*y) < pos n 4 (0)) ∧
    (pos n 4 (0) < pos n 2 ((-1)*y)) ∧
    (pos n 2 ((-1)*y) < pos n 3 ((-1)*a+(1)*b+(-1)*y)) ∧
    (pos n 3 ((-1)*a+(1)*b+(-1)*y) < pos n 0 ((-1)*a+(1)*b+(-1)*x+(-1)*y)) ∧
    (pos n 0 ((-1)*a+(1)*b+(-1)*x+(-1)*y) < pos n 3 ((1)*b+(-1)*y)) ∧
    (pos n 3 ((1)*b+(-1)*y) < pos n 0 ((1)*b+(-1)*x+(-1)*y)) ∧
    (pos n 0 ((1)*b+(-1)*x+(-1)*y) < pos n 4 ((-1)*a)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 2 ((-1)*a+(-1)*y) (0) (by omega) (by omega)
  have p3 := reducePos n 3 ((-1)*a+(1)*b+(-1)*y) (0) (by omega) (by omega)
  have p4 := reducePos n 0 ((-1)*a+(1)*b+(-1)*x+(-1)*y) (0) (by omega) (by omega)
  have p5 := reducePos n 0 ((1)*b+(-1)*x+(-1)*y) (0) (by omega) (by omega)
  have p6 := reducePos n 3 ((1)*b+(-1)*y) (0) (by omega) (by omega)
  have p7 := reducePos n 2 ((-1)*y) (0) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5, p6, p7]
  omega

theorem chartT_20473561 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : a=1) (h1 : b=1) (h2 : x=0) (h3 : y= -1) :
    (pos n 2 ((-1)*a+(-1)*y) < pos n 4 (0)) ∧
    (pos n 4 (0) < pos n 0 ((-1)*a+(1)*b+(-1)*x+(-1)*y)) ∧
    (pos n 0 ((-1)*a+(1)*b+(-1)*x+(-1)*y) < pos n 2 ((-1)*y)) ∧
    (pos n 2 ((-1)*y) < pos n 3 ((-1)*a+(1)*b+(-1)*y)) ∧
    (pos n 3 ((-1)*a+(1)*b+(-1)*y) < pos n 0 ((1)*b+(-1)*x+(-1)*y)) ∧
    (pos n 0 ((1)*b+(-1)*x+(-1)*y) < pos n 3 ((1)*b+(-1)*y)) ∧
    (pos n 3 ((1)*b+(-1)*y) < pos n 4 ((-1)*a)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 2 ((-1)*a+(-1)*y) (0) (by omega) (by omega)
  have p3 := reducePos n 3 ((-1)*a+(1)*b+(-1)*y) (0) (by omega) (by omega)
  have p4 := reducePos n 0 ((-1)*a+(1)*b+(-1)*x+(-1)*y) (0) (by omega) (by omega)
  have p5 := reducePos n 0 ((1)*b+(-1)*x+(-1)*y) (0) (by omega) (by omega)
  have p6 := reducePos n 3 ((1)*b+(-1)*y) (0) (by omega) (by omega)
  have p7 := reducePos n 2 ((-1)*y) (0) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5, p6, p7]
  omega

theorem chartT_73046521 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : a=1) (h1 : b=1) (h2 : x= -1) (h3 : y=0) :
    (pos n 2 ((-1)*y) < pos n 3 ((-1)*a+(1)*b+(-1)*y)) ∧
    (pos n 3 ((-1)*a+(1)*b+(-1)*y) < pos n 4 (0)) ∧
    (pos n 4 (0) < pos n 0 ((-1)*a+(1)*b+(-1)*x+(-1)*y)) ∧
    (pos n 0 ((-1)*a+(1)*b+(-1)*x+(-1)*y) < pos n 3 ((1)*b+(-1)*y)) ∧
    (pos n 3 ((1)*b+(-1)*y) < pos n 0 ((1)*b+(-1)*x+(-1)*y)) ∧
    (pos n 0 ((1)*b+(-1)*x+(-1)*y) < pos n 2 ((-1)*a+(-1)*y)) ∧
    (pos n 2 ((-1)*a+(-1)*y) < pos n 4 ((-1)*a)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 2 ((-1)*a+(-1)*y) (-1) (by omega) (by omega)
  have p3 := reducePos n 3 ((-1)*a+(1)*b+(-1)*y) (0) (by omega) (by omega)
  have p4 := reducePos n 0 ((-1)*a+(1)*b+(-1)*x+(-1)*y) (0) (by omega) (by omega)
  have p5 := reducePos n 0 ((1)*b+(-1)*x+(-1)*y) (0) (by omega) (by omega)
  have p6 := reducePos n 3 ((1)*b+(-1)*y) (0) (by omega) (by omega)
  have p7 := reducePos n 2 ((-1)*y) (0) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5, p6, p7]
  omega

theorem chartU_17034625 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : a=1) (h1 : b=1) (h2 : x= -a) (h3 : y=a-1) :
    (pos n 0 ((1)+(-1)*a) < pos n 2 ((-1)*y)) ∧
    (pos n 2 ((-1)*y) < pos n 4 (0)) ∧
    (pos n 4 (0) < pos n 3 ((1)+(-1)*a+(-1)*b+(1)*x)) ∧
    (pos n 3 ((1)+(-1)*a+(-1)*b+(1)*x) < pos n 0 ((1)+(-1)*a+(-1)*b)) ∧
    (pos n 0 ((1)+(-1)*a+(-1)*b) < pos n 2 ((-1)*b+(-1)*y)) ∧
    (pos n 2 ((-1)*b+(-1)*y) < pos n 3 ((1)+(-1)*a+(1)*x)) ∧
    (pos n 3 ((1)+(-1)*a+(1)*x) < pos n 4 ((-1)*b)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 0 ((1)+(-1)*a) (0) (by omega) (by omega)
  have p2 := reducePos n 3 ((1)+(-1)*a+(1)*x) (-1) (by omega) (by omega)
  have p3 := reducePos n 3 ((1)+(-1)*a+(-1)*b+(1)*x) (-1) (by omega) (by omega)
  have p4 := reducePos n 0 ((1)+(-1)*a+(-1)*b) (-1) (by omega) (by omega)
  have p5 := reducePos n 4 ((-1)*b) (-1) (by omega) (by omega)
  have p6 := reducePos n 2 ((-1)*b+(-1)*y) (-1) (by omega) (by omega)
  have p7 := reducePos n 2 ((-1)*y) (0) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5, p6, p7]
  omega

theorem chartU_03462517 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : a=b) (h1 : 2≤a) (h2 : 3*a≤n) (h3 : x= -a) (h4 : y=a-1) :
    (pos n 4 (0) < pos n 3 ((1)+(-1)*a+(-1)*b+(1)*x)) ∧
    (pos n 3 ((1)+(-1)*a+(-1)*b+(1)*x) < pos n 0 ((1)+(-1)*a+(-1)*b)) ∧
    (pos n 0 ((1)+(-1)*a+(-1)*b) < pos n 2 ((-1)*b+(-1)*y)) ∧
    (pos n 2 ((-1)*b+(-1)*y) < pos n 3 ((1)+(-1)*a+(1)*x)) ∧
    (pos n 3 ((1)+(-1)*a+(1)*x) < pos n 4 ((-1)*b)) ∧
    (pos n 4 ((-1)*b) < pos n 0 ((1)+(-1)*a)) ∧
    (pos n 0 ((1)+(-1)*a) < pos n 2 ((-1)*y)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 0 ((1)+(-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 3 ((1)+(-1)*a+(1)*x) (-1) (by omega) (by omega)
  have p3 := reducePos n 3 ((1)+(-1)*a+(-1)*b+(1)*x) (-1) (by omega) (by omega)
  have p4 := reducePos n 0 ((1)+(-1)*a+(-1)*b) (-1) (by omega) (by omega)
  have p5 := reducePos n 4 ((-1)*b) (-1) (by omega) (by omega)
  have p6 := reducePos n 2 ((-1)*b+(-1)*y) (-1) (by omega) (by omega)
  have p7 := reducePos n 2 ((-1)*y) (-1) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5, p6, p7]
  omega

theorem chartV_03526174 (n a b x y : Int) (hn : 5 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : 2*a < n) (hB : 2*b < n) (h0 : a=b) (h1 : n<3*a) (h2 : x= -a) (h3 : y=a-1) :
    (pos n 4 (0) < pos n 1 ((-1)+(-1)*a+(-1)*y)) ∧
    (pos n 1 ((-1)+(-1)*a+(-1)*y) < pos n 4 ((-1)+(1)*x+(-1)*y)) ∧
    (pos n 4 ((-1)+(1)*x+(-1)*y) < pos n 1 ((-1)*a+(-1)*y)) ∧
    (pos n 1 ((-1)*a+(-1)*y) < pos n 1 ((-1)+(-1)*y)) ∧
    (pos n 1 ((-1)+(-1)*y) < pos n 4 ((-1)*a)) ∧
    (pos n 4 ((-1)*a) < pos n 1 ((-1)*y)) ∧
    (pos n 1 ((-1)*y) < pos n 4 ((-1)+(-1)*a+(1)*x+(-1)*y)) := by
  have p0 := reducePos n 4 (0) (0) (by omega) (by omega)
  have p1 := reducePos n 4 ((-1)*a) (-1) (by omega) (by omega)
  have p2 := reducePos n 1 ((-1)*a+(-1)*y) (-1) (by omega) (by omega)
  have p3 := reducePos n 1 ((-1)+(-1)*a+(-1)*y) (-1) (by omega) (by omega)
  have p4 := reducePos n 4 ((-1)+(-1)*a+(1)*x+(-1)*y) (-2) (by omega) (by omega)
  have p5 := reducePos n 4 ((-1)+(1)*x+(-1)*y) (-1) (by omega) (by omega)
  have p6 := reducePos n 1 ((-1)+(-1)*y) (-1) (by omega) (by omega)
  have p7 := reducePos n 1 ((-1)*y) (-1) (by omega) (by omega)
  simp only [p0, p1, p2, p3, p4, p5, p6, p7]
  omega

#print axioms chartP_0312
#print axioms chartQ_402315
#print axioms chartQ_023154
#print axioms chartQ_305412
#print axioms chartQ_054123
#print axioms chartR_054123
#print axioms chartS_043512
#print axioms chartR_032451
#print axioms chartR_024153
#print axioms chartT_20734651
#print axioms chartT_20473561
#print axioms chartT_73046521
#print axioms chartU_17034625
#print axioms chartU_03462517
#print axioms chartV_03526174
end SheehanFive
