import RibbonP3Chart
import HaarClass3Collect

namespace RibbonP3

variable {G : Type*} [Group G]

abbrev coord (r : Row) : HaarClass3Table.Coord := (r.i,r.j,r.k,r.l,r.m)
abbrev eval (x y c u v : G) (r : Row) := HaarClass3Collect.norm x y c u v (coord r)

structure Class3 (x y c u v : G) : Prop where
  hu : ∀ z, Commute u z
  hv : ∀ z, Commute v z
  xy : x*y=y*x*c
  cx : c*x=x*c*u
  cy : c*y=y*c*v

def Range (i : ℤ) : Prop := -1 ≤ i ∧ i ≤ 2

theorem x_word_to_y {x y c u v : G} (d : Class3 x y c u v) (i : ℤ) (hi : Range i) :
    x^i*y=y*x^i*c^i*u^(i*(i-1)/2) := by
  have bounds : i=(-1:ℤ) ∨ i=0 ∨ i=1 ∨ i=2 := by unfold Range at hi; omega
  rcases bounds with rfl|rfl|rfl|rfl
  · exact HaarClass3Collect.pow_trans_limited x y c u (d.hu x) (d.hu c) d.xy d.cx (-1) (by decide)
  · simp
  · simpa using d.xy
  · convert (show (x*x)*y = (y*(x*x))*(c*c)*u by
      calc
        (x*x)*y = x*(x*y) := by group
        _ = x*(y*x*c) := by rw [d.xy]
        _ = (x*y)*x*c := by group
        _ = (y*x*c)*x*c := by rw [d.xy]
        _ = y*x*(c*x)*c := by group
        _ = y*x*(x*c*u)*c := by rw [d.cx]
        _ = y*(x*x)*c*(u*c) := by group
        _ = y*(x*x)*c*(c*u) := by rw [(d.hu c).eq]
        _ = (y*(x*x))*(c*c)*u := by group) using 1 <;> norm_num [pow_two]

private def plusX (r : Row) : Row := {r with i := r.i+1, l := r.l+r.k}
private def minusX (r : Row) : Row := {r with i := r.i-1, l := r.l-r.k}
private def plusY (r : Row) : Row :=
  {r with j := r.j+1,k:=r.k+r.i,l:=r.l+r.i*(r.i-1)/2,m:=r.m+r.k}
private def minusY (r : Row) : Row :=
  {r with j := r.j-1,k:=r.k-r.i,l:=r.l-r.i*(r.i-1)/2,m:=r.m-r.k+r.i}

theorem collect_plusX {x y c u v : G} (d : Class3 x y c u v) (r : Row) :
    eval x y c u v (plusX r) = eval x y c u v r * x :=
  HaarClass3Collect.norm_x x y c u v d.hu d.hv d.cx (coord r)

/-- Positive y transport for arbitrary bounded or unbounded exponents, given
the usual power-swap identity for this particular exponent. -/
theorem collect_plusY_of_swap {x y c u v : G} (d : Class3 x y c u v) (r : Row)
    (swap : x^r.i*y = y*x^r.i*c^r.i*u^(r.i*(r.i-1)/2)) :
    eval x y c u v (plusY r) = eval x y c u v r * y := by
  let i := r.i; let j := r.j; let k := r.k; let a := r.l; let b := r.m
  let t : ℤ := i*(i-1)/2
  have cY := HaarCycle.shift c y v (d.hv c) d.cy k
  have uvY : Commute (u^a*v^b) y := ((d.hu y).zpow_left a).mul_left ((d.hv y).zpow_left b)
  have uC : Commute (u^t) (c^k) := (d.hu c).zpow_zpow _ _
  have vU : Commute (v^k) (u^a) := (d.hv u).zpow_zpow _ _
  change y^(j+1)*x^i*c^(k+i)*u^(a+t)*v^(b+k) =
    y^j*x^i*c^k*u^a*v^b*y
  symm
  calc
    y^j*x^i*c^k*u^a*v^b*y = y^j*x^i*c^k*((u^a*v^b)*y) := by simp only [mul_assoc]
    _ = y^j*x^i*(c^k*y)*(u^a*v^b) := by rw [uvY.eq]; simp only [mul_assoc]
    _ = y^j*(x^i*y)*c^k*v^k*u^a*v^b := by rw [cY]; simp only [mul_assoc]
    _ = (y^j*y)*x^i*c^i*u^t*c^k*v^k*u^a*v^b := by
      change x^i*y = y*x^i*c^i*u^t at swap
      rw [swap]
      simp only [mul_assoc]
    _ = (y^j*y)*x^i*(c^i*c^k)*(u^t*u^a)*(v^k*v^b) := by
      simp only [mul_assoc]
      rw [← mul_assoc (u^t) (c^k) _,uC.eq,mul_assoc (c^k) (u^t) _]
      rw [← mul_assoc (v^k) (u^a) _,vU.eq]
      simp only [mul_assoc]
    _ = y^(j+1)*x^i*c^(k+i)*u^(a+t)*v^(b+k) := by
      rw [zpow_add_one,show k+i=i+k by omega,show a+t=t+a by omega,
        show b+k=k+b by omega,zpow_add,zpow_add,zpow_add]

theorem collect_minusX {x y c u v : G} (d : Class3 x y c u v) (r : Row) :
    eval x y c u v (minusX r) = eval x y c u v r * x⁻¹ := by
  have z := collect_plusX d (minusX r)
  have h : plusX (minusX r) = r := by cases r; simp [plusX,minusX]
  rw [h] at z
  rw [z,mul_inv_cancel_right]

theorem collect_minusY_of_swap {x y c u v : G} (d : Class3 x y c u v) (r : Row)
    (swap : x^r.i*y = y*x^r.i*c^r.i*u^(r.i*(r.i-1)/2)) :
    eval x y c u v (minusY r) = eval x y c u v r * y⁻¹ := by
  have z := collect_plusY_of_swap d (minusY r) swap
  have h : plusY (minusY r) = r := by
    cases r
    simp [plusY,minusY]
  rw [h] at z
  rw [z,mul_inv_cancel_right]

/-- Each step in the actual single-matching ribbon chart agrees with the
group word evaluation in the class-three quotient. -/
theorem eval_march {x y c u v : G} (d : Class3 x y c u v) (r : Row) (p : Fin 3)
    (swap : x^r.i*y = y*x^r.i*c^r.i*u^(r.i*(r.i-1)/2)) :
    eval x y c u v (march r p) = eval x y c u v r * trace x y r.rim [p] := by
  fin_cases p
  · cases hs : r.rim
    · simpa [march,hs,trace,plusX] using collect_plusX d r
    · simpa [march,hs,trace,plusY] using collect_plusY_of_swap d r swap
  · cases hs : r.rim
    · simpa [march,hs,trace,minusX] using collect_minusX d r
    · simpa [march,hs,trace,minusY] using collect_minusY_of_swap d r swap
  · simp [march,trace,eval,HaarClass3Collect.norm]

/-- Transfer an entire finite ribbon walk's row computation into the
class-three group where its matching and rim relations hold. -/
theorem eval_fold {x y c u v : G} (d : Class3 x y c u v)
    (w : List (Fin 3)) (r : Row)
    (safe : ∀ r' ∈ w.scanl march r, Range r'.i) :
    eval x y c u v (w.foldl march r) = eval x y c u v r * trace x y r.rim w := by
  induction w generalizing r with
  | nil => simp [trace]
  | cons p w ih =>
    have hs : Range r.i := safe r (by rw [List.scanl_cons]; simp)
    have st : ∀ r' ∈ w.scanl march (march r p), Range r'.i := by
      intro r' h
      exact safe r' (by rw [List.scanl_cons]; exact List.mem_cons_of_mem _ h)
    rw [List.foldl_cons, ih (march r p) st, eval_march d r p (x_word_to_y d r.i hs)]
    fin_cases p <;> cases hs : r.rim <;> simp [march,trace,hs,mul_assoc]

end RibbonP3

#print axioms RibbonP3.eval_march

#print axioms RibbonP3.eval_fold
