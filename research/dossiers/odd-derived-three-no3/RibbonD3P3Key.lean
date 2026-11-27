import RibbonP3KeySound

namespace RibbonD3P3
open RibbonP3

def key (q t : Fin 3) (r : Row) : Nat :=
  let c := (r.l + q.val*r.m + (r.k/3)*t.val)%3
  (if r.rim then 1 else 0) + 2*(r.i%3).toNat + 6*(r.j%3).toNat +
    18*(r.k%3).toNat + 54*c.toNat

variable {H Q : Type*} [Group H] [Group Q]

theorem key_of_equal (f : H →* Q) (x y c u v : H)
    (cx : Commute (f c) (f x)) (cy : Commute (f c) (f y))
    (xy : f x*f y=f y*f x*f c) (ord : orderOf (f c)=3)
    (zu : f u=1) (zv : f v=1)
    (S : Subgroup H) (hc : c^3∈S) (hu : u∈S) (hv : v∈S)
    (χ : S →* Multiplicative (ZMod 3)) (q t : Fin 3)
    (fc : χ ⟨c^3,hc⟩ = Multiplicative.ofAdd ((t.val:ℤ):ZMod 3))
    (fu : χ ⟨u,hu⟩ = Multiplicative.ofAdd (1:ZMod 3))
    (fv : χ ⟨v,hv⟩ = Multiplicative.ofAdd ((q.val:ℤ):ZMod 3))
    (P R : Row) (gi : -3 < P.i-R.i ∧ P.i-R.i < 3)
    (gj : -3 < P.j-R.j ∧ P.j-R.j < 3)
    (rim : P.rim=R.rim) (e : eval x y c u v P=eval x y c u v R) :
    key q t P = key q t R := by
  have proj (r : Row) :
      f (eval x y c u v r) = HaarCycle.norm (f x) (f y) (f c) (r.i,r.j,r.k) := by
    simp [eval,HaarClass3Collect.norm,HaarCycle.norm,zu,zv]
  have e2 := congrArg f e
  rw [proj,proj] at e2
  have ij := abelian_residues (f x) (f y) (f c) cx cy xy ord
    (P.i,P.j,P.k) (R.i,R.j,R.k) e2
  have ei : P.i%3=R.i%3 := ij.1
  have ej : P.j%3=R.j%3 := ij.2
  have ei' : P.i=R.i := by omega
  have ej' : P.j=R.j := by omega
  rw [ei',ej'] at e2
  have low := commutator_residue (f x) (f y) (f c) ord R.i R.j P.k R.k e2
  have tail : c^P.k*u^P.l*v^P.m=c^R.k*u^R.l*v^R.m := by
    change y^P.j*x^P.i*c^P.k*u^P.l*v^P.m =
      y^R.j*x^R.i*c^R.k*u^R.l*v^R.m at e
    rw [ei',ej'] at e
    apply mul_left_cancel (a:=y^R.j*x^R.i)
    simpa only [mul_assoc] using e
  have ch := tail_character c u v S hc hu hv χ q.val t.val fc fu fv
    P.k P.l P.m R.k R.l R.m low tail
  unfold key
  rw [rim,ei,ej,low,mul_comm (P.k/3) (t.val:ℤ),mul_comm (R.k/3) (t.val:ℤ),ch]

#print axioms key_of_equal
end RibbonD3P3
