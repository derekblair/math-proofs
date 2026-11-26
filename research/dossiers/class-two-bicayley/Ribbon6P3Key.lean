import Ribbon6P3Chart
import RibbonP3Collect
import RibbonP3Compare
import RibbonP3Character

namespace Ribbon6
open RibbonP3
variable {G Q : Type*} [Group G] [Group Q]

theorem key_sound (f : G →* Q) (x y c u v : G)
    (cx : Commute (f c) (f x)) (cy : Commute (f c) (f y))
    (xy : f x*f y=f y*f x*f c) (ord : orderOf (f c)=3)
    (zu : f u=1) (zv : f v=1)
    (S : Subgroup G) (hc : c^3∈S) (hu : u∈S) (hv : v∈S)
    (χ : S →* Multiplicative (ZMod 3)) (q t : Fin 3)
    (fc : χ ⟨c^3,hc⟩ = Multiplicative.ofAdd ((t.val:ℤ):ZMod 3))
    (fu : χ ⟨u,hu⟩ = Multiplicative.ofAdd (1:ZMod 3))
    (fv : χ ⟨v,hv⟩ = Multiplicative.ofAdd ((q.val:ℤ):ZMod 3))
    (i j : Fin 64)
    (rim : (prow i).rim=(prow j).rim)
    (e : eval x y c u v (prow i)=eval x y c u v (prow j)) :
    pkey q t i=pkey q t j := by
  let P := prow i
  let R := prow j
  have proj (r : Row) :
      f (eval x y c u v r) = HaarCycle.norm (f x) (f y) (f c) (r.i,r.j,r.k) := by
    simp [eval,HaarClass3Collect.norm,HaarCycle.norm,zu,zv]
  have e2 := congrArg f e
  rw [proj,proj] at e2
  have ij := abelian_residues (f x) (f y) (f c) cx cy xy ord
    (P.i,P.j,P.k) (R.i,R.j,R.k) e2
  have ei : P.i%3=R.i%3 := ij.1
  have ej : P.j%3=R.j%3 := ij.2
  have B (k : Fin 64) : 0≤(prow k).i ∧ (prow k).i≤2 ∧ -2≤(prow k).j ∧ (prow k).j≤0 :=
    (by decide +kernel : ∀ n : Fin 64, 0≤(prow n).i ∧ (prow n).i≤2 ∧ -2≤(prow n).j ∧ (prow n).j≤0) k
  have ei' : P.i=R.i := by
    have L := (B i).1
    have U := (B i).2.1
    have L' := (B j).1
    have U' := (B j).2.1
    change 0≤P.i at L; change P.i≤2 at U
    change 0≤R.i at L'; change R.i≤2 at U'
    omega
  have ej' : P.j=R.j := by
    have L := (B i).2.2.1
    have U := (B i).2.2.2
    have L' := (B j).2.2.1
    have U' := (B j).2.2.2
    change -2≤P.j at L; change P.j≤0 at U
    change -2≤R.j at L'; change R.j≤0 at U'
    omega
  change HaarCycle.norm (f x) (f y) (f c) (P.i,P.j,P.k) =
    HaarCycle.norm (f x) (f y) (f c) (R.i,R.j,R.k) at e2
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
  change (if P.rim then 1 else 0) + 2*(P.i%3).toNat + 6*(P.j%3).toNat +
    18*(P.k%3).toNat + 54*((P.l+q.val*P.m+(P.k/3)*t.val)%3).toNat = _
  change (if P.rim then 1 else 0) + 2*(P.i%3).toNat + 6*(P.j%3).toNat +
    18*(P.k%3).toNat + 54*((P.l+q.val*P.m+(P.k/3)*t.val)%3).toNat =
    (if R.rim then 1 else 0) + 2*(R.i%3).toNat + 6*(R.j%3).toNat +
    18*(R.k%3).toNat + 54*((R.l+q.val*R.m+(R.k/3)*t.val)%3).toNat
  rw [rim,ei,ej,low,mul_comm (P.k/3) (t.val:ℤ),mul_comm (R.k/3) (t.val:ℤ),ch]

end Ribbon6
#print axioms Ribbon6.key_sound
