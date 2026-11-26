import RibbonP3Collect
import RibbonP3Compare
import RibbonP3Character

namespace RibbonP3
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
    (rim : (row t i).rim=(row t j).rim)
    (e : eval x y c u v (row t i)=eval x y c u v (row t j)) :
    key q t i=key q t j := by
  let P := row t i
  let R := row t j
  have proj (r : Row) :
      f (eval x y c u v r) = HaarCycle.norm (f x) (f y) (f c) (r.i,r.j,r.k) := by
    simp [eval,HaarClass3Collect.norm,HaarCycle.norm,zu,zv]
  have e2 := congrArg f e
  rw [proj,proj] at e2
  have ij := abelian_residues (f x) (f y) (f c) cx cy xy ord
    (P.i,P.j,P.k) (R.i,R.j,R.k) e2
  have ei : P.i%3=R.i%3 := ij.1
  have ej : P.j%3=R.j%3 := ij.2
  have he : abelKey P=abelKey R := by unfold abelKey; rw [rim,ei,ej]
  have ints := integer_abelian_coordinates t i j he
  have ei' : P.i=R.i := ints.1
  have ej' : P.j=R.j := ints.2
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

end RibbonP3
#print axioms RibbonP3.key_sound
