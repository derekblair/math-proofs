import HaarClass4Graph

namespace HaarClass4Projection
open HaarClass4Normal HaarClass4Table

variable {G H : Type*} [Group G] [Group H]

structure KillsTail (M : Data G) (φ : G →* H) : Prop where
  a : φ M.a=1
  b : φ M.b=1
  d : φ M.d=1

structure KillsMid (M : Data G) (φ : G →* H) extends KillsTail M φ : Prop where
  u : φ M.u=1
  v : φ M.v=1

theorem projected (M : Data G) (φ : G →* H) (h : KillsMid M φ) (p : Row) :
    φ (eval M p) = HaarCycle.norm (φ M.x) (φ M.y) (φ M.c) (p.i,p.j,p.c) := by
  simp [eval,tail,mid,HaarCycle.norm,h.a,h.b,h.d,h.u,h.v,mul_assoc]

theorem power_one {g : H} {i j : ℤ} (e : g^i=g^j) : g^(i-j)=1 := by
  rw [zpow_sub,e,mul_inv_cancel]

theorem projections_of_equal (M : Data G) (φ : G →* H) (h : KillsMid M φ)
    (p q : Row) (eq : eval M p = eval M q) :
    (φ M.c)^((diff p q).i) = 1 ∧ (φ M.c)^((diff p q).j) = 1 ∧
    ((diff p q).i=0 → (diff p q).j=0 → (φ M.c)^((diff p q).c)=1) := by
  let X := φ M.x
  let Y := φ M.y
  let C := φ M.c
  let P : HaarCycle.Coord := (p.i,p.j,p.c)
  let Q : HaarCycle.Coord := (q.i,q.j,q.c)
  have cx : Commute C X := by
    change φ M.c*φ M.x=φ M.x*φ M.c
    simpa [h.u,h.a] using congrArg φ M.cx
  have cy : Commute C Y := by
    change φ M.c*φ M.y=φ M.y*φ M.c
    simpa [h.v,h.d] using congrArg φ M.cy
  have r : X*Y=Y*X*C := by simpa [X,Y,C] using congrArg φ M.xy
  have e : HaarCycle.norm X Y C P=HaarCycle.norm X Y C Q :=
    (projected M φ h p).symm.trans ((congrArg φ eq).trans (projected M φ h q))
  have hI : C^P.1=C^Q.1 := by
    apply mul_left_cancel (a:=Y*HaarCycle.norm X Y C P)
    rw [← HaarCycle.normShiftY X Y C cx cy r P,e,HaarCycle.normShiftY X Y C cx cy r Q,←e]
  have hJ : C^(-P.2.1)=C^(-Q.2.1) := by
    apply mul_left_cancel (a:=X*HaarCycle.norm X Y C P)
    rw [← HaarCycle.normShiftX X Y C cx cy r P,e,HaarCycle.normShiftX X Y C cx cy r Q,←e]
  refine ⟨power_one hI.symm,?_ ,?_⟩
  · have s := power_one hJ
    change C^(-p.j- -q.j) = 1 at s
    rw [show -p.j- -q.j=q.j-p.j by ring] at s
    exact s
  · intro hi hj
    have ha : q.i=p.i := sub_eq_zero.mp hi
    have hb : q.j=p.j := sub_eq_zero.mp hj
    change Y^p.j*X^p.i*C^p.c=Y^q.j*X^q.i*C^q.c at e
    rw [ha,hb] at e
    exact power_one (mul_left_cancel e).symm

theorem equal_diff (M : Data G) (p q : Row) (hi : (diff p q).i=0)
    (hj : (diff p q).j=0) (eq : eval M p=eval M q) :
    eval M (diff p q)=1 := by
  have ha : q.i=p.i := sub_eq_zero.mp hi
  have hb : q.j=p.j := sub_eq_zero.mp hj
  let m := mid M p.c p.u p.v
  let t := tail M p.a p.b p.d
  let dm := mid M (q.c-p.c) (q.u-p.u) (q.v-p.v)
  let dt := tail M (q.a-p.a) (q.b-p.b) (q.d-p.d)
  have e : eval M (diff p q)=dm*dt := by simp [eval,hi,hj,diff,dm,dt,sub_eq_zero.mpr ha,sub_eq_zero.mpr hb]
  have H : eval M p * eval M (diff p q)=eval M q := by
    rw [e]
    change (M.y^p.j*M.x^p.i*(m*t))*(dm*dt)=_
    have c : Commute t dm := tail_center M _ _ _ _
    calc
      (M.y^p.j*M.x^p.i*(m*t))*(dm*dt) =
          (M.y^p.j*M.x^p.i)*((m*(t*dm))*dt) := by simp only [mul_assoc]
      _ = (M.y^p.j*M.x^p.i)*((m*dm)*(t*dt)) := by rw [c.eq]; simp only [mul_assoc]
      _ = eval M q := by
        unfold m dm t dt
        rw [mid_add,tail_add]
        simp [eval,ha,hb]
  rw [← eq] at H
  exact mul_left_cancel (H.trans (mul_one _).symm)

end HaarClass4Projection

#print axioms HaarClass4Projection.projections_of_equal
#print axioms HaarClass4Projection.equal_diff
