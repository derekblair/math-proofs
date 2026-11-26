import HaarP3CollectActions
import HaarClass5L2Abelian

namespace HaarP3FifthLaws
open HaarP3CollectCore HaarP3CollectActions HaarClass4CollectCore
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem twist_from_actions (x y c u A B z : G) (p q t : ℤ)
    (hxy : x*y=y*x*c) (zc : Central z)
    (b : B=A⁻¹*z^t) (_au : Commute A u)
    (xu : MulAut.conj x u=A⁻¹*u) (yu : MulAut.conj y u=B⁻¹*u)
    (xa : MulAut.conj x A=(z^p)⁻¹*A) (ya : MulAut.conj y A=(z^q)⁻¹*A) :
    c*u=u*c*z^(-p-q) := by
  let X := MulAut.conj x
  let Y := MulAut.conj y
  let K := z^(-p-q)
  have zinv (g : G) : MulAut.conj g z=z := by
    change g*z*g⁻¹=z
    rw [(zc g).symm.eq,mul_inv_cancel_right]
  have xb : X B=B*z^p := by
    change MulAut.conj x B=B*z^p
    rw [b,map_mul,map_inv,map_zpow,xa,zinv,mul_inv_rev,inv_inv]
    rw [mul_assoc,(Commute.refl z).zpow_zpow p t |>.eq,←mul_assoc]
  have ab : Commute A B := by rw [b]; exact (Commute.inv_right (Commute.refl A)).mul_right ((zc A).symm.zpow_right _)
  have l : X (Y u)=(B⁻¹*A⁻¹*u)*(z^p)⁻¹ := by
    change X (MulAut.conj y u)=_
    rw [yu,map_mul,map_inv,xb,show X u=A⁻¹*u from xu,mul_inv_rev]
    calc
      _ = (z^p)⁻¹ * (B⁻¹*A⁻¹*u) := by simp only [mul_assoc]
      _ = _ := (((zc (B⁻¹*A⁻¹*u)).zpow_left p).inv_left).eq
  have r : Y (X u)=(B⁻¹*A⁻¹*u)*z^q := by
    change Y (MulAut.conj x u)=_
    rw [xu,map_mul,map_inv,show Y A=(z^q)⁻¹*A from ya, show Y u=B⁻¹*u from yu,mul_inv_rev,inv_inv]
    have c1 := ((zc (B⁻¹*u)).zpow_left q).eq
    calc
      _ = A⁻¹*(z^q*(B⁻¹*u)) := by simp only [mul_assoc]
      _ = (A⁻¹*B⁻¹)*u*z^q := by rw [c1]; simp only [mul_assoc]
      _ = _ := by rw [ab.inv_left.inv_right.eq]
  have Kspec : (z^q)*K=(z^p)⁻¹ := by
    dsimp [K]
    rw [←zpow_add,show q+(-p-q)=-p by ring,zpow_neg]
  have ec : X (Y u)=Y (X u)*K := by rw [l,r,mul_assoc (B⁻¹*A⁻¹*u),Kspec]
  let F := MulAut.conj (y*x)
  have fe : F (c*u*c⁻¹)=X (Y u) := by
    change (y*x)*(c*u*c⁻¹)*(y*x)⁻¹=x*(y*u*y⁻¹)*x⁻¹
    calc
      _ = ((y*x)*c)*u*((y*x)*c)⁻¹ := by group
      _ = _ := by rw [←hxy]; group
  have ff : F u=Y (X u) := by change (y*x)*u*(y*x)⁻¹=y*(x*u*x⁻¹)*y⁻¹; group
  have fk : F K=K := by change MulAut.conj (y*x) (z^(-p-q))=z^(-p-q); rw [map_zpow,zinv]
  have h : c*u*c⁻¹=u*K := by
    apply F.injective
    rw [fe,ec,map_mul,ff,fk]
  have h' : c*u=u*K*c := mul_inv_eq_iff_eq_mul.mp h
  rw [h',mul_assoc,((zc c).zpow_left (-p-q)).eq,←mul_assoc]

end HaarP3FifthLaws
#print axioms HaarP3FifthLaws.twist_from_actions

namespace HaarP3FifthLaws
open HaarP3CollectCore HaarP3CollectActions HaarClass4CollectCore
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem conj_of_right_comm (g h k : G) (e : ⁅h,g⁆=k) :
    MulAut.conj g h=k⁻¹*h := by
  subst k
  change g*h*g⁻¹=(h*g*h⁻¹*g⁻¹)⁻¹*h
  group

def modelOf (x y c u a z : G) (P : Params)
    (hxy : x*y=y*x*c) (zc : Central z) (ca : Commute c a) (ua : Commute u a)
    (cx : ⁅c,x⁆=u) (cy : ⁅c,y⁆*u*a=z^P.t0)
    (ux : ⁅u,x⁆=a) (uy : ⁅u,y⁆*a=z^P.t2)
    (ax : ⁅a,x⁆=z^P.p) (ay : ⁅a,y⁆=z^P.q)
    (u3 : u^(3:ℤ)=z^P.t1) (a3 : a^(3:ℤ)=1) (z3 : z^(3:ℤ)=1) :
    Model G := by
  let B := ⁅u,y⁆
  have b : B=a⁻¹*z^P.t2 := by
    change B*a=z^P.t2 at uy
    calc
      B = (B*a)*a⁻¹ := by group
      _ = _ := by rw [uy,((zc a).zpow_left _).inv_right.eq]
  have xu := conj_of_right_comm x u a ux
  have yu : MulAut.conj y u=B⁻¹*u := conj_of_right_comm _ _ _ rfl
  have xa := conj_of_right_comm x a _ ax
  have ya := conj_of_right_comm y a _ ay
  have sw : c*u=u*c*z^twist P := twist_from_actions x y c u a B z P.p P.q P.t2
    hxy zc b ua.symm xu yu xa ya
  have sw' : u*c=c*u*z^(-twist P) := by
    calc
      _ = (u*c*z^twist P)*(z^twist P)⁻¹ := by group
      _ = _ := by rw [←sw,zpow_neg]
  let M : Base G := ⟨c,u,a,z,twist P,P.t1,zc,ca,ua,sw,u3,a3,z3⟩
  refine { toBase := M, P := P, tw := rfl, ca1 := rfl, x := x, y := y, xy := hxy,
           hxC := ?_, hxU := ?_, hxA := ?_, hyC := ?_, hyU := ?_, hyA := ?_ }
  · have e := conj_of_right_comm x c u cx
    have q : u⁻¹*c=c*u⁻¹*z^twist P := by
      calc
        u⁻¹*c = u⁻¹*(c*u)*u⁻¹ := by group
        _ = u⁻¹*(u*c*z^twist P)*u⁻¹ := by rw [sw]
        _ = c*(z^twist P*u⁻¹) := by group
        _ = _ := by rw [((zc u).zpow_left _).inv_right.eq,←mul_assoc]
    simpa [ne,xC,M,zpow_neg] using e.trans q
  · simpa [ne,xU,M,ua.inv_right.eq] using xu
  · simpa [ne,xA,M,zpow_neg,((zc a).zpow_left _).inv_left.eq] using xa
  · let v := ⁅c,y⁆
    change v*u*a=z^P.t0 at cy
    have e : v⁻¹=u*a*z^(-P.t0) := by
      rw [zpow_neg,←cy,mul_inv_rev,mul_inv_rev]
      group
    have hh := conj_of_right_comm y c v rfl
    rw [e] at hh
    simp only [ne,yC,M,zpow_one]
    change MulAut.conj y c = c*u*a*z^(-P.t0-twist P)
    calc
      _ = (u*a*z^(-P.t0))*c := hh
      _ = (u*c)*a*z^(-P.t0) := by
        rw [mul_assoc (u*a),((zc c).zpow_left _).eq,←mul_assoc, mul_assoc u,ca.symm.eq]
        simp only [mul_assoc]
      _ = _ := by rw [sw', mul_assoc (c*u), ((zc a).zpow_left _).eq]
                  simp only [mul_assoc]
                  rw [← zpow_add,show -twist P + -P.t0 = -P.t0 - twist P by ring]
  · simp only [ne,yU,M,zpow_zero,zpow_one,one_mul]
    rw [yu,b,mul_inv_rev,inv_inv]
    change (z^P.t2)⁻¹*a*u=u*a*z^(-P.t2)
    rw [mul_assoc,ua.symm.eq,((zc (u*a)).zpow_left _).inv_left.eq,zpow_neg]
  · simpa [ne,yA,M,zpow_neg,((zc a).zpow_left _).inv_left.eq] using ya

end HaarP3FifthLaws
#print axioms HaarP3FifthLaws.modelOf
