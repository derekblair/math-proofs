import HaarMetaTorsionOneVoltage
import HaarMetaVoltagePullback

namespace HaarMetaTorsionOneGeometry
open HaarMetaTorsionOneVoltage HaarMetaVoltagePullback
variable {G Q : Type*} [Group G] [CommGroup Q]

def coord (u : B) : Fin 4 × Fin 3 :=
  (⟨(u.val%12)/3,by omega⟩,⟨u.val%3,by omega⟩)
def side (u : B) : Bool := decide (12≤u.val)
def repr (z t : G) (u : B) : G := z^(coord u).1.val*t^(coord u).2.val

theorem geo_inj : Function.Injective (fun u : B => (side u,coord u)) := by decide +kernel
theorem geoflip : ∀ u j, u≠next u j → side (next u j)= !side u := by decide +kernel
theorem georev : ∀ u j, u≠next u j → next (next u j) j=u := by decide +kernel
theorem geounique : ∀ u j k, u≠next u j → next u j=next u k → j=k := by decide +kernel
theorem geo0 : ∀ u, u≠next u 0 → side u=false → coord (next u 0)=coord u := by decide +kernel
theorem geo1 : ∀ u, u≠next u 1 → side u=false →
    (coord (next u 1)).1=(coord u).1 ∧
    (coord (next u 1)).2.val=((coord u).2.val+1)%3 := by decide +kernel
theorem geo2 : ∀ u, u≠next u 2 → side u=false →
    (coord (next u 2)).1.val=(coord u).1.val+1 ∧
    (coord (next u 2)).2=(coord u).2 := by decide +kernel

theorem wrap_pow (g : Q) (hc : g^(3:ℕ)=1) (i : Fin 3) :
    g^((i.val+1)%3)=g^i.val*g := by
  fin_cases i
  · simp
  · simp [pow_two]
  · change g^(0:ℕ)=g^(2:ℕ)*g
    rw [pow_zero,←pow_succ]
    exact hc.symm

def setup (f : G→*Q) (x y z t : G) (px : f x=f t) (py : f y=f z) (ht : (f t)^(3:ℕ)=1)
    (inj : Function.Injective (fun u : Fin 4 × Fin 3 => f (z^u.1.val*t^u.2.val))) :
    Setup f x y B := by
  refine ⟨next,side,repr z t,?_,geoflip,georev,geounique,?_⟩
  · intro u v e
    apply geo_inj
    have s : side u=side v := congrArg (fun p : Bool × Q => p.1) e
    have t' : f (repr z t u)=f (repr z t v) := congrArg (fun p : Bool × Q => p.2) e
    exact Prod.ext s (inj t')
  · intro u j ne h
    fin_cases j
    · change f (repr z t (next u 0))=f (repr z t u)*f (HaarMetaVoltagePullback.port x y 0)
      have q := geo0 u ne h
      simp [repr,q,HaarMetaVoltagePullback.port]
    · change f (repr z t (next u 1))=f (repr z t u)*f (HaarMetaVoltagePullback.port x y 1)
      have ⟨p,q⟩ := geo1 u ne h
      simp only [repr,map_mul,map_pow,p,q]
      rw [wrap_pow _ ht,←mul_assoc]
      simp [HaarMetaVoltagePullback.port,px]
    · change f (repr z t (next u 2))=f (repr z t u)*f (HaarMetaVoltagePullback.port x y 2)
      have ⟨p,q⟩ := geo2 u ne h
      simp only [repr,map_mul,map_pow,p,q,pow_succ]
      simp only [HaarMetaVoltagePullback.port,Fin.val_two,show ¬(2:ℕ)=0 by decide,
        show ¬(2:ℕ)=1 by decide,ite_false,py]
      ac_rfl

end HaarMetaTorsionOneGeometry
#print axioms HaarMetaTorsionOneGeometry.setup
