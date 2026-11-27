import HaarMetaVoltagePullback
import HaarOrbitGroup
import HaarOrbitChains

namespace HaarOrbitActual
open HaarMetaVoltagePullback HaarOrbitGroup HaarOrbitChains
variable {G Q B E : Type*} [Group G] [Group Q]
variable {f : G →* Q} {x y : G}
variable [hc : Fact (∀ (a b : f.ker), a*b=b*a)]
local instance kerComm : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hc.out
local instance addCommK : AddCommGroup (Additive f.ker) := inferInstance

theorem raw_weight (T : Setup f x y B) (u v : B) (j : P)
    (hu : T.side u=false) (ne : u≠v) (nv : T.next u j=v)
    (q : f (T.repr u * port x y j)=f (T.repr v)) :
    HaarMetaVoltagePullback.weight T u v =
      HaarOrbitGroup.weight f (T.repr u) (T.repr v) (port x y j) q := by
  subst v
  have h : good T u (T.next u j) := ⟨hu,ne,j,rfl⟩
  classical
  simp only [HaarMetaVoltagePullback.weight,dite_eq_left h]
  apply Subtype.ext
  exact raw_step T u j ne h

def RawGeometry (T : Setup f x y B) (src dst : E → B) (label : E → P) : Prop :=
  ∀ e, T.side (src e)=false ∧ src e≠dst e ∧ T.next (src e) (label e)=dst e

def Transition (T : Setup f x y B) (src dst : E → B) (label : E → P)
    (tv : B → B) (te : E → E) (g : G) (e : E) : Prop :=
  src (te e)=tv (src e) ∧ dst (te e)=tv (dst e) ∧ label (te e)=label e ∧
    f (g*T.repr (src e))=f (T.repr (tv (src e))) ∧
    f (g*T.repr (dst e))=f (T.repr (tv (dst e)))

/-- Equivariance of normalized edge weights under an allowed quotient translation.
    The translation can be partial: `active` specifies the edges it preserves. -/
theorem normalized_law {k : Nat} [DecidableEq E]
    (T : Setup f x y B) (src dst : E → B) (label : E → P)
    (geom : RawGeometry T src dst label) (cot : Fin k → E)
    (w : Fin k → Additive f.ker) (p : B → Additive f.ker)
    (gauge : ∀ e, normalized cot w e =
      HaarMetaVoltagePullback.weight T (src e) (dst e) + p (src e) - p (dst e))
    (tv : B → B) (te : E → E) (g : G) (active : E → Prop)
    (moves : ∀ e, active e → Transition T src dst label tv te g e) :
    ∃ ψ : Additive f.ker →+ Additive f.ker, ∃ P : B → Additive f.ker,
        ∀ e, active e →
          normalized cot w (te e) = ψ (normalized cot w e) + P (dst e) - P (src e) := by
  classical
  let ψ := conjugation f g
  let off (b : B) : Additive f.ker :=
    if h : f (g*T.repr b)=f (T.repr (tv b)) then offset f (T.repr b) (T.repr (tv b)) g h else 0
  let P (b : B) := off b + ψ (p b) - p (tv b)
  refine ⟨ψ,P,fun e he => ?_⟩
  obtain ⟨u,v,j,hu,hv⟩ := moves e he
  obtain ⟨s0,n0,t0⟩ := geom e
  obtain ⟨s1,n1,t1⟩ := geom (te e)
  have edge0 : f (T.repr (src e) * port x y (label e)) = f (T.repr (dst e)) := by
    rw [map_mul,← T.forward _ _ (by rwa [t0]) s0,t0]
  have edge1 : f (T.repr (src (te e)) * port x y (label (te e))) = f (T.repr (dst (te e))) := by
    rw [map_mul,← T.forward _ _ (by rwa [t1]) s1,t1]
  have eu : f (g*T.repr (src e)) = f (T.repr (src (te e))) := by rwa [u]
  have ev : f (g*T.repr (dst e)) = f (T.repr (dst (te e))) := by rwa [v]
  have Lu : offset f (T.repr (src e)) (T.repr (src (te e))) g eu = off (src e) := by
    simp only [off,dite_eq_left hu]
    apply Subtype.ext
    simp [offset,u]
  have Lv : offset f (T.repr (dst e)) (T.repr (dst (te e))) g ev = off (dst e) := by
    simp only [off,dite_eq_left hv]
    apply Subtype.ext
    simp [offset,v]
  have raw := raw_weight T (src e) (dst e) (label e) s0 n0 t0 edge0
  have edge1' : f (T.repr (src (te e)) * port x y (label e)) = f (T.repr (dst (te e))) := by
    simpa only [j] using edge1
  have t1' : T.next (src (te e)) (label e)=dst (te e) := by simpa only [j] using t1
  have raw' := raw_weight T (src (te e)) (dst (te e)) (label e) s1 n1 t1' edge1' 
  have move : HaarMetaVoltagePullback.weight T (src (te e)) (dst (te e)) =
      ψ (HaarMetaVoltagePullback.weight T (src e) (dst e)) + off (dst e) - off (src e) := by
    rw [raw,raw']
    rw [edge_law f _ _ _ _ _ g edge0 edge1' eu ev,Lu,Lv]
  rw [gauge,gauge,move,u,v]
  simp only [map_sub,map_add,P]
  abel

end HaarOrbitActual
#print axioms HaarOrbitActual.normalized_law
