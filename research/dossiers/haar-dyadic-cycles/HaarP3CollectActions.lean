import HaarP3CollectCore

namespace HaarP3CollectActions
open HaarP3CollectCore
variable {G : Type*} [Group G]

structure Params where
  p : ℤ
  q : ℤ
  t0 : ℤ
  t1 : ℤ
  t2 : ℤ
  deriving DecidableEq

def twist (p : Params) := -p.p-p.q

def xC (p : Params) : Coord := ⟨1,-1,0,twist p⟩
def xU : Coord := ⟨0,1,-1,0⟩
def xA (p : Params) : Coord := ⟨0,0,1,-p.p⟩
def yC (p : Params) : Coord := ⟨1,1,1,-p.t0-twist p⟩
def yU (p : Params) : Coord := ⟨0,1,1,-p.t2⟩
def yA (p : Params) : Coord := ⟨0,0,1,-p.q⟩

def act (d s : ℤ) (C U A r : Coord) : Coord :=
  mul d s (mul d s (mul d s (powZ d s C r.k) (powZ d s U r.u))
    (powZ d s A r.a)) ⟨0,0,0,r.z⟩

def actX (p : Params) (r : Coord) : Coord :=
  act (twist p) p.t1 (xC p) xU (xA p) r
def actY (p : Params) (r : Coord) : Coord :=
  act (twist p) p.t1 (yC p) (yU p) (yA p) r

theorem map_act (M : Base G) (f : G →* G) (c u a r : Coord)
    (hc : f M.C=ne M c) (hu : f M.U=ne M u) (ha : f M.A=ne M a) (hz : f M.Z=M.Z) :
    ne M (act M.twist M.carry c u a r) = f (ne M r) := by
  rw [act,ne_mul,ne_mul,ne_mul,ne_powZ,ne_powZ,ne_powZ]
  simp [ne,map_mul,map_zpow,hc,hu,ha,hz]

structure Model (G : Type*) [Group G] extends Base G where
  P : Params
  tw : twist = HaarP3CollectActions.twist P
  ca1 : carry=P.t1
  x : G
  y : G
  xy : x*y=y*x*C
  hxC : MulAut.conj x C = ne toBase (xC P)
  hxU : MulAut.conj x U = ne toBase xU
  hxA : MulAut.conj x A = ne toBase (xA P)
  hyC : MulAut.conj y C = ne toBase (yC P)
  hyU : MulAut.conj y U = ne toBase (yU P)
  hyA : MulAut.conj y A = ne toBase (yA P)

theorem conj_z (M : Model G) (g : G) : MulAut.conj g M.Z = M.Z := by
  change g*M.Z*g⁻¹=M.Z
  rw [(M.zcent g).symm.eq,mul_inv_cancel_right]

theorem ne_actX (M : Model G) (r : Coord) :
    ne M.toBase (actX M.P r) = M.x * ne M.toBase r * M.x⁻¹ := by
  unfold actX
  rw [← M.tw,← M.ca1]
  exact map_act M.toBase (MulEquiv.toMonoidHom (MulAut.conj M.x)) _ _ _ _
    M.hxC M.hxU M.hxA (conj_z M M.x)

theorem ne_actY (M : Model G) (r : Coord) :
    ne M.toBase (actY M.P r) = M.y * ne M.toBase r * M.y⁻¹ := by
  unfold actY
  rw [← M.tw,← M.ca1]
  exact map_act M.toBase (MulEquiv.toMonoidHom (MulAut.conj M.y)) _ _ _ _
    M.hyC M.hyU M.hyA (conj_z M M.y)

end HaarP3CollectActions
#print axioms HaarP3CollectActions.ne_actY
