import HaarP3CollectActions
import HaarHalfCollision

namespace HaarP3CollectSteps
open HaarP3CollectCore HaarP3CollectActions
variable {G : Type*} [Group G]

structure Grid where
  i : ℤ
  j : ℤ
  n : Coord
  deriving DecidableEq, Inhabited

def ev (M : Model G) (r : Grid) :=
  M.y^r.j * M.x^r.i * ne M.toBase r.n

def mulP (p : Params) := mul (twist p) p.t1
def invP (p : Params) := neg (twist p)
def f2 (p : Params) : Coord :=
  mulP p ⟨1,1,1,p.p-twist p⟩ basisC

def corr (p : Params) (i : ℤ) : Coord :=
  if i = -1 then actX p (invP p basisC) else
  if i = 1 then basisC else
  if i = 2 then f2 p else zero

def corrTest (p : Params) : Prop :=
  actX p (f2 p) = mulP p basisC (actX p basisC)
instance (p : Params) : Decidable (corrTest p) := by unfold corrTest; infer_instance

theorem eval_mulP (M : Model G) (a b : Coord) :
    ne M.toBase (mulP M.P a b) = ne M.toBase a * ne M.toBase b := by
  rw [mulP,← M.tw,← M.ca1,ne_mul]

theorem eval_invP (M : Model G) (a : Coord) :
    ne M.toBase (invP M.P a) = (ne M.toBase a)⁻¹ := by
  rw [invP,← M.tw,ne_neg]

theorem corr_eval (M : Model G) (hc : corrTest M.P) (i : ℤ)
    (hi : i = -1 ∨ i=0 ∨ i=1 ∨ i=2) :
    M.x^i*M.y = M.y*M.x^i*ne M.toBase (corr M.P i) := by
  rcases hi with rfl | rfl | rfl | rfl
  · simp only [corr,ite_true,ne_actX,eval_invP,ne_C,zpow_neg_one]
    have t : M.y*M.x=M.x*M.y*M.C⁻¹ := by rw [M.xy,mul_inv_cancel_right]
    calc
      M.x⁻¹*M.y = M.x⁻¹*(M.y*M.x)*M.x⁻¹ := by group
      _ = _ := by rw [t]; group
  · simp [corr,ne_zero]
  · simpa [corr,ne_C] using M.xy
  · have h := congrArg (ne M.toBase) hc
    rw [ne_actX,eval_mulP,ne_actX,ne_C] at h
    have g : ne M.toBase (f2 M.P)=M.x⁻¹*M.C*M.x*M.C := by
      calc
        _= M.x⁻¹*(M.x*ne M.toBase (f2 M.P)*M.x⁻¹)*M.x := by group
        _= _ := by rw [h]; group
    simp only [corr,show (2:ℤ)≠-1 by decide,show (2:ℤ)≠1 by decide,ite_false,ite_true,g]
    calc
      M.x^(2:ℤ)*M.y = M.x*(M.x*M.y) := by rw [zpow_two,mul_assoc]
      _ = M.x*(M.y*M.x*M.C) := congrArg (M.x*·) M.xy
      _ = (M.x*M.y)*M.x*M.C := by group
      _ = M.y*M.x^(2:ℤ)*(M.x⁻¹*M.C*M.x*M.C) := by rw [M.xy,zpow_two]; group

def negStep (p : Params) (port : Fin 3) (r : Grid) : Grid :=
  if port=0 then r else
  if port=1 then ⟨r.i-1,r.j,actX p r.n⟩ else
  ⟨r.i,r.j-1,actY p (mulP p (invP p (corr p r.i)) r.n)⟩

def rangeI (r : Grid) : Prop := r.i = -1 ∨ r.i=0 ∨ r.i=1 ∨ r.i=2
instance (r : Grid) : Decidable (rangeI r) := by unfold rangeI; infer_instance

theorem negStep_eval (M : Model G) (hc : corrTest M.P) (port : Fin 3) (r : Grid)
    (hr : port=2 → rangeI r) :
    ev M (negStep M.P port r) = ev M r * (HaarHalfCollision.port M.x M.y port)⁻¹ := by
  fin_cases port
  · simp [negStep,HaarHalfCollision.port]
  · change ev M (negStep M.P 1 r) = ev M r * (HaarHalfCollision.port M.x M.y 1)⁻¹
    simp only [negStep,show (1:Fin 3)≠0 by decide,ite_false,ite_true,
      HaarHalfCollision.port,ev,ne_actX,zpow_sub,zpow_one]
    group
  · change ev M (negStep M.P 2 r) = ev M r * (HaarHalfCollision.port M.x M.y 2)⁻¹
    have h := corr_eval M hc r.i (hr rfl)
    simp only [negStep,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,
      ite_false,HaarHalfCollision.port,ev,ne_actY,eval_mulP,eval_invP,zpow_sub,zpow_one]
    have g : M.y⁻¹*M.x^r.i*M.y=M.x^r.i*ne M.toBase (corr M.P r.i) := by
      rw [mul_assoc,h]
      group
    calc
      _ = M.y^r.j*(M.y⁻¹*M.x^r.i*M.y)*(ne M.toBase (corr M.P r.i))⁻¹*ne M.toBase r.n*M.y⁻¹ := by group
      _ = _ := by rw [g]; group

end HaarP3CollectSteps
#print axioms HaarP3CollectSteps.negStep_eval
