import IntegerTrace
import FiniteEdges

namespace PhaseProduct

structure Machine (Q E : Type*) where
  src : E → Q
  dst : E → Q
  ex : E → ℤ
  nu : E → ℤ
  mult : ℤ
  neg : Bool

variable {Q E : Type*} (M : Machine Q E)

def sign (q : Bool) : ℤ := if q then -1 else 1
def s : ℤ := sign M.neg
def phase (q : Bool) := q ^^ M.neg

theorem sign_sq (q : Bool) : sign q * sign q=1 := by cases q <;> decide

theorem phase_sign (q : Bool) : sign (phase M q) = sign q * s M := by
  cases h : M.neg <;> cases q <;> simp [phase,s,sign,h]

structure Node (Q : Type*) where
  loc : Q
  ex : ℤ
  phase : Bool
  deriving DecidableEq

def next (e : E) (p : Node Q) : Node Q :=
  ⟨M.dst e, M.mult*p.ex+M.ex e, phase M p.phase⟩

def cost (e : E) (q : Bool) : ℤ := sign (phase M q)*M.nu e

inductive Path : Q → Q → List E → Prop
  | nil (q : Q) : Path q q []
  | cons (e : E) {q L} : Path (M.dst e) q L → Path (M.src e) q (e::L)

def aug : Node Q → List E → Node Q
  | p, [] => p
  | p,e::es => aug (next M e p) es

def costs : Bool → List E → List ℤ
  | q, [] => []
  | q,e::es => cost M e q :: costs (phase M q) es

theorem aug_ex (p : Node Q) (L : List E) :
    (aug M p L).ex = ScalarTrace.zeval M.mult p.ex (L.map M.ex) := by
  induction L generalizing p with
  | nil => rfl
  | cons e L ih => exact ih (next M e p)

theorem aug_loc {x y : Q} {L : List E} (h : Path M x y L) (v : ℤ) (q : Bool) :
    (aug M ⟨x,v,q⟩ L).loc = y := by
  induction h generalizing v q with
  | nil => rfl
  | cons e w ih => exact ih _ _

theorem fold (p : Node Q) (z : ℤ) (L : List E) :
    sign (aug M p L).phase * ScalarTrace.zeval (s M) z (L.map M.nu) =
      sign p.phase*z + (costs M p.phase L).sum := by
  induction L generalizing p z with
  | nil => simp [aug,costs,ScalarTrace.zeval]
  | cons e L ih =>
    simp only [aug,List.map_cons,ScalarTrace.zeval,costs,List.sum_cons,ih,next,cost]
    rw [phase_sign]
    rw [← add_assoc]
    congr 1
    exact NeutralAffine.phase_step _ _ _ _ (sign_sq M.neg)

theorem zero_iff (p : Node Q) (L : List E) :
    ScalarTrace.zeval (s M) 0 (L.map M.nu)=0 ↔ (costs M p.phase L).sum=0 := by
  have h := fold M p 0 L
  rw [mul_zero,zero_add] at h
  rw [← h]
  exact (NeutralAffine.phase_zero _ _ (sign_sq _)).symm

end PhaseProduct

#print axioms PhaseProduct.aug_ex
#print axioms PhaseProduct.zero_iff
