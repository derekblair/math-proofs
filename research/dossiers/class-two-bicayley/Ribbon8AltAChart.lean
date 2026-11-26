import Ribbon8Free
import Ribbon7Algebra

namespace Ribbon8AltA
open Ribbon5Bridge Ribbon8Free
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 32000
set_option maxHeartbeats 0

def la : List P := [0,2,1,2,1,2,1,2,1,2,0,0,2,0,2,1,2,0,2,0,2,1,1,2,1,1,2,0,2,0,0,2]
def wa : Array P := la.toArray
def ta : Array Q := #[(false,0,0,0),(false,1,0,0),(true,1,0,0),(true,1,-1,-1),(false,1,-1,-1),(false,0,-1,-1),(true,0,-1,-1),(true,0,-2,-1),(false,0,-2,-1),(false,-1,-2,-1),(true,-1,-2,-1),(true,-1,-1,-2),(true,-1,0,-3),(false,-1,0,-3),(false,0,0,-3),(true,0,0,-3),(true,0,-1,-3),(false,0,-1,-3),(false,1,-1,-3),(true,1,-1,-3),(true,1,0,-2),(false,1,0,-2),(false,0,0,-2),(false,-1,0,-2),(true,-1,0,-2),(true,-1,-1,-1),(true,-1,-2,0),(false,-1,-2,0),(false,0,-2,0),(true,0,-2,0),(true,0,-1,0),(true,0,0,0),(false,0,0,0)]
def lw : List P := [0,2,1,2,1,2,1,2,1,2,0,0,2,0,2,1,2,0,2,0,2,1,1,2,1,1,2,0,2,0,0,2,0,2,1,2,1,2,0,2,1,2,1,1,2,0,2,0,2,0,2,0,2,1,2,1,1,2,1,2,0,0,2,0]
def ww : Array P := lw.toArray
def tw : Array Q := #[(false,0,0,0),(false,1,0,0),(true,1,0,0),(true,1,-1,-1),(false,1,-1,-1),(false,0,-1,-1),(true,0,-1,-1),(true,0,-2,-1),(false,0,-2,-1),(false,-1,-2,-1),(true,-1,-2,-1),(true,-1,-1,-2),(true,-1,0,-3),(false,-1,0,-3),(false,0,0,-3),(true,0,0,-3),(true,0,-1,-3),(false,0,-1,-3),(false,1,-1,-3),(true,1,-1,-3),(true,1,0,-2),(false,1,0,-2),(false,0,0,-2),(false,-1,0,-2),(true,-1,0,-2),(true,-1,-1,-1),(true,-1,-2,0),(false,-1,-2,0),(false,0,-2,0),(true,0,-2,0),(true,0,-1,0),(true,0,0,0),(false,0,0,0),(false,1,0,0),(true,1,0,0),(true,1,-1,-1),(false,1,-1,-1),(false,0,-1,-1),(true,0,-1,-1),(true,0,0,-1),(false,0,0,-1),(false,-1,0,-1),(true,-1,0,-1),(true,-1,-1,0),(true,-1,-2,1),(false,-1,-2,1),(false,0,-2,1),(true,0,-2,1),(true,0,-1,1),(false,0,-1,1),(false,1,-1,1),(true,1,-1,1),(true,1,0,2),(false,1,0,2),(false,0,0,2),(true,0,0,2),(true,0,-1,2),(true,0,-2,2),(false,0,-2,2),(false,-1,-2,2),(true,-1,-2,2),(true,-1,-1,1),(true,-1,0,0),(false,-1,0,0),(false,0,0,0)]
def lt : List P := [0,2,1,2,1,2,1,2,1,2,0,0,2,0,2,1,2,0,2,0,2,1,1,2,1,1,2,0,2,0,0,2,0,2,1,2,1,2,0,2,1,2,1,1,2,0,2,0,2,0,2,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,2,1,2,0,2,1,2,1,1,2,0,2,0,2,0,2,0,2,1,1,2,1,1,2,0,2,0,0,2,0,2,1,2,1,2,1,2,1,2,0,0,2,0,2,1,2,0,2,0,2,1,2,1,1,2,1,2,0,0,2,0]
def wt : Array P := lt.toArray
def tt : Array Q := #[(false,0,0,0),(false,1,0,0),(true,1,0,0),(true,1,-1,-1),(false,1,-1,-1),(false,0,-1,-1),(true,0,-1,-1),(true,0,-2,-1),(false,0,-2,-1),(false,-1,-2,-1),(true,-1,-2,-1),(true,-1,-1,-2),(true,-1,0,-3),(false,-1,0,-3),(false,0,0,-3),(true,0,0,-3),(true,0,-1,-3),(false,0,-1,-3),(false,1,-1,-3),(true,1,-1,-3),(true,1,0,-2),(false,1,0,-2),(false,0,0,-2),(false,-1,0,-2),(true,-1,0,-2),(true,-1,-1,-1),(true,-1,-2,0),(false,-1,-2,0),(false,0,-2,0),(true,0,-2,0),(true,0,-1,0),(true,0,0,0),(false,0,0,0),(false,1,0,0),(true,1,0,0),(true,1,-1,-1),(false,1,-1,-1),(false,0,-1,-1),(true,0,-1,-1),(true,0,0,-1),(false,0,0,-1),(false,-1,0,-1),(true,-1,0,-1),(true,-1,-1,0),(true,-1,-2,1),(false,-1,-2,1),(false,0,-2,1),(true,0,-2,1),(true,0,-1,1),(false,0,-1,1),(false,1,-1,1),(true,1,-1,1),(true,1,0,2),(false,1,0,2),(false,0,0,2),(true,0,0,2),(true,0,-1,2),(true,0,-2,2),(false,0,-2,2),(false,-1,-2,2),(true,-1,-2,2),(true,-1,-1,1),(true,-1,0,0),(false,-1,0,0),(false,0,0,0),(false,1,0,0),(true,1,0,0),(true,1,-1,-1),(false,1,-1,-1),(false,0,-1,-1),(true,0,-1,-1),(true,0,0,-1),(false,0,0,-1),(false,-1,0,-1),(true,-1,0,-1),(true,-1,-1,0),(true,-1,-2,1),(false,-1,-2,1),(false,0,-2,1),(true,0,-2,1),(true,0,-1,1),(false,0,-1,1),(false,1,-1,1),(true,1,-1,1),(true,1,0,2),(false,1,0,2),(false,0,0,2),(false,-1,0,2),(true,-1,0,2),(true,-1,-1,3),(true,-1,-2,4),(false,-1,-2,4),(false,0,-2,4),(true,0,-2,4),(true,0,-1,4),(true,0,0,4),(false,0,0,4),(false,1,0,4),(true,1,0,4),(true,1,-1,3),(false,1,-1,3),(false,0,-1,3),(true,0,-1,3),(true,0,-2,3),(false,0,-2,3),(false,-1,-2,3),(true,-1,-2,3),(true,-1,-1,2),(true,-1,0,1),(false,-1,0,1),(false,0,0,1),(true,0,0,1),(true,0,-1,1),(false,0,-1,1),(false,1,-1,1),(true,1,-1,1),(true,1,0,2),(false,1,0,2),(false,0,0,2),(true,0,0,2),(true,0,-1,2),(true,0,-2,2),(false,0,-2,2),(false,-1,-2,2),(true,-1,-2,2),(true,-1,-1,1),(true,-1,0,0),(false,-1,0,0),(false,0,0,0)]

def lu : List Ltr := [0,3,1,3,1,2,2,0,3,0,2,1]
def lv : List Ltr := [1,3,3,0,2,2]
def origA : List Ltr := [0,3,1,3,1,2,2,0,3,0,2,1,1,3,3,0,2,2]
def origW : List Ltr := [0,3,1,3,1,2,2,0,3,0,2,1,1,3,3,0,2,2,0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]

def U (x y : G) : G := ev x y lu
def V (x y : G) : G := ev x y lv
def R (x y : G) : G := U x y * V x y
def Z (x y : G) : G := ⁅U x y,V x y⁆

structure Mate where
  i : Nat
  j : Nat
  kind : Fin 6
  conjugator : List Ltr
  deriving Inhabited

def mates : Array Mate := #[
  ⟨0,32,0,[]⟩,
  ⟨1,33,0,[1]⟩,
  ⟨2,34,0,[1]⟩,
  ⟨3,35,0,[2,1]⟩,
  ⟨4,36,0,[2,1]⟩,
  ⟨5,37,0,[0,2,1]⟩,
  ⟨6,38,0,[0,2,1]⟩,
  ⟨0,64,2,[]⟩,
  ⟨32,64,1,[1,3,3,0,2,2]⟩,
  ⟨1,65,2,[1]⟩,
  ⟨33,65,1,[1,1,3,3,0,2,2]⟩,
  ⟨2,66,2,[1]⟩,
  ⟨34,66,1,[1,1,3,3,0,2,2]⟩,
  ⟨3,67,2,[2,1]⟩,
  ⟨35,67,1,[2,1,1,3,3,0,2,2]⟩,
  ⟨4,68,2,[2,1]⟩,
  ⟨36,68,1,[2,1,1,3,3,0,2,2]⟩,
  ⟨5,69,2,[0,2,1]⟩,
  ⟨37,69,1,[0,2,1,1,3,3,0,2,2]⟩,
  ⟨6,70,2,[0,2,1]⟩,
  ⟨38,70,1,[0,2,1,1,3,3,0,2,2]⟩,
  ⟨39,71,1,[3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨40,72,1,[3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨41,73,1,[0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨42,74,1,[0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨43,75,1,[2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨44,76,1,[2,2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨45,77,1,[2,2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨46,78,1,[1,2,2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨47,79,1,[1,2,2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨48,80,1,[3,1,2,2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨49,81,1,[3,1,2,2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨50,82,1,[1,3,1,2,2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨51,83,1,[1,3,1,2,2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨52,84,1,[3,1,3,1,2,2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨53,85,1,[3,1,3,1,2,2,0,3,0,2,1,1,3,3,0,2,2]⟩,
  ⟨54,86,1,[]⟩,
  ⟨48,112,3,[2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨80,112,0,[2,1,3,3,0,2,0,2,1]⟩,
  ⟨49,113,3,[2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨81,113,0,[2,1,3,3,0,2,0,2,1]⟩,
  ⟨50,114,3,[1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨82,114,0,[1,2,1,3,3,0,2,0,2,1]⟩,
  ⟨51,115,3,[1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨83,115,0,[1,2,1,3,3,0,2,0,2,1]⟩,
  ⟨52,116,3,[3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨84,116,0,[3,1,2,1,3,3,0,2,0,2,1]⟩,
  ⟨53,117,3,[3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨85,117,0,[3,1,2,1,3,3,0,2,0,2,1]⟩,
  ⟨54,118,3,[0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨86,118,0,[0,3,1,2,1,3,3,0,2,0,2,1]⟩,
  ⟨55,119,3,[0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨56,120,3,[2,0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨57,121,3,[2,2,0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨58,122,3,[2,2,0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨59,123,3,[0,2,2,0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨60,124,3,[0,2,2,0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨61,125,3,[3,0,2,2,0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨62,126,3,[3,3,0,2,2,0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩,
  ⟨63,127,3,[3,3,0,2,2,0,3,1,2,1,3,3,0,2,0,2,1,3,3,1,2,2,0]⟩]

def row (n : Fin 60) : Mate := mates[n.val]!

def names (k : Fin 6) : List Ltr :=
  ![origA,rev origA,origW,rev origW,origA++rev origW,rev origA++origW] k

def target (x y : G) (k : Fin 6) : G :=
  ![R x y,(R x y)⁻¹,Z x y,(Z x y)⁻¹,R x y*(Z x y)⁻¹,(R x y)⁻¹*Z x y] k

def low (p q : Q) : Prop :=
  p.1≠q.1 ∨ (0<(p.2.1-q.2.1).natAbs ∧ (p.2.1-q.2.1).natAbs≤2) ∨
    (0<(p.2.2.1-q.2.2.1).natAbs ∧ (p.2.2.1-q.2.2.1).natAbs≤2) ∨
    (p.2.1=q.2.1 ∧ p.2.2.1=q.2.2.1 ∧
      0<(p.2.2.2-q.2.2.2).natAbs ∧ (p.2.2.2-q.2.2.2).natAbs≤7)
instance (p q : Q) : Decidable (low p q) := by unfold low; infer_instance

def covered (i j : Nat) : Prop := ∃ k : Fin 60, (row k).i=i ∧ (row k).j=j
instance (i j : Nat) : Decidable (covered i j) := by unfold covered; infer_instance

theorem astep : ∀ i : Fin 32, push ta[i.val]! wa[i.val]! = ta[i.val+1]! := by decide +kernel
theorem wstep : ∀ i : Fin 64, push tw[i.val]! ww[i.val]! = tw[i.val+1]! := by decide +kernel
theorem tstep : ∀ i : Fin 128, push tt[i.val]! wt[i.val]! = tt[i.val+1]! := by decide +kernel
theorem achart : ∀ (i j : Fin 32), i.val<j.val → low ta[i.val]! ta[j.val]! := by decide +kernel
theorem wchart : ∀ (i j : Fin 64), i.val<j.val → low tw[i.val]! tw[j.val]! ∨
    (∃ k : Fin 60, (row k).i=i.val ∧ (row k).j=j.val ∧ (row k).kind.val≤1) := by decide +kernel
theorem tchart : ∀ (i j : Fin 128), i.val<j.val → low tt[i.val]! tt[j.val]! ∨ covered i.val j.val := by decide +kernel

theorem certificate : ∀ k : Fin 60,
    let m := row k
    reduce (rev (encode false (lt.take m.i)) ++ encode false (lt.take m.j)) =
    reduce (m.conjugator ++ names m.kind ++ rev m.conjugator) := by decide +kernel

theorem a_eq (x y : G) : ev x y origA = R x y := by
  rw [show origA=lu++lv by decide, ev_append]
  rfl

theorem w_eq (x y : G) : ev x y origW = Z x y := by
  have H : reduce origW=reduce (lu++lv++rev lu++rev lv) := by decide +kernel
  rw [sound x y _ _ H]
  simp [ev_append,ev_rev,Z,U,V,commutatorElement_def,mul_assoc]

theorem target_eq (x y : G) (k : Fin 6) : ev x y (names k)=target x y k := by
  fin_cases k <;> simp [names,target,ev_append,ev_rev,a_eq,w_eq]

theorem mate_sound (x y : G) (k : Fin 60) :
  let m := row k
  (Ribbon5Law.trace x y false (lt.take m.i))⁻¹ *
    Ribbon5Law.trace x y false (lt.take m.j) =
    ev x y m.conjugator * target x y m.kind * (ev x y m.conjugator)⁻¹ := by
  have e := sound x y _ _ (certificate k)
  simpa only [ev_append,ev_rev,ev_encode,target_eq] using e

theorem t_close_if (x y : G) (H : Commute (Z x y) (U x y)) :
    Ribbon5Law.trace x y false lt = 1 := by
  have e : reduce (encode false lt) = reduce (origW++rev lu++rev origW++lu) := by decide +kernel
  rw [← ev_encode x y lt false,sound x y _ _ e]
  simp only [ev_append,ev_rev,w_eq]
  change Z x y * (U x y)⁻¹ * (Z x y)⁻¹ * U x y=1
  rw [H.inv_right.eq,mul_inv_cancel_right,inv_mul_cancel]

end Ribbon8AltA
#print axioms Ribbon8AltA.certificate
#print axioms Ribbon8AltA.mate_sound
#print axioms Ribbon8AltA.t_close_if
