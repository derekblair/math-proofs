import HaarClass3Odd

namespace HaarClass4Table

structure Row where
  i : ℤ
  j : ℤ
  c : ℤ
  u : ℤ
  v : ℤ
  a : ℤ
  b : ℤ
  d : ℤ
  deriving DecidableEq, Inhabited

def diff (p q : Row) : Row :=
  ⟨q.i-p.i,q.j-p.j,q.c-p.c,q.u-p.u,q.v-p.v,q.a-p.a,q.b-p.b,q.d-p.d⟩

def tri (i : ℤ) := i*(i-1)/2
def tet (i : ℤ) := (i+1)*i*(i-1)/6

def rightX (p : Row) : Row :=
  ⟨p.i+1,p.j,p.c,p.u+p.c,p.v,p.a+p.u+p.c,p.b+p.v,p.d⟩

def rightY (p : Row) : Row :=
  ⟨p.i,p.j+1,p.c+p.i,p.u+tri p.i,p.v+p.c,p.a+tet p.i,p.b+p.u,p.d+p.v+p.c⟩

def reaches (p q : Row) : Prop := q=p ∨ q=rightX p ∨ q=rightY p
instance (p q : Row) : Decidable (reaches p q) := by unfold reaches; infer_instance

def ordinary : Nat → Row := fun i => (#[⟨0,0,0,0,0,0,0,0⟩, ⟨0,0,0,0,0,0,0,0⟩, ⟨0,-1,0,0,0,0,0,0⟩,
  ⟨0,-1,0,0,0,0,0,0⟩, ⟨-1,-1,0,0,0,0,0,0⟩, ⟨-1,0,-1,1,0,0,0,0⟩,
  ⟨-1,0,-1,1,0,0,0,0⟩, ⟨-1,1,-2,2,-1,0,1,-1⟩, ⟨-1,1,-2,2,-1,0,1,-1⟩,
  ⟨0,1,-2,0,-1,0,0,-1⟩, ⟨0,0,-2,0,1,0,0,0⟩, ⟨1,0,-2,-2,1,-2,1,0⟩,
  ⟨1,-1,-3,-2,4,-2,3,-1⟩, ⟨1,-1,-3,-2,4,-2,3,-1⟩, ⟨0,-1,-3,1,4,0,-1,-1⟩,
  ⟨0,0,-3,1,1,0,0,0⟩, ⟨-1,0,-3,4,1,-1,-1,0⟩, ⟨-1,0,-3,4,1,-1,-1,0⟩,
  ⟨-1,-1,-2,3,3,-1,-4,-1⟩, ⟨0,-1,-2,1,3,0,-1,-1⟩, ⟨0,-1,-2,1,3,0,-1,-1⟩,
  ⟨0,0,-2,1,1,0,0,0⟩, ⟨0,0,-2,1,1,0,0,0⟩, ⟨0,1,-2,1,-1,0,1,-1⟩,
  ⟨-1,1,-2,3,-1,-1,2,-1⟩, ⟨-1,1,-2,3,-1,-1,2,-1⟩, ⟨-1,0,-1,2,0,-1,0,0⟩,
  ⟨0,0,-1,1,0,0,0,0⟩, ⟨0,-1,-1,1,1,0,-1,0⟩, ⟨1,-1,-1,0,1,0,0,0⟩,
  ⟨1,-1,-1,0,1,0,0,0⟩, ⟨1,0,0,0,0,0,0,0⟩, ⟨0,0,0,0,0,0,0,0⟩] : Array Row)[i]!
def conditional : Nat → Row := fun i => (#[⟨0,0,0,0,0,0,0,0⟩, ⟨0,0,0,0,0,0,0,0⟩, ⟨-1,0,0,0,0,0,0,0⟩,
  ⟨-1,1,-1,1,0,0,0,0⟩, ⟨-2,1,-1,2,0,-1,0,0⟩, ⟨-2,1,-1,2,0,-1,0,0⟩,
  ⟨-2,0,1,-1,-1,0,1,0⟩, ⟨-1,0,1,0,-1,0,0,0⟩, ⟨-1,0,1,0,-1,0,0,0⟩,
  ⟨0,0,1,1,-1,1,-1,0⟩, ⟨0,0,1,1,-1,1,-1,0⟩, ⟨0,1,1,1,0,1,0,0⟩,
  ⟨-1,1,1,0,0,0,0,0⟩, ⟨-1,1,1,0,0,0,0,0⟩, ⟨-2,1,1,-1,0,0,0,0⟩,
  ⟨-2,1,1,-1,0,0,0,0⟩, ⟨-2,0,3,-4,-3,1,4,0⟩, ⟨-2,0,3,-4,-3,1,4,0⟩,
  ⟨-2,-1,5,-7,-8,2,11,3⟩, ⟨-1,-1,5,-2,-8,0,3,3⟩, ⟨-1,-1,5,-2,-8,0,3,3⟩,
  ⟨0,-1,5,3,-8,3,-5,3⟩, ⟨0,-1,5,3,-8,3,-5,3⟩, ⟨0,0,5,3,-3,3,-2,0⟩,
  ⟨-1,0,5,-2,-3,0,1,0⟩, ⟨-1,0,5,-2,-3,0,1,0⟩, ⟨-2,0,5,-7,-3,2,4,0⟩,
  ⟨-2,1,3,-4,2,1,-3,2⟩, ⟨-2,1,3,-4,2,1,-3,2⟩, ⟨-1,1,3,-1,2,0,-1,2⟩,
  ⟨-1,1,3,-1,2,0,-1,2⟩, ⟨0,1,3,2,2,2,1,2⟩, ⟨0,0,3,2,-1,2,-1,0⟩] : Array Row)[i]!

def base : Row := ⟨0,0,0,0,0,0,0,0⟩
def unstable : Row := ⟨0,0,-3,1,1,0,0,0⟩
def unstable' : Row := ⟨0,0,-3,1,4,0,-1,-1⟩
def rebound : Row := ⟨0,0,3,2,-1,2,-1,0⟩

theorem ends :
    ordinary 0 = base ∧ ordinary 32 = base ∧ conditional 0 = base ∧ conditional 32 = rebound := by
  decide

def stepCondition (T : Nat → Row) (i : Fin 32) : Prop :=
  if HaarCycle.side i then reaches (T (i.val+1)) (T i.val)
  else reaches (T i.val) (T (i.val+1))
instance (T : Nat → Row) (i : Fin 32) : Decidable (stepCondition T i) := by
  unfold stepCondition
  infer_instance

set_option maxRecDepth 10000 in
theorem edges : (∀ i : Fin 32, stepCondition ordinary i) ∧
    (∀ i : Fin 32, stepCondition conditional i) := by decide

def small (i : ℤ) : Prop := |i|=1 ∨ |i|=2 ∨ |i|=4
instance (i : ℤ) : Decidable (small i) := by unfold small; infer_instance

def ordinarySeparation (r : Row) : Prop :=
  small r.i ∨ small r.j ∨
  (r.i=0 ∧ r.j=0 ∧ small r.c) ∨
  (r.i=0 ∧ r.j=0 ∧ r.c=0 ∧ r.u=1 ∧ r.v=0) ∨ r=unstable ∨ r=unstable'

instance (r : Row) : Decidable (ordinarySeparation r) := by unfold ordinarySeparation; infer_instance

def conditionalSeparation (r : Row) : Prop :=
  r.i%3 ≠ 0 ∨ r.j%3 ≠ 0 ∨ (r.i=0 ∧ r.j=0 ∧ r.c%3≠0)

instance (r : Row) : Decidable (conditionalSeparation r) := by unfold conditionalSeparation; infer_instance

set_option maxRecDepth 15000 in
set_option maxHeartbeats 4000000 in
theorem separateOrd (i j : Fin 32) :
    j.val ≤ i.val ∨ HaarCycle.side i ≠ HaarCycle.side j ∨
      ordinarySeparation (diff (ordinary i.val) (ordinary j.val)) := by
  revert i j
  decide

set_option maxRecDepth 15000 in
set_option maxHeartbeats 4000000 in
theorem separateCond (i j : Fin 32) :
    j.val ≤ i.val ∨ HaarCycle.side i ≠ HaarCycle.side j ∨
      conditionalSeparation (diff (conditional i.val) (conditional j.val)) := by
  revert i j
  decide

end HaarClass4Table

#print axioms HaarClass4Table.edges
#print axioms HaarClass4Table.separateOrd
#print axioms HaarClass4Table.separateCond
