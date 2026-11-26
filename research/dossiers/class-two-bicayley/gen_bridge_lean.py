from pathlib import Path
W='12002021212120200212120212'; T='020021'
def inverse(x):return x[::-1].translate(str.maketrans('01','10'))
full=W+T+inverse(W)+inverse(T)
short='12002002121121200200211212002121'
def data(w):
 s,i,j,k=0,0,0,0; tab=[(False,0,0,0)]
 for p in w:
  if p=='2':s=1-s
  elif s:
   e=1 if p=='0' else -1
   j+=e;k+=e*i
  else:i+=1 if p=='0' else -1
  tab.append((bool(s),i,j,k))
 return tab
head='''import HaarCycle
import Ribbon

namespace Ribbon5Bridge
abbrev P := Fin 3
abbrev Q := Bool × HaarCycle.Coord

def push (s : Q) (p : P) : Q :=
  if p=2 then (!s.1,s.2)
  else if s.1 then
    if p=0 then (s.1,HaarCycle.rightY s.2)
    else (s.1,s.2.1,s.2.2.1-1,s.2.2.2-s.2.1)
  else if p=0 then (s.1,HaarCycle.rightX s.2)
    else (s.1,s.2.1-1,s.2.2.1,s.2.2.2)

def gap (d : ℤ) : Prop :=
  d=1 ∨ d= -1 ∨ d=2 ∨ d= -2 ∨ d=3 ∨ d= -3 ∨ d=4 ∨ d= -4
instance (d : ℤ) : Decidable (gap d) := by unfold gap; infer_instance

def separated (u v : Q) : Prop :=
  u.1 ≠ v.1 ∨ gap (u.2.1-v.2.1) ∨ gap (u.2.2.1-v.2.2.1) ∨
    (u.2.1=v.2.1 ∧ u.2.2.1=v.2.2.1 ∧ gap (u.2.2.2-v.2.2.2))
instance (u v : Q) : Decidable (separated u v) := by unfold separated; infer_instance

/-- The 7 ends/points of the two copies of the connecting bridge.
Indices from the pair are ordered increasingly; at the first bridge end
the mate is the original vertex 0, not the closing endpoint 64. -/
def mate (i j : Nat) : Prop :=
  (i = 0 ∧ j = 26) ∨ (27 ≤ i ∧ i ≤ 32 ∧ i + j = 90)
instance (i j : Nat) : Decidable (mate i j) := by unfold mate; infer_instance

set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
'''
s=[head]
for n,ww in [(32,short),(64,full)]:
 q=data(ww)
 vals=', '.join(f'({str(v).lower()}, {i}, {j}, {k})' for v,i,j,k in q)
 s.append(f'def tab{n} : Array Q := #[{vals}]')
 s.append(f'def word{n} : Array P := #[{",".join(ww)}]')
 s.append(f'theorem step{n} : ∀ i : Fin {n}, push tab{n}[i.val]! word{n}[i.val]! = tab{n}[i.val+1]! := by decide +kernel')
 s.append(f'theorem closed{n} : tab{n}[{n}]! = tab{n}[0]! := by decide +kernel')
 mate_clause=' ∨ mate i.val j.val' if n==64 else ''
 s.append(f'theorem chart{n} : ∀ i j : Fin {n}, i.val<j.val → separated tab{n}[i.val]! tab{n}[j.val]!{mate_clause} := by decide +kernel')
s.append('end Ribbon5Bridge\n#print axioms Ribbon5Bridge.chart32\n#print axioms Ribbon5Bridge.chart64\n')
Path('Ribbon5BridgeChart.lean').write_text('\n\n'.join(s))
