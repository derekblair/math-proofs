#!/usr/bin/env python3
from pathlib import Path
rows=[r.split() for r in Path('owner5.txt').read_text().splitlines()]
src='''import RibbonClass4SharpGraph

namespace RibbonClass4SharpGraph

def key (s : V) : Nat :=
  let l := if s.1 then 1 else 0
  (((((((((l*11+s.2.x.val)*11+s.2.y.val)*11+s.2.z.val)*11+s.2.t.val)*11+s.2.u.val)*11+s.2.v.val)*11+s.2.w.val)*11+s.2.r.val)*11+s.2.s.val)*11+s.2.f.val

def owner (m mask0 mask1 : Nat) (u : V) : P :=
  let i := key u % m
  if mask0.testBit i then 0 else if mask1.testBit i then 1 else 2

def checkOwner (h : Nat) (s : Bool) (m mask0 mask1 : Nat) (q : P) : Bool :=
  (ends (h-1) (step (s,1) q) q).all fun u => decide (owner m mask0 mask1 u=q)

theorem sound_check_owner (h : Nat) (s : Bool) (m mask0 mask1 : Nat)
    (cert : ∀ q : P, checkOwner h s m mask0 mask1 q = true) (q r : P) (hqr : q≠r) :
    List.Disjoint (ends (h-1) (step (s,1) q) q) (ends (h-1) (step (s,1) r) r) := by
  intro v Hq Hr
  have E := List.all_eq_true.mp (cert q) v Hq
  have F := List.all_eq_true.mp (cert r) v Hr
  exact hqr ((of_decide_eq_true E).symm.trans (of_decide_eq_true F))

set_option maxRecDepth 30000
set_option maxHeartbeats 0
'''
for h,s,m,b0,b1 in rows:
 t=('false','true')[int(s)]
 src+=f'''private def maskA{h}_{s} : Nat := {b0}
private def maskB{h}_{s} : Nat := {b1}
private theorem cert{h}_{s} : ∀ q : P, checkOwner {h} {t} {m} maskA{h}_{s} maskB{h}_{s} q = true :=
  by decide +kernel

'''
for h in ('2','4','8'):
 src+=f'''theorem checked{h} : Checked {h} := by
  intro s q r H
  cases s
  · exact sound_check_owner {h} false _ _ _ cert{h}_0 q r H
  · exact sound_check_owner {h} true _ _ _ cert{h}_1 q r H

'''
src+='end RibbonClass4SharpGraph\n#print axioms RibbonClass4SharpGraph.checked8\n'
Path('RibbonClass4SharpCert.lean').write_text(src)
