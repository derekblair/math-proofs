#!/usr/bin/env python3
from pathlib import Path
from simple import *
from sys import argv
tag = argv[1] if len(argv)>1 else ''
if tag:
 from variants import WORDS,info
 import simple as S
 A,U,V,W,T,t,args,e=info(WORDS['ABC'.index(tag)])
 G=fw(A); Z=fw(W)
 S.G=G; S.Z=Z
 S.vals={(a,b):(G if a>0 else inv(G))*abs(a)+(Z if b>0 else inv(Z))*abs(b)
   for a,b in ((1,0),(-1,0),(0,1),(0,-1),(-1,1),(1,-1))}

def a(w):return '#['+','.join(map(str,w))+']'
def l(w):return '['+','.join(map(str,w))+']'
def c(w):return a(f'({str(bool(s)).lower()},{x},{y},{z})' for s,x,y,z in chart(w))
sign={1:0,-1:1,2:2,-2:3}
kind=[(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)]
mates=data(T)[2];assert len(mates)==60 and all(k in kind for _,_,k,_ in mates)
s='''import Ribbon8Free
import Ribbon7Algebra

namespace Ribbon8
open Ribbon5Bridge Ribbon8Free
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 32000
set_option maxHeartbeats 0

'''
for n,w in [('a',A),('w',W),('t',T)]:
 s+=f'def l{n} : List P := {l(w)}\ndef w{n} : Array P := l{n}.toArray\ndef t{n} : Array Q := {c(w)}\n'
s+=f'''
def lu : List Ltr := {l(sign[p] for p in fw(U))}
def lv : List Ltr := {l(sign[p] for p in fw(V))}
def origA : List Ltr := {l(sign[p] for p in G)}
def origW : List Ltr := {l(sign[p] for p in Z)}

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
'''.replace('def U (x y : G)','def U (x y : G)')
s+=',\n'.join(f'  ⟨{i},{j},{kind.index(k)},{l(sign[x] for x in p)}⟩' for i,j,k,p in mates)+']\n'
s+='''
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

end Ribbon8
#print axioms Ribbon8.certificate
#print axioms Ribbon8.mate_sound
#print axioms Ribbon8.t_close_if
'''
if tag:
 ns='Ribbon8Alt'+tag
 s=s.replace('namespace Ribbon8\n','namespace '+ns+'\n').replace('end Ribbon8\n','end '+ns+'\n').replace('#print axioms Ribbon8.','#print axioms '+ns+'.')
 Path(ns+'Chart.lean').write_text(s)
 base=Path('Ribbon8Algebra.lean').read_text()
 base=base.replace('import Ribbon8Chart','import '+ns+'Chart').replace('namespace Ribbon8\n','namespace '+ns+'\n').replace('end Ribbon8\n','end '+ns+'\n').replace('#print axioms Ribbon8.','#print axioms '+ns+'.')
 fmt={1:'x',2:'y',-1:'x⁻¹',-2:'y⁻¹'}
 k='*'.join(fmt[p] for p in t)
 from re import sub
 base=sub(r'private def twist \(x y : G\) := [^\n]+','private def twist (x y : G) := '+k,base)
 r=f'(Ribbon6.residue {fmt[args[0]]} {fmt[args[1]]})'
 if e<0:r+='⁻¹'
 base=base.replace('Ribbon6.residue x y⁻¹',r,1)
 # The selected reference residue is itself in the normal layer,
 # and the inverse case follows by closure under inverses.
 old='  exact (inferInstance : (L G 4).Normal).conj_mem _ (Ribbon6.residue_layer x y⁻¹) _'
 proof=f'(Ribbon6.residue_layer {fmt[args[0]]} {fmt[args[1]]})'
 if e<0:proof=f'((L G 4).inv_mem {proof})'
 base=base.replace(old,'  exact (inferInstance : (L G 4).Normal).conj_mem _ '+proof+' _')
 base=base.replace('  norm_num [U,lu,ev,letter,map_mul,map_inv]',"""  simp only [U,lu,ev,letter,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,map_mul,map_inv,mul_one]
  let X := Abelianization.of x
  let Y := Abelianization.of y
  calc
    _ = (X*X*X*X⁻¹*X⁻¹*X⁻¹)*(Y*Y*Y*Y⁻¹*Y⁻¹*Y⁻¹) := by dsimp [X,Y]; ac_rfl
    _ = 1 := by group""")

 Path(ns+'Algebra.lean').write_text(base)
else:
 Path('Ribbon8Chart.lean').write_text(s)

