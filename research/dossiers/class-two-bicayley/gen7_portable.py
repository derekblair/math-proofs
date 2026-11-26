from pathlib import Path
from ast import literal_eval
def rw(x):return ''.join('102'[int(j)] for j in x[::-1])
def fw(w,r=0):
 a=[]
 for j in w:
  if j=='2':r^=1
  else:a.append((r+1)*(1 if j=='0' else -1))
 return tuple(a)
def red(w):
 a=[]
 for v in w:
  if a and a[-1]==-v:a.pop()
  else:a.append(v)
 return tuple(a)
def inv(w):return tuple(-z for z in w[::-1])
def expr(w):return '*'.join({1:'x',-1:'x⁻¹',2:'y',-2:'y⁻¹'}[v] for v in w) or '1'
def arr(w):return '#['+','.join(w)+']'
def chart(w):
 r=x=y=z=0; out=[(r,x,y,z)]
 for j in w:
  if j=='2':r^=1
  elif r:
   d=1 if j=='0' else -1;y+=d;z+=x*d
  else:x+=1 if j=='0' else -1
  out.append((r,x,y,z))
 return out
def ct(w):
 return '#['+','.join(f'({str(bool(r)).lower()},{x},{y},{z})' for r,x,y,z in chart(w))+']'

# Selected witness and comparison categories. The Lean kernel checks them.
line = "HIT 27 0 27 1212002121202120200212121202002112120212020211202002112120202021 12120021212021202002121212020021121202120202112020021121202020211202020211212021202021120200212121202002112120021212021202002112 Counter({'free': 24, 'h': 3}) [('free', 0, 32, (1, 0)), ('free', 0, 64, (0, 1)), ('free', 32, 64, (-1, 1)), ('free', 1, 33, (1, 0)), ('free', 1, 65, (0, 1)), ('free', 33, 65, (-1, 1)), ('free', 2, 34, (1, 0)), ('free', 2, 66, (0, 1)), ('free', 34, 66, (-1, 1)), ('free', 3, 35, (1, 0)), ('free', 4, 36, (1, 0)), ('free', 5, 37, (1, 0)), ('free', 29, 61, (-1, 1)), ('free', 30, 62, (-1, 1)), ('free', 31, 63, (-1, 1)), ('h', 48, 98, 1), ('h', 49, 99, 1), ('h', 50, 100, 1), ('free', 86, 118, (1, 0)), ('free', 87, 119, (1, 0)), ('free', 88, 120, (1, 0)), ('free', 89, 121, (1, 0)), ('free', 90, 122, (1, 0)), ('free', 91, 123, (1, 0)), ('free', 92, 124, (1, 0)), ('free', 93, 125, (1, 0)), ('free', 94, 126, (1, 0))]"
_,_,rim,rot,W,T,more=line.split(' ',6)
assert rim=='0'; rot=int(rot)
A=W[:32]; B=rw(W[32:]);assert A[18:]+A[:18]==B
assert T==W+rw(W[rot:]+W[:rot])
i7=literal_eval(more.split('}) ',1)[1])
M4=[(i,j) for d,i,j,z in i7 if d=='h']; MF=[(i,j) for d,i,j,z in i7 if d=='free']
R=fw(A); Z=fw(W); U=fw(A[:18]); V=fw(A[18:]); K=fw(W[:rot])
c='''import Ribbon6Family
namespace Ribbon7
open Ribbon5Bridge
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 32000
set_option maxHeartbeats 0
'''
for name,w in [('wa',A),('ww',W),('wt',T)]:
 c+=f'def {name} : Array P := {arr(w)}\n'
for name,w in [('ta',A),('tw',W),('tt',T)]:
 c+=f'def {name} : Array Q := {ct(w)}\n'
for a,L in [('a',32),('w',64),('t',128)]:
 c+=f'theorem {a}step : ∀ i : Fin {L}, push t{a}[i.val]! w{a}[i.val]! = t{a}[i.val+1]! := by decide +kernel\n'
for name,L,Ms in [('mw',64,[(i,j) for i,j in MF if j<64]),('mt',128,[(i,j) for _,i,j,_ in i7])]:
 c+=f'def {name} (i j : Nat) : Prop := '+' ∨ '.join(f'(i={i} ∧ j={j})' for i,j in Ms)+'\n'
 c+=f'instance (i j : Nat) : Decidable ({name} i j) := by unfold {name}; infer_instance\n'
c+='''theorem achart : ∀ i j : Fin 32, i.val < j.val → separated ta[i.val]! ta[j.val]! := by decide +kernel
theorem wchart : ∀ i j : Fin 64, i.val < j.val → separated tw[i.val]! tw[j.val]! ∨ mw i.val j.val := by decide +kernel
theorem tchart : ∀ i j : Fin 128, i.val < j.val → separated tt[i.val]! tt[j.val]! ∨ mt i.val j.val := by decide +kernel
'''
for name,g in [('U',U),('V',V),('K',K)]:
 c+=f'def {name} (x y : G) : G := {expr(g)}\n'
c+='''def R (x y : G) : G := U x y * V x y
def Z (x y : G) : G := ⁅U x y,V x y⁆
'''
for n,L,defn in [('a',32,'R x y'),('w',64,'Z x y'),('t',128,'Z x y * (K x y)⁻¹ * (Z x y)⁻¹ * K x y')]:
 c+=f'''theorem {n}_end (x y : G) : pathAt x y w{n} {L}=(false,{defn}) := by
  norm_num [pathAt,run,start,action,w{n},R,Z,K,U,V,commutatorElement_def] <;> group
'''
c+='\nend Ribbon7\n'
Path('Ribbon7Chart.lean').write_text(c)
F='''import Ribbon7Chart
namespace Ribbon7
open Ribbon5Bridge
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 32000
set_option maxHeartbeats 0
'''
for typ,i,j,rel in i7:
 if typ!='free':continue
 a,b=rel
 base=(R if a>=0 else inv(R))*abs(a)+(Z if b>=0 else inv(Z))*abs(b)
 d=red(inv(fw(T[:i]))+fw(T[:j])); p=()
 while d and d[0]==-d[-1]:p+=d[:1];d=d[1:-1]
 base=red(base);q=()
 while base and base[0]==-base[-1]:q+=base[:1];base=base[1:-1]
 con=next(red(p+inv(base[:k])+inv(q)) for k in range(len(base)) if base[k:]+base[:k]==d)
 expression={(-1,1):'(R x y)⁻¹ * Z x y',(0,1):'Z x y',(1,0):'R x y'}[rel]
 ident=f'''
theorem t_{i}_{j} (x y : G) :
    ∃ k : G, (pathAt x y wt {i}).2⁻¹*(pathAt x y wt {j}).2=k*({expression})*k⁻¹ := by
  refine ⟨{expr(con)},?_⟩
  norm_num [pathAt,run,start,action,wt,R,Z,U,V,commutatorElement_def] <;> group
'''
 F+=ident
 if j<64:
  F+=ident.replace('theorem t_','theorem w_').replace('pathAt x y wt','pathAt x y ww').replace('action,wt','action,ww')
F+='\nend Ribbon7\n'
Path('Ribbon7Mates.lean').write_text(F)
print(A,B,W,T,MF,M4)
code='''import Ribbon7Algebra
import Ribbon7Mates

namespace Ribbon7
open HaarClass4Structure HaarClass4Ports Ribbon5Bridge
variable {G : Type*} [Group G]
set_option maxRecDepth 32000
set_option maxHeartbeats 0

private theorem relative_ne {u v : Bool×G} {g : G} (N : g≠1)
    (E : ∃ c : G,u.2⁻¹*v.2=c*g*c⁻¹) : u≠v := by
  intro eq
  obtain ⟨c,h⟩ := E
  rw [eq,inv_mul_cancel] at h
  apply N
  calc
    g = c⁻¹*(c*g*c⁻¹)*c := by group
    _ = 1 := by rw [←h]; group

private theorem low_sep (x y : G)
    (good : ∀ k : Nat, 1≤k → k≤4 → (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1)
    (w : Array P) (tab : Array Q)
    (h0 : tab[0]! = (false,0,0,0))
    (step : ∀ i, i<w.size → push tab[i]! w[i]! = tab[i+1]!)
    (i j : Nat) (hi : i≤w.size) (hj : j≤w.size)
    (h : separated tab[i]! tab[j]!) :
    pathAt x y w i ≠ pathAt x y w j := by
  let f := QuotientGroup.mk' (LS G 2)
  let C := f (portC x y)
  have U' : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have V' : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute C (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C,portU,map_commutatorElement] using U'
  have cy : Commute C (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C,portV,map_commutatorElement] using V'
  have xy : f x*f y=f y*f x*C := by simpa only [C,map_mul] using congrArg f (ports_xy x y)
  let F : Bool×G → Bool × (G ⧸ LS G 2) := fun u => (u.1,f u.2)
  intro E
  have T := transported f x y w tab C cx cy xy h0 step
  have e : vert (f x) (f y) C tab[i]! = vert (f x) (f y) C tab[j]! :=
    (T i hi).symm.trans ((congrArg F E).trans (T j hj))
  exact separates_low (f x) (f y) C cx cy xy good _ _ h e

private theorem fin32 (i : Fin 32) : i.val ≤ wa.size := i.isLt.le
private theorem fin64 (i : Fin 64) : i.val ≤ ww.size := i.isLt.le
private theorem fin128 (i : Fin 128) : i.val ≤ wt.size := i.isLt.le
'''
code+='''\ndef exceptional (x y : G) : Prop :=
  pathAt x y wt 48 ≠ pathAt x y wt 98 ∧
    pathAt x y wt 49 ≠ pathAt x y wt 99 ∧
    pathAt x y wt 50 ≠ pathAt x y wt 100

theorem local_bound_if (nil : LS G 7=⊥) (x y : G)
    (good : ∀ k : Nat, 1≤k → k≤4 → (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1)
    (ex : Z x y ≠ 1 → exceptional x y) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  by_cases r : R x y=1
  · left
    apply cycle_from_at x y wa (by decide) (by rw [a_end,r]; rfl)
    intro i j l
    exact low_sep x y good wa ta (by decide +kernel) (fun n hn => astep ⟨n,hn⟩) _ _
      (fin32 i) (fin32 j) (achart i j l)
  · right
    by_cases z : Z x y=1
    · left
      apply cycle_from_at x y ww (by decide) (by rw [w_end,z]; rfl)
      intro i j l
      rcases wchart i j l with h|h
      · exact low_sep x y good ww tw (by decide +kernel) (fun n hn => wstep ⟨n,hn⟩) _ _
          (fin64 i) (fin64 j) h
      · have N : (R x y)⁻¹ * Z x y ≠ 1 := by
          rw [z,mul_one]
          exact fun h => r (inv_eq_one.mp h)
        rcases h with '''
ww=[(i,j,zz) for ll,i,j,zz in i7 if j<64]
code+=' | '.join('⟨hi,hj⟩' for i,j,z in ww)+'\n'
for i,j,z in ww:
 code+=f'        · rw [hi,hj]\n          exact relative_ne {"N" if z==(-1,1) else "r"} (w_{i}_{j} x y)\n'
code+='''    · right
      apply cycle_from_at x y wt (by decide) (close128 nil x y)
      intro i j l
      rcases tchart i j l with h|h
      · exact low_sep x y good wt tt (by decide +kernel) (fun n hn => tstep ⟨n,hn⟩) _ _
          (fin128 i) (fin128 j) h
      · have M := nz_mix nil x y z
        rcases h with '''
code+=' | '.join('⟨hi,hj⟩' for e in i7)+'\n'
for kind,i,j,rel in i7:
 code+='        · rw [hi,hj]\n'
 if kind=='free':
  k={(-1,1):'M',(1,0):'r',(0,1):'z'}[rel]
  code+=f'          exact relative_ne {k} (t_{i}_{j} x y)\n'
 else:
  path={48:'.1',49:'.2.1',50:'.2.2'}[i]
  code+=f'          exact (ex z){path}\n'
code+='\nend Ribbon7\n#print axioms Ribbon7.local_bound_if\n'
Path('Ribbon7Local.lean').write_text(code)
