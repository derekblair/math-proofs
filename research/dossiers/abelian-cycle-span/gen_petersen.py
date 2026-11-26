from span_search import step_graph,compute
from itertools import product
from sympy import Matrix,linsolve
import json
_,W,_=json.load(open('petersen.json'))
N,A=step_graph(5,2)
E=[(u,v) for u in range(N) for v in sorted(A[u]) if u<v]
D,c=compute(N,A,E,W)
def rawprefix(W):
 z=[0]*len(E)
 result=[]
 for i,u in enumerate(W):
  result.append(tuple(z))
  v=W[(i+1)%len(W)]
  j=E.index(tuple(sorted((u,v))))
  z[j]+=1 if u<v else -1
 result.append(tuple(z))
 return result
P=[rawprefix(w) for w in W]
S=list(D)
stats=[]
def coeff(v,C):
    if not any(v):
        return [0]*len(C)
    if not C:return None
    T=Matrix(C).T
    V=Matrix(v)
    s=linsolve((T,V))
    if not s:return None
    a=next(iter(s)); vars=sorted(set().union(*[x.free_symbols for x in a]),key=str)
    for p in product((0,1,-1,2,-2,3,-3),repeat=len(vars)):
        aa=[x.subs(dict(zip(vars,p))) for x in a]
        if all(a.is_integer for a in aa):
            res=list(map(int,aa));assert T*Matrix(res)==V
            return res
    return None
def vstr(v):return '(!['+','.join(f'({t})' for t in v)+'])'
def tpls(a):return '['+','.join(str(x) for x in a)+']'
def proof(C,depth):
    pad='  '*depth
    for j,(v,F) in enumerate(S):
        if any(coeff(c,C) is not None for c in F):continue
        cs=coeff(v,C)
        if cs is None:continue
        i=stats.__len__();stats.append([j,C,cs])
        print(pad+f'have e{i} : E (closing {j}) = 0 := by')
        print(pad+f'  have EV : combine {tpls(cs)} ['+','.join(vstr(c) for c in C)+f'] = closing {j} := by decide +revert')
        print(pad+f'  rw [←EV]')
        if not C: print(pad+'  simp [combine]')
        else:
            print(pad+'  exact eval_combine E _ _ (by simp ['+','.join('c'+str(k) for k in range(len(C)))+'])')
        print(pad+f'obtain ⟨z{i},h{i},a{i}⟩ := H {j} e{i}')
        if not F:
            print(pad+f'simp [clashes] at h{i}')
        else:
            print(pad+f'change z{i} ∈ ['+','.join(vstr(c) for c in F)+f'] at h{i}')
            print(pad+f'simp only [List.mem_cons,List.not_mem_nil,or_false] at h{i}')
            print(pad+f'rcases h{i} with '+ ' | '.join(['rfl']*len(F)))
            for c in F:
                print(pad+f'· have c{len(C)} := a{i}')
                proof(C+[c],depth+1)
        return
    raise RuntimeError(('incomplete branch',C))
def md(W):
 return '['+','.join('['+','.join(map(str,w))+']' for w in W)+']'
if __name__=='__main__':
 import sys
 sys.stdout=open('PetersenDecision.lean','w')
 print('''import Mathlib.Tactic

namespace PetersenDecision
abbrev V := Fin 15 → ℤ

def combine : List ℤ → List V → V
  | c::cs, v::vs => c • v+combine cs vs
  | _,_=> 0

theorem eval_combine {A : Type*} [AddCommGroup A] (E : V →+ A) (c : List ℤ) (v : List V)
    (h : ∀ x∈v,E x=0) : E (combine c v)=0 := by
  induction c generalizing v with
  | nil => simp [combine]
  | cons q c ih =>
    cases v with
    | nil => simp [combine]
    | cons x v =>
      simp only [combine,map_add,map_zsmul,h x (by simp),zsmul_zero,zero_add]
      exact ih v (fun a ha => h a (by simp [ha]))
''')
 print(f'def closing : Fin {len(S)} → V := !['+','.join(vstr(v) for v,F in S)+']')
 print(f'def clashes : Fin {len(S)} → List V := !['+','.join('['+','.join(map(vstr,F))+']' for v,F in S)+']')
 print(f'def word : Fin {len(S)} → List (Fin 10) := !['+','.join('['+','.join(map(str,D[v,F]))+']' for v,F in S)+']')
 print(f'def edges : Fin 15 → Fin 10 × Fin 10 := !['+','.join(str(e) for e in E)+']')
 print('set_option maxHeartbeats 0 in\nset_option maxRecDepth 20000 in')
 print(f'theorem chart_no_bad {{A : Type*}} [AddCommGroup A] (E : V →+ A)\n    (H : ∀ i : Fin {len(S)}, E (closing i)=0 → ∃ x∈clashes i,E x=0) : False := by')
 proof([],1)
 print(f'end PetersenDecision\n#print axioms PetersenDecision.chart_no_bad')
 sys.stdout.close()
 json.dump(stats,open('petersen-trace.json','w'))
