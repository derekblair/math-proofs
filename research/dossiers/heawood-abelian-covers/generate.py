"""Rebuild and verify the relayed exact Heawood certificate in the repo gauge."""
from pathlib import Path
from itertools import product
from collections import deque
rows = '''
081b4c2a
2a3d674c
3a081b4c2a3d674b 1 2
076d5c2a
196d5c4b
2c4b196d5c2a0769 4 5
076d3b18
074c2918
074b192a
192c5d3b
074b3d58
1b47085d3b192c58 10 11
074b192a 9
0a291b470a296d58 9
085d692a
196d580a291b4708 9 15
074c5d3a
2a3d5c470a291b4c 9 17
2c5d691b4c2a0819 1 5
08196d3a
296d3a08192c470a 8 20
4c5d670a2c4b1807 1 4
192c4708192c5d3b 8
476d3b18074c291b 8 7
08192c476d3b18074b3d5c291b4c5d67 3 6 4 7 8 9 12 10 1
08192a085d691b470a296d580a291b47 13 14 9 15 16
08192c5d3a074c2a3d69180a296d5c47 18 19 5 17 8 1 21 20 9
08192a076d5c291b3d6708192c5d3b47 25 12 4 10 7 22
08192a076d5c291b470a2c5d67081b47 25 22 27 4 9 32
08192c4b3d674c2918074b192c5d3b47 10 12 23 8 24 27
08192a074b18074b180a291b47081b47 25 9 26 27 29 28
'''.strip().splitlines()
rows=[(r.split()[0],list(map(int,r.split()[1:]))) for r in rows]
rows[12]=(rows[12][0]*2,rows[12][1])
new=[(2,10),(3,11),(4,12),(4,7),(5,13),(5,8),(6,7),(6,9)]
old=[(2,10),(3,11),(4,11),(4,12),(5,12),(5,13),(6,9),(6,13)]
edge=[(u,7+(u+d)%7) for u in range(7) for d in (0,1,3)]
tree={u:[] for u in range(14)}
for u,v in edge:
    if (u,v) not in new:tree[u].append(v);tree[v].append(u)
def between(u,v):
    q=deque([[u]])
    while q:
        p=q.popleft()
        if p[-1]==v:return p
        for t in tree[p[-1]]:
            if t not in p:q.append(p+[t])
    raise ValueError(u,v)
zero=(0,)*8
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def mul(i,x):return tuple(i*a for a in x)
def step(u,v):
    e=tuple(sorted((u,v)))
    assert e in edge
    return tuple((1 if u<7 else -1) if d==e else 0 for d in old)
def total(w):
    z=zero
    for u,v in zip(w,w[1:]+w[:1]):z=add(z,step(u,v))
    return z
xs = [total([u,*between(v,u)[:-1]]) for u,v in new]
def transform(vec):
    v=zero
    for i,w in zip(vec,xs):v=add(v,mul(i,w))
    return v
H={25:(1,0,0,0,0,0,0,0),26:(1,0,0,-2,0,0,0,0),
   27:(0,0,0,1,0,0,0,0),28:(1,0,0,1,0,0,0,0),29:(0,0,0,2,0,0,0,0),32:(0,0,0,1,-1,0,-1,0)}
H={i:transform(v) for i,v in H.items()}

def calc(seed):
    w=list(int(a,16) for a in seed)
    ports=[];z=zero;seen={};dif=set()
    for u,v in zip(w,w[1:]+w[:1]):
        for old_z in seen.setdefault(u,[]):
            d=add(z,mul(-1,old_z));dif.add(min(d,mul(-1,d)))
        seen[u].append(z)
        ports.append((0,1,3).index(((v-u) if u<7 else (u-v))%7))
        z=add(z,step(u,v))
    # The relayed table uses different roots. Translate the base by -root
    # for Lean rows (which start at 0), defining each row's own shifted gauge.
    return z,sorted(dif),ports,w[0]
# Start by retaining original vertex roots: no change to gauge or voltages.
C={i:calc(w) for i,(w,ds) in enumerate(rows,1)}
expect={i:C[i][0] for i in range(1,25)}|H
def zeds(zs):
    for coeff in product(range(-5,6),repeat=len(zs)):
        s=zero
        for k,x in zip(coeff,zs):s=add(s,mul(k,x))
        yield coeff,s
def params(i):
    return [i] if 25<=i<=29 else ([29,32] if i==30 else [])
co={};ms={}
for i,(_,ds) in enumerate(rows,1):
    z, repeats, ports, root=C[i]
    Z={s:a for a,s in zeds([H[j] for j in params(i)])}
    if i>=25:
        assert z in Z,(i,z,Z)
        co[i]=list(Z[z])
    matches=[]
    for d in repeats:
        options=[(j,s,list(Z[t])) for j in ds for s in (1,-1)
           if (t:=add(d,mul(-s,expect[j]))) in Z]
        assert options,(i,d,ds)
        matches.append(options[0])
    ms[i]=matches
print('All 31 rows verified in repo gauge; repeat vectors',sum(len(c[1]) for c in C.values()))
def vec(v):
    return '!['+','.join(str(a) for a in v)+']'
groups=[range(k,min(k+5,32)) for k in range(1,32,5)]
for j,g in enumerate(groups):
    s='import HeawoodCertCore\nnamespace HeawoodCert\nopen HaarOrbitC7Voltage\nset_option maxRecDepth 20000\nset_option maxHeartbeats 0\n'
    for i in g:
        z,ds,ports,root=C[i]
        rep='['+','.join(vec(x) for x in ds)+']'
        s+=f'def row{i} : Data := ⟨{root}, {ports}, {vec(z)}, {rep}⟩\n'
        s+=f'theorem check{i} : check row{i} := by decide +kernel\n'
    s+='end HeawoodCert\n'
    Path(f'HeawoodRows{j}.lean').write_text(s)

# Lean checks the flow, closure, and every equal-base pair at each case.
s='\n'.join(f'import HeawoodRows{j}' for j in range(len(groups)))+'''
namespace HeawoodCert
open HaarOrbitC7Voltage
open HaarOrbitC7DAG (Vanish)
variable {A : Type*} [AddCommGroup A]
set_option maxRecDepth 20000
set_option maxHeartbeats 0
'''
for j,vec0 in H.items():s+=f'def h{j} : V := {vec(vec0)}\n'

def vref(j):return f'row{j}.closing' if j<=24 else f'h{j}'
def known(j):return f'hn{j}' if j!=32 else 'hm'
def nzproof(i,depth=2):
    ind=' '*depth
    o=f'{ind}have sep{i} : ∀ v ∈ row{i}.repeats, φ v ≠ 0 := by\n'
    o+=f'{ind}  intro v hv\n'
    o+=f'{ind}  simp only [row{i},List.mem_cons,List.not_mem_nil,or_false] at hv\n'
    if ms[i]:
        if len(ms[i])>1:o+=f'{ind}  rcases hv with '+('|'.join('rfl' for _ in ms[i]))+'\n'
        else:o+=f'{ind}  subst v\n'
        for (j,sgn,coef),actual in zip(ms[i],C[i][1]):
            bullet='· ' if len(ms[i])>1 else ''
            o+=f'{ind}  {bullet}exact via_deps φ L Z _ {vref(j)} ({sgn}:ℤ) (by decide) ({coef}) (by decide +kernel) {known(j)}\n'
    else:pass
    return o

s+='''
theorem obstruction (φ : V →+ A) (F : NoCycles φ) : False := by
  let L : List V := []
  have Z : Vanish φ L := vanish_nil φ
'''
for i in range(1,25):
    s+=nzproof(i)
    s+=f'  have hn{i} : φ row{i}.closing≠0 := force φ F row{i} check{i} sep{i}\n'
for i in range(25,29):
    s+=f'  have hn{i} : φ h{i}≠0 := by\n    intro zero\n    let L := [h{i}]\n    have Z : Vanish φ L := vanish_one φ h{i} zero\n'
    s+=nzproof(i,4)
    s+=f'    exact force φ F row{i} check{i} sep{i} (via_zero φ L Z _ {co[i]} (by decide +kernel))\n'
s+='''  have hn29 : φ h29≠0 := by
    intro zero
    by_cases hm : φ h32≠0
    · let L := [h29]
      have Z : Vanish φ L := vanish_one φ h29 zero
'''
s+=nzproof(29,6)
s+=f'      exact force φ F row29 check29 sep29 (via_zero φ L Z _ {co[29]} (by decide +kernel))\n'
s+='''    · let L := [h29,h32]
      have Z : Vanish φ L := vanish_two φ h29 h32 zero (not_not.mp hm)
'''
s+=nzproof(30,6)
s+=f'      exact force φ F row30 check30 sep30 (via_zero φ L Z _ {co[30]} (by decide +kernel))\n'
s+=nzproof(31)
s+=f'  exact force φ F row31 check31 sep31 (via_zero φ L Z _ {co[31]} (by decide +kernel))\n'
s+='''
theorem any_voltage (φ : V →+ A) : ∃ n, n ∈ [8,16,32] ∧ HasCycle φ n := by
  classical
  by_contra! h
  exact obstruction φ h

theorem every_regular_abelian_voltage (W : B → B → A) (anti : ∀ u v, W v u = -W u v) :
    ∃ n, n ∈ [8,16,32] ∧ HaarOrbitC7RealCover.HasCycle W n := by
  obtain ⟨n,hn,cv⟩ := any_voltage (HaarOrbitC7Gauge.map W)
  refine ⟨n,hn,HaarOrbitC7RealCover.real (by simp at hn; omega) W ?_⟩
  exact HaarOrbitC7Gauge.ungauge W anti cv

end HeawoodCert
#print axioms HeawoodCert.every_regular_abelian_voltage
'''
# Lean vectors accept numerals; subtraction-generated coefficient lists may be negative.
Path('HeawoodAbelian.lean').write_text(s)
