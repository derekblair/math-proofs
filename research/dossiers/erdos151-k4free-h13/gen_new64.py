"""Emit numeric input and untrusted exact adaptive/matching proof plan."""
import json
from pathlib import Path
data=json.loads(Path('New64Input.json').read_text())
assert data['n']==64
A=[0]*64
for x,y in data['edges']:
    assert 0<=x<y<64 and not (A[x]>>y&1)
    A[x]|=1<<y; A[y]|=1<<x
assert len(data['edges'])==414
U=(1<<64)-1
def write(mod,imp,text):
    Path(mod+'.lean').write_text(f'import {imp}\nnamespace Erdos151Ramsey.New64\nset_option maxRecDepth 8192\nset_option maxHeartbeats 0\n{text}\nend Erdos151Ramsey.New64\n')
write('New64Input','RamseySearch',
      'def masks : Array Nat := #['+', '.join(map(str,A))+']\n'+
      'def alphaWitness : Finset (Fin 64) := {'+', '.join(map(str,data['alpha13']))+'}')
def bits(P):
    while P:
        q=P&-P;P-=q;yield q.bit_length()-1
def matching(P):
    Q=P; es=[]
    while Q:
        v=min((i for i in bits(Q) if A[i]&Q),key=lambda i:(A[i]&Q).bit_count(),default=None)
        if v is None:break
        u=min(bits(A[v]&Q),key=lambda i:(A[i]&Q).bit_count())
        Q^=(1<<u)|(1<<v);es.append((u,v))
    return es
def scan(P,k):
    assert k>0
    es=matching(P)
    if P.bit_count()-len(es)<k:
        return (1+len(es),P,k,es)
    x=max(bits(P),key=lambda i:((A[i]&P).bit_count(),i))
    Q=P^(1<<x)
    l=scan(Q&~A[x],k-1);r=scan(Q,k)
    return (1+l[0]+r[0],P,k,x,l,r)
root=U&~((1<<63)|A[63]); tree=scan(root,13)
print('plan node+matching edge count',tree[0],'root',root)
def term(T):
    if len(T)==4:
        return '(.leaf ['+', '.join(f'({u}, {v})' for u,v in T[3])+'])'
    return f'(.step {T[3]} {term(T[4])} {term(T[5])})'
nodes=[];leaves=[];top=[]
def visit(T):
    j=len(nodes);nodes.append(T)
    if T[0]<=550:
        leaves.append((j,T))
    else:
        a=visit(T[4]);b=visit(T[5])
        top.append((j,T,a,b))
    return j
visit(tree)
names=[]
while leaves:
    out=[]
    count=0
    while leaves and (not out or count+leaves[0][1][0]<=1450):
        j,T=leaves.pop(0)
        sz,P,k,*_=T
        out.append(f'def p{j} : Plan := {term(T)}\ntheorem c{j} : check p{j} {P} {k} = true := by decide +kernel')
        count+=sz
    name=f'New64Cert{len(names)}'; names.append(name)
    write(name,'New64Mask','\n'.join(out))
lines=[f'def p{j} : Plan := .step {T[3]} p{a} p{b}\n'+
       f'theorem c{j} : check p{j} {T[1]} {T[2]} = true := check_combine (v := {T[3]}) (l := p{a}) (r := p{b}) (m := {T[1]}) (k := {T[2]}) (by decide +kernel) c{a} c{b}'
       for j,T,a,b in top]
lines += [f'theorem root_mask : checkRoot = {root} := by decide +kernel',
          'theorem checked_root : check p0 checkRoot 13 = true := by rw [root_mask]; exact c0']
write('New64Numeric','\nimport '.join(names),'\n'.join(lines))
Path('order64-generated-modules.txt').write_text('\n'.join(['New64Input','New64Mask','New64Graph']+names+['New64Numeric','New64Endpoint'])+'\n')
