"""Generate reverse-owner payload by a displacement hash; Lean independently checks every owner."""
from pathlib import Path
import sys
from class5_ranks import make, p

PRIME, C, D, E = 18446744073709551557, 6364136223846793005, 1442695040888963407, 123456789
def place(shards):
    m=sum(map(len,shards))
    b=max(m//3,1)
    bucket=[[] for _ in range(b)]
    shift=[0]*b
    where=[-1]*m
    stride=len(shards[0])
    assert all(len(s)==stride for s in shards)
    def h1(k): return ((k*C+E)%PRIME)%b
    def h2(k,d): return ((k*(C+d*D)+E)%PRIME)%m
    for s,keys in enumerate(shards):
        for i,key in enumerate(keys):
            bucket[h1(key)].append((key,s*stride+i))
    for i in sorted(range(b),key=lambda i: -len(bucket[i])):
        if len(bucket[i]) < 2: break
        for d in range(100000):
            pos=[h2(k,d) for k,_ in bucket[i]]
            if len(set(pos))==len(pos) and all(where[j]<0 for j in pos):
                shift[i]=d
                for j,(_,o) in zip(pos,bucket[i]): where[j]=o
                break
        else: raise ValueError("displacement budget exceeded")
    free=iter(j for j,x in enumerate(where) if x<0)
    for i,A in enumerate(bucket):
        if len(A)==1:
            j=next(free)
            shift[i]=100000+j
            where[j]=A[0][1]
    assert all(x>=0 for x in where)
    def slot(k):
        d=shift[h1(k)]
        return d-100000 if d>=100000 else h2(k,d)
    assert all(where[slot(k)] == s*stride+i for s,A in enumerate(shards) for i,k in enumerate(A))
    return b,m,stride,shift,where

def data_module(M, name, entries, size=64):
    chunks=[entries[i:i+size] for i in range(0,len(entries),size)]
    out=[f'import {M}','namespace HaarOwnerPayload','set_option maxRecDepth 8000']
    for i,A in enumerate(chunks):
        out.append(f'private def {name}Bank{i} : Array ℕ := #['+', '.join(map(str,A))+']')
    def tree(d,f):
        if d+1>=f:return f'{name}Bank{d}'
        m=(d+f)//2
        return f'(if i < {m} then {tree(d,m)} else {tree(m,f)})'
    out.extend([f'private def {name}Bank (i : ℕ) : Array ℕ := '+tree(0,len(chunks)),
                f'def {name} (i : ℕ) : ℕ := ({name}Bank (i/{size}))[i%{size}]!',
                'end HaarOwnerPayload'])
    return '\n'.join(out)+'\n'

def generate(coll, B,M,stride,shift,where):
    root=Path('.')
    pfx=f'HaarOwner{coll}'
    (root/(pfx+'Shift.lean')).write_text(data_module("Mathlib.Data.Nat.Basic",f'shift{coll}',shift))
    (root/(pfx+'Data.lean')).write_text(data_module(pfx+'Shift',f'slots{coll}',where))
    (root/(pfx+'Eval.lean')).write_text(f'''import {pfx}Data
namespace HaarOwnerPayload
def bucket{coll} (k : ℕ) : ℕ := ((k*{C}+{E})%{PRIME})%{B}
def slot{coll} (k : ℕ) : ℕ :=
  let d := shift{coll} (bucket{coll} k)
  if d ≥ 100000 then d-100000 else ((k*({C}+d*{D})+{E})%{PRIME})%{M}
def owner{coll} (k : ℕ) : ℕ×ℕ :=
  let i := slots{coll} (slot{coll} k)
  (i/{stride},i%{stride})
end HaarOwnerPayload
''')
if __name__=='__main__':
    S,T=map(int,sys.argv[1:3])
    shards,_,_=make(S,T)
    cert=place(shards)
    name=f'F{p}S{S}T{T}' if p!=17 else f'S{S}T{T}'
    generate(name,*cert)
    print(f'{name} {len(shards)} shards and {cert[1]} rows; displacement max '+str(max(d for d in cert[3] if d<100000)))
