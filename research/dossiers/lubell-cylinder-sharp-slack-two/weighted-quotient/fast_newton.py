from quotient import *
from newton_domination import newton1
from collections import Counter
from math import prod
import numpy as np
def tables(s):
    V,A=graph(s); C=tuple(maximal(A))
    ty=[(r,j+r-mask.bit_count(),j) for r,mask,j in V]
    labels=sorted(set(ty)); ix={z:i for i,z in enumerate(labels)}
    Q=[ix[z] for z in ty]
    H=np.zeros((len(C),len(labels)),dtype=np.int64)
    for i,c in enumerate(C):
        for j,k in Counter(Q[x] for x in c).items():H[i,j]=k
    return labels,H,C

def work(s,target,params,L,H):
    deg=s+max(r+z for r,z,j in L)
    def at(r,z,j,a,b):
        t,u=params(a,b)
        return binom(t,r)*binom(u,z)*prod(range(t+1,t+j+1))*prod(range(u+1,u+s-j+1))
    N=[]
    for r,z,j in L:
        Z=[newton1([at(r,z,j,a,b) for b in range(deg+1)]) for a in range(deg+1)]
        N.append([x for col in zip(*Z) for x in newton1(list(col))])
    assert max(abs(x) for row in N for x in row)*(int(H.sum(1).max())*2)<2**63
    S=H@np.array(N,dtype=np.int64)
    D=S[target,:]-S
    bad=(D.min(1)<0)
    print('s',s,'target',target,'nbad',int(bad.sum()),'min',int(D.min()),'start',int(D[:,0].min()),flush=True)
    if bad.any():print('bad examples:',np.where(bad)[0][:40].tolist(),flush=True)
    return int(bad.sum()),D


if __name__=="__main__":
    s=7; L,H,C=tables(s)
    assert len(C)==79620 and len(L)==40
    cones=[
       (0,6865,lambda a,b:(1,2+b)),
       (0,6865,lambda a,b:(2+a,3+3*a+b)),
       (6865,0,lambda a,b:(2+a+b,2+3*a+b)),
       (6865,0,lambda a,b:(3+a+b,4+3*a+b))]
    for i,other,f in cones:
        bad,D=work(s,i,f,L,H)
        assert not bad and D[other,0]>0
