"""Exact scaled-integer layout DP. No cryptographic or network operations."""
from math import comb,lcm
from fractions import Fraction
from functools import reduce

H,F,N=64,6,130
R=F+1
B=N-H
GMAX=min(H,B//F)
SMAX=B-F
den=[comb(F+s+1,R) for s in range(SMAX+1)]
L=reduce(lcm,den,1)
cost={(h,s):comb(h+F+s,R)*(L//den[s])
      for h in range(1,H+1) for s in range(SMAX+1)}

states={(0,0):(0,None)}
layers=[states]
terminal={}
for g in range(1,GMAX+1):
    sl=B-F*g
    out={}
    for (prev_h,prev_s),(value,_) in states.items():
        hmin=1 if g>1 else 1
        for h in range(hmin,H-prev_h+1):
            for s in range(sl-prev_s+1):
                key=(prev_h+h,prev_s+s)
                v=value+cost[h,s]
                old=out.get(key)
                if old is None or v<old[0]:
                    out[key]=(v,(prev_h,prev_s,h,s))
    for (h,s),(v,_) in out.items():
        if h!=H:continue
        D=H+s
        Nused=H+s+g*F
        row=terminal.get(D)
        if row is None or v<row[0]:
            terminal[D]=(v,g,Nused)
    layers.append(out)
    states=out

def build(g,s):
    layout=[]
    hnew=H
    for i in range(g,0,-1):
        hp,sp,h,s0=layers[i][hnew,s][1]
        layout.append((h+s0+F,h,h+s0))
        hnew,s=hp,sp
    return sorted(layout)

def at_cap(cap):
    D=min((D for D in terminal if D<=cap),key=lambda D:terminal[D])
    v,g,n=terminal[D]
    lay=build(g,D-H)
    W=sum(Fraction(comb(a,R),comb(a-h+1,R)) for a,h,k in lay)
    assert W==Fraction(v,L) and sum(a for a,h,k in lay)==n
    assert sum(h for a,h,k in lay)==H and sum(k for a,h,k in lay)==D
    return D,n,W,lay

for cap in (64,70,76,80,82,84,88,92,100,112,124):
    d,n,v,lay=at_cap(cap)
    print(cap,'=>',d,n,v,float(v),lay)
