from quotient import *
from math import prod
from collections import Counter

def int_poly_vals(s,V,C,t,u):
    weights=[prod(range(t+1,t+j+1))*prod(range(u+1,u+s-j+1)) for j in range(s+1)]
    W=[binom(t,r)*binom(u,j+r-mask.bit_count())*weights[j] for r,mask,j in V]
    return [sum(W[i] for i in c) for c in C]
def newton1(a):
    r=[]
    while a:
        r.append(a[0]);a=[j-i for i,j in zip(a,a[1:])]
    return r
def control(s,best,params):
    V,A=graph(s); C=tuple(maximal(A))
    deg=s+max(r+j+r-mask.bit_count() for r,mask,j in V)
    G=[[int_poly_vals(s,V,C,*params(a,b)) for b in range(deg+1)] for a in range(deg+1)]
    # It is valid to use total-degree degree bound in each coordinate.
    fails=[]
    for ck in range(len(C)):
        Z=[newton1([G[a][b][best]-G[a][b][ck] for b in range(deg+1)]) for a in range(deg+1)]
        out=[newton1(list(col)) for col in zip(*Z)]
        mn=min(z for col in out for z in col)
        if mn<0:fails.append((ck,mn,out[0][0]))
    print(s,len(V),len(C),degree if (degree:=deg) else 0,best,len(fails),fails[:24],flush=True)
    return fails

if __name__=='__main__':
    for s,w in [(4,5),(5,29)]:
        control(s,0,lambda a,b:(1+a,1+2*a+b))
        control(s,w,lambda a,b:(2+a+b,2+2*a+b))
