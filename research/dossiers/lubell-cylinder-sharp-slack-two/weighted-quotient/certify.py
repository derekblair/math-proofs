from newton_domination import *
from hashlib import sha256
expected={4:(31,22,5),5:(62,105,29),6:(150,1648,191)}
for s,(nv,nc,k) in expected.items():
    V,A=graph(s)
    C=tuple(maximal(A))
    assert (len(V),len(C))==(nv,nc)
    def check(best,f):
        assert not control(s,best,f)
        other=k if best==0 else 0
        t,u=f(0,0)
        x,y=int_poly_vals(s,V,(C[best],C[other]),t,u)
        assert x>y
    check(0,lambda a,b:(1,2+b))
    if s<=5:
        check(0,lambda a,b:(2+a,3+2*a+b))
        check(k,lambda a,b:(2+a+b,2+2*a+b))
    else:
        check(0,lambda a,b:(2+a,3+3*a+b))
        check(k,lambda a,b:(2+a+b,2+3*a+b))
        check(k,lambda a,b:(3+a+b,4+3*a+b))
