from rational_intervals import *
c,t,delta,alpha=map(F,['11.476','.0073948','.06193','.0060375'])
l2=log(2)
gamma=div(mul(box(t),log((c-1)/4)),l2)
q=div(add(H(t),mul(box(t),log(4))),l2)
denom=add(sub(sub(mul(box(c),log(5)),mul(box(c/2),H(1/c))),mul(box(c-1),l2)),mul(gamma,l2))
R=div(l2,denom)
p=12+delta
pre=sub(mul(box(p),gamma),box(2*delta))
qry=sub(box(1-delta),mul(box(p),q))
feat=sub(R,box(p*alpha))
assert all(x[0]>0 for x in (pre,qry,feat)), [list(map(float,x)) for x in (pre,qry,feat)]
saving=alpha*delta
assert saving>F('.0003738')
print('gamma/query/radius:',[list(map(float,x)) for x in (gamma,q,R)])
print('margin:',[list(map(float,x)) for x in (pre,qry,feat)])
print('raw exponent',float(2-saving),'exact gap',saving)
