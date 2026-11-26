from rational_intervals import *
c,t,delta,alpha=map(F,['24.26','.014561','.06012','.004070'])
l4=log(4)
gamma=div(mul(box(t),log((c-1)/9)),l4)
q=div(add(H(t),mul(box(t),log(9))),l4)
denom=add(sub(sub(mul(box(c),log(10)),mul(box(c/2),H(1/c))),mul(box(c-1),log(3))),mul(gamma,l4))
R=div(l4,denom)
p=12+delta
pre=sub(mul(box(p),gamma),box(2*delta))
qry=sub(box(1-delta),mul(box(p),q))
feat=sub(R,box(p*alpha))
assert all(x[0]>0 for x in (pre,qry,feat)), [list(map(float,x)) for x in (pre,qry,feat)]
saving=alpha*delta
assert saving>F('.0002446')
print('margin:',[list(map(float,x)) for x in (pre,qry,feat)])
print('raw exponent',float(2-saving),'exact gap',saving)
