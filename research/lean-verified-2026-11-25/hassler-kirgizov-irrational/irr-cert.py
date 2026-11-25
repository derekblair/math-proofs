from itertools import permutations
from math import sqrt
allowed={(1,2,3,4),(2,1,3,4),(1,3,2,4),(1,2,4,3),(2,1,4,3)}
def pat(x):return tuple(1+sum(a<b for a in x) for b in x)
def exact(n):
    a=b=0
    for P in permutations(range(n)):
        w=[pat(P[i:i+4]) for i in range(n-3)]
        if all(s in allowed for s in w):
            a+=1
            b+=w.count((2,1,4,3))
    return a,b
F=[0,1]
for i in range(450):F.append(F[-1]+F[-2])
for n in [4,5,6,7,8,9,20,50,100,300]:
    a,b=F[n+1],sum(F[j+1]*F[n-3-j] for j in range(n-3))
    if n<=9:assert exact(n)==(a,b),n
    print(n,a,b,b/(n*a))
print('limit',1-2*sqrt(5)/5)
