from math import isqrt,sqrt
from itertools import combinations
for m in range(1,26):
 q=2*m+1; b=2+isqrt(3*m*m); n=q*b-m; mult=1-2*b
 p=[(mult*i)%n for i in range(n)]
 assert len(set(p))==n and (q*mult)%n==1
 # If a row gap is ≥ 2m, it already has the required Euclidean separation.
 least=min((j-i)**2+(p[i]-p[j])**2 for i in range(n)
           for j in range(i+1,min(n,i+2*m+2)))
 assert least >= 4*m*m,(m,b,n,least)
 print(m,n,least,round(n/m**2,6))
