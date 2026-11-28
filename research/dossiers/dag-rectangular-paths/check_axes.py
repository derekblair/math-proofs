"""Independent small cohort contraction vs direct scalar kernel over F_2."""
from itertools import product
from random import Random
rng=Random(496)
def mm(X,Y):return [[sum(a*b for a,b in zip(row,col))%2 for col in zip(*Y)] for row in X]
tests=0
for _ in range(30):
   N=11; out=[range(2,5),range(5,8),range(2,N)][_%3]; D=list(range(max(out)+1)); J=list(out); W=J[:2]
   X=[[[rng.randrange(2) if a<b else 0 for b in range(N)] for a in range(N)] for i in range(2)]
   P=[]
   for i in range(2):
      P.append([[int(a==b) for b in range(N)] for a in range(N)])
      for a in range(N):
       for b in range(a+1,N):
        P[i][a][b]=sum(P[i][a][c]*X[i][c][b] for c in range(a,b))%2
   Q={(w,c,e):rng.randrange(2) if c<w and e<w else 0 for w,c,e in product(W,D,D)}
   def K(i,w,c,e):
      if e<w:return int(c==e)
      if e==w:return 0
      return sum(X[i][c][d]*P[i][d][e] for d in range(w+1,e+1))%2
   def transform(Q,i):
      rows=list(product(W,D))
      old=lambda w,z,c: Q[w,c,z] if i==0 else Q[w,z,c]
      T=mm([[old(w,z,c) if c<w else 0 for c in D] for w,z in rows],[[X[i][c][d] for d in J] for c in D])
      Y=mm([[v if d>w else 0 for d,v in zip(J,row)] for (w,z),row in zip(rows,T)],[[P[i][d][e] for e in J] for d in J])
      result={}
      for (w,z),row in zip(rows,Y):
       read=dict(zip(J,row))
       assert all(v==0 for e,v in read.items() if e<=w)
       for e in D:
        key=(w,e,z) if i==0 else (w,z,e)
        result[key]=old(w,z,e) if e<w else 0 if e==w else read[e]
      return result
   got=transform(transform(Q,0),1)
   for (w,a,b),x in got.items():
      assert x==sum(Q[w,c,e]*K(0,w,c,a)*K(1,w,e,b) for c,e in product(range(w),repeat=2))%2
      tests+=1
print(tests,'binary two-axis direct kernel/cohort comparisons')
