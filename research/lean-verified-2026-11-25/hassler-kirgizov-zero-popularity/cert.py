from itertools import permutations
from collections import Counter

P=(2,4,5,3,1)
I=(1,2,3,4,5)
A={I,(5,4,3,2,1),(1,2,4,5,3),P,(4,5,3,2,1),(2,1,4,3,5),(1,3,2,5,4)}
B=A-{P}
def magic(x):
 return tuple(1+sum(e<y for e in x) for y in x)
def scan(n):
 a=b=ai=bi=ap=aq=bq=0
 for seq in permutations(range(1,n+1)):
  words=[]
  for i in range(n-4):
   q=magic(seq[i:i+5])
   if q not in A:break
   words.append(q)
  else:
   a+=1; ai+=words.count(I); ap+=words.count(P); aq+=words.count((2,1,4,3,5))
   if P not in words: b+=1;bi+=words.count(I);bq+=words.count((2,1,4,3,5))
 assert (a,b,ap,aq,bq)==(2**(n-4)+5,6,2**(n-4)-1,n-4,n-4)
 return n,a,b,ai,bi,ap,aq,bq
if __name__=='__main__':
 for n in range(5,10):print(scan(n),flush=True)
