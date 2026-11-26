from itertools import product
from functools import reduce
from operator import xor
from span_search import *
petersen_chords,_,_=json.load(open('petersen.json'))
N,A=step_graph(5,2)
rows,d=compute(N,A,petersen_chords,words(N,A,{4,8}))
assert len(rows)==15 and not any(c for z,c in rows)
for D in ["C1","C2","C3","C4","V4","C5"]:
 n=4 if D=="V4" else int(D[1])
 def val(x,z):
  return reduce(xor,(a for a,t in zip(x,z) if t%2),0) if D=="V4" else sum(a*t for a,t in zip(x,z))%n
 sol=[x for x in product(range(n),repeat=d) if all(val(x,z) for z,c in rows)]
 print(D,len(sol),sol[0] if sol else None)
