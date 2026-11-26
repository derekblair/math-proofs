"""Independent exact full-matrix generator for the Haar class-five rank certificate."""
from pathlib import Path
import sys
import os
p = int(os.environ.get("HAAR_CERT_FIELD","17"))
I = tuple(tuple(int(i == j) for j in range(6)) for i in range(6))
def multiply(A, B):
    return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(i,j+1)) % p if i<=j else 0
                       for j in range(6)) for i in range(6))
def power(A, k):
    R = I
    while k:
        if k & 1:
            R = multiply(R, A)
        A = multiply(A, A)
        k >>= 1
    return R
def port(row):
    return tuple(tuple(1 if i==j else row[i] if j==i+1 else 0 for j in range(6)) for i in range(6))
ports={17:([2,1,7,1,15],[1,5,15,9,15]),31:([14,22,19,2,14],[28,11,15,24,13])}
X,Y=map(port,ports[p])
moves = ((I, power(X,p-1), power(Y,p-1)),(I,X,Y))
assert multiply(moves[0][1],X)==I and multiply(moves[0][2],Y)==I
def walk(n, depth=0, state=I, last=3):
    if n==0:
        yield depth, state, last
    else:
        for j in range(3):
            if j!=last:
                yield from walk(n-1,depth+1,multiply(state,moves[1-depth%2][j]),j)
def packed(A):
    code = 0
    for i in range(6):
        for j in range(i+1,6):
            code = code*p + A[i][j]
    return code
def make(split, tail):
    shards = [[packed(A) for _,A,_ in walk(tail,*q)] for q in walk(split)]
    rows = sorted((key,s,i) for s,shard in enumerate(shards) for i,key in enumerate(shard))
    assert all(a[0] < b[0] for a,b in zip(rows,rows[1:]))
    assert len(rows) == 3*2**(split+tail-1)
    ranks = [[None]*len(shard) for shard in shards]
    for r,(_,s,i) in enumerate(rows):
        ranks[s][i]=r
    return shards,rows,ranks

if __name__=='__main__':
    S,T = map(int,sys.argv[1:3])
    shards,rows,ranks=make(S,T)
    print(f'shards={len(shards)} rows={len(rows)} unique=yes')
    if 'prototype' in sys.argv:
        st=['import HaarMatrixShards','open HaarMatrixShards',
            'set_option maxRecDepth 40000','set_option maxHeartbeats 0']
        for j in (0,len(shards)//2,len(shards)-1):
            st.append(f'theorem exact_shard_{j} : (shards {S} {T})[{j}]! = '
                      f'{shards[j]} := by decide +kernel')
            st.append(f'#print axioms exact_shard_{j}')
        Path('HaarMatrixPrototype.lean').write_text('\n'.join(st)+'\n')
