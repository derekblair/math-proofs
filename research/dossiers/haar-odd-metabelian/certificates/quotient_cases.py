"""Independent finite arithmetic audit for reduction of short relations."""
from math import gcd

def relation_types():
    T=set()
    for a in range(-3,4):
      for b in range(-3,4):
        c=-a-b
        if a==b==0:continue
        if a%2==b%2==0:a0,b0,c0=a//2,b//2,c//2
        else:a0,b0,c0=a,b,c
        S=(a0,b0,c0)
        T.add(min(tuple(sorted(S)),tuple(sorted(-z for z in S))))
    return T

def canon(n,S):
    assert len(set(x%n for x in S))==3
    return min(tuple(sorted((a*x+c)%n for x in S))
      for a in range(n) if gcd(a,n)==1 for c in range(n))

def primitive_cases():
    unresolved=set()
    for S,w in [((0,1,3),10),((0,1,4),12),((0,2,5),13)]:
      for n in range(3,w,2):
        if len(set(x%n for x in S))==3 and canon(n,S)!=canon(n,[0,1,2]):
          unresolved.add((n,canon(n,S)))
    return unresolved

def torsion_cases(n,k):
    T=set()
    for z in range(n):
      for t in range(n):
        if gcd(gcd(t,z),n)!=1 or t==0 or (3*t)%n:continue
        S=(0,t,z) if k==0 else (0,z,2*z+t)
        if len(set(x%n for x in S))==3:T.add(canon(n,S))
    return T

if __name__=='__main__':
    assert relation_types()=={(-1,0,1),(-2,1,1),(-3,1,2),(-4,1,3),(-5,2,3),(-3,0,3),(-6,3,3)}
    assert primitive_cases()=={(7,(0,1,3)),(9,(0,1,3)),(11,(0,1,3))}
    assert torsion_cases(9,0)=={(0,1,3)}
    assert torsion_cases(9,1)=={(0,1,2)}
    assert torsion_cases(15,1)=={(0,1,3),(0,1,4)}
    print('seven relation types; cyclic corner cases independently audited')
