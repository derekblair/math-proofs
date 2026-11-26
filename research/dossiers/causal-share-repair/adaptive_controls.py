"""Exhaustive finite synthetic prefix-law checks, not a repair transport."""
from itertools import product
from collections import Counter, defaultdict

Q=5; T=2
P=list(product(range(Q),repeat=T+1))

def plus(x,y):
    return tuple((a+b)%Q for a,b in zip(x,y))

def scal(i,x):
    return tuple(i*a%Q for a in x)

def val(h,a):
    return sum(c*a**i for i,c in enumerate(h))%Q

def messages(h,a,vis=(0,1,2)):
    sites=[x for x in range(1,Q) if x!=a]
    def weight(x):
        w=1
        for y in sites:
            if x!=y:
                w=w*(a-y)*pow((x-y)%Q,-1,Q)%Q
        return w
    return tuple(weight(sites[i])*val(h,sites[i])%Q for i in vis)

def space_extend(zero, W, ext):
    # ext maps a subspace of the old pad space to section values.
    ext=dict(ext)
    for x in sorted(W):
        if x not in ext:
            keep=list(ext.items())
            for c in range(1,Q):
                for u, v in keep:
                    ext[plus(u,scal(c,x))]=v
    assert set(ext)==W and ext[(0,)*len(next(iter(W)))]==zero
    return ext

def full_visibility_adaptive():
    # First repaired value authorized at stage 1. The second target depends
    # on one earlier visible value. No fresh refresh state is present.
    a=1
    W={messages(h,a) for h in P if val(h,a)==0}
    data={}
    for target in (2,3):
        K={(messages(h,a),messages(h,target)) for h in P if val(h,a)==val(h,target)==0}
        section={}
        for x,y in K:
            assert x not in section or section[x]==y
            section[x]=y
        lift=space_extend((0,0,0),W,section)
        assert K <= set(lift.items())
        assert len(lift)==25
        data[target]=lift
    test=0
    for h in P:
        forced={}
        shadows={}
        for b in (2,3):
            y=(val(h,a),val(h,b))
            same=[g for g in P if (val(g,a),val(g,b))==y]
            laws=[]
            for g in same:
                laws.append(Counter((plus(messages(g,a),old), plus(messages(g,b),new))
                                    for old,new in data[b].items()))
                test+=1
            assert all(c==laws[0] for c in laws)
            forced[b]=laws[0]
            shadows[b]=same[-1]
        real=Counter()
        simulator=Counter()
        for old in W:
            m=plus(messages(h,a),old)
            b=2 if m[0] in (0,2,4) else 3
            real[b,m,plus(messages(h,b),data[b][old])]+=1
        g=next(g for g in P if val(g,a)==val(h,a))
        for old in W:
            m=plus(messages(g,a),old)
            b=2 if m[0] in (0,2,4) else 3
            comparisons=Counter({n:v for (u,n),v in forced[b].items() if u==m})
            assert sum(comparisons.values())==1
            for n,v in comparisons.items():
                simulator[b,m,n]+=v
        assert real==simulator
    return test

def mixed_visibility():
    # Nothing authorized. One visible helper allows arbitrary visible pad
    # while a hidden component cancels it in the sum.
    for v in range(3):
        k1={messages(h,1,(v,)) for h in P}
        assert len(k1)==5
        for w in range(3):
            k2={(messages(h,1,(v,)),messages(h,1,(w,))) for h in P}
            assert len(k2)==(5 if v==w else 25)
    assert any(sum(messages(h,1))%Q for h in P)
    # All helpers visible and target not authorized: pad is constrained to
    # sum zero, yet some target-shift direction is outside that space.

def memory_tradeoff():
    # Small linear pad space; cover all diagonal shifts and exact support sizes.
    q=3; t=2; E=3
    vectors=list(product(range(q),repeat=t))
    for m in range(4):
        k=min(m,t)
        laws=Counter()
        for state in product(range(q),repeat=k):
            for tails in product(list(product(range(q),repeat=t-k)),repeat=E):
                laws[tuple(state+tail for tail in tails)]+=1
        assert len(laws)==q**(t+(E-1)*max(0,t-m))
        for v in vectors:
            for path,prob in laws.items():
                translated=tuple(tuple((a+b)%q for a,b in zip(stage,v)) for stage in path)
                assert laws[translated]==prob

if __name__=='__main__':
    n=full_visibility_adaptive()
    mixed_visibility()
    print(n, 'forced-prefix equal-output law comparisons;', len(P), 'adaptive complete histories.')
    print('Nine mixed helper-visibility/correlation controls and impossible hidden full sum checked.')
    memory_tradeoff()
    print("Four exact finite-state stationary memory tradeoffs checked.")
