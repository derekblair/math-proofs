from random import Random
from sweep import adj,topo
from dynamic import lift,reach,search

def dag(n,E,F):
    D={e for e in E if F.isdisjoint(e)}
    return len(topo(adj(n,D)))==n

def complement(E,F):
    return {e for e in E if F.isdisjoint(e)}

def transition(n,G1,F0,F1,D,removed,center=None):
    D=set(D); entering=F1-F0; leaving=F0-F1
    drops={e for e in removed if e in D}
    # On production lists this can be enumerated just at entering vertices;
    # the prototype uses a single final-graph scan for both phases.
    drops.update(e for e in G1 if not entering.isdisjoint(e) and e in D)
    D-=drops
    T=complement(G1,F1)
    assert D<=T and dag(n,D,set())
    batches={}
    original=[]
    for e in T:
        if e in D:continue
        u,v=e
        L=leaving.intersection(e)
        if L:batches.setdefault(min(L),[]).append(e)
        else:
            assert center is not None and center in e
            original.append(e)
    if original:batches.setdefault(center,[]).extend(original)
    assert len(batches)<=len(leaving)+1
    for z,b in sorted(batches.items()):
        assert all(z in e and e not in D for e in b)
        D.update(b)
        assert D<=T and dag(n,D,set())
    assert D==T
    return D,len(drops),sum(map(len,batches.values())),len(batches)

def run():
    rng=Random(109043);T=0;changed=0;maxB=0;dm=im=0;trans_cat=[0,0]
    for n in range(3,13):
      V=list(range(n))
      for k in range(1,min(n,5)):
        for _ in range(7):
          F=set(rng.sample(V,k));G=set();D=set()
          for t in range(105):
             newF=set(rng.sample(V,k)); center=None
             if t%3==1:
                # Deletion batch: impose a newly randomly ordered feasible complement.
                P=[u for u in V if u not in newF];rng.shuffle(P);rank={v:i for i,v in enumerate(P)}
                G1={e for e in G if (not newF.isdisjoint(e) or rank[e[0]]<rank[e[1]]) and rng.random()>.15}
             else:
                # Keep the old graph and add an incident batch consistent with F_new.
                if not dag(n,G,newF):newF=F
                P=topo(adj(n,complement(G,newF)));rank={v:i for i,v in enumerate(P)}
                center=rng.choice(V)
                add={(u,v) for u in V for v in V if u!=v and center in (u,v)
                    and (not newF.isdisjoint((u,v)) or rank[u]<rank[v]) and rng.random()<.35}
                G1=G|add
             assert dag(n,G1,newF)
             D,dd,ii,bb=transition(n,G1,F,newF,D,G-G1,center)
             if F!=newF:
                changed+=1;trans_cat[bool(G1-G)]+=1
             maxB=max(maxB,bb);dm+=dd;im+=ii
             O=lift(n,G1,newF)
             assert O<=G1 and reach(n,O)==reach(n,G1)
             for u,v in O:assert v not in search(adj(n,O-{(u,v)}),u)
             F,G=newF,G1;T+=1
    print(T,'updates;',changed,'changed anchors (with/without original inserts)',trans_cat[::-1],
          'max batches',maxB,'masked edits',dm,im)
if __name__=='__main__':run()
