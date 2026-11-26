from itertools import product

def supports(k,h,f,b,truth):
    result=set()
    for x in product((-1,0,1),repeat=k): # -1 = missing/rejected
        if any(xi==1-truth for xi in x[:h]):
            continue # ideal certificates cannot certify a wrong value
        d=x.count(-1)
        wrong=x[h:].count(1-truth)
        if wrong+max(0,d-f)<=b:
            result.add(x)
    return result

m=0
for k in range(9):
    for h in range(k+1):
        for f in range(k+2):
            for b in range(k+2):
                obs0=supports(k,h,f,b,0)
                obs1=supports(k,h,f,b,1)
                exp=k>=f+b+1 and k+max(0,h-f)>=f+2*b+1
                assert obs0.isdisjoint(obs1)==exp,(k,h,f,b)
                m+=1
print(m,'complete binary view intersections')

# For each nonzero RS difference over small fields, check the exact joint
# pair-support condition, against the closed form closed independently.
for p in (2,3,5):
    for n in range(1,p+1):
        for K in range(1,n+1):
            words=[]
            for coeffs in product(range(p),repeat=K):
                if not any(coeffs):
                    continue
                words.append([sum(coef*pow(x,j,p) for j,coef in enumerate(coeffs))%p
                              for x in range(n)])
            d=n-K+1
            catalog=[{(sum(x!=0 for x in w),sum(x!=0 for x in w[:h])) for w in words} for h in range(n+1)]
            for h,f,b in product(range(n+1),repeat=3):
                support=catalog[h] #{(sum(x!=0 for x in w),sum(x!=0 for x in w[:h])) for w in words}
                res=all(k>f+b and k+max(0,g-f)>f+2*b for k,g in support)
                assert res==(d>f+b and d+max(0,h-(K-1)-f)>f+2*b)
                if res:
                    for z in range(max(0,h-K+1),n+1):
                        err=b-max(0,z-f)
                        if err>=0:
                            assert z+2*err<=n-K
                m+=1
print(m-2640,'RS parameter and actual difference-support checks')
