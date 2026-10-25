# GCD determinants: a hypothesis and prior-art audit

Research note, 2026-10-25. Status: known-theory exposition and exact finite checks, not a novelty claim. The arguments below are written, unformalized arguments awaiting programme verification, not Lean-certified results. The computations are **[COMPUTED]**, not kernel certificates. No Lean files or formalization are supplied.

## Decision

The apparent coincidence between a GCD determinant and a product of totients is established theory, not a new research target. Its exact hypothesis is **factor closure**, not merely GCD closure. A divisor-incidence factorization explains both the product and the positive surplus when divisors are missing. The useful output of this audit is a reusable hypothesis test and explicit regression examples; neither the identity nor the arithmetic/linear-algebra connection clears a novelty gate.

## Sources and coverage

1. H. J. S. Smith, *On the Value of a Certain Arithmetical Determinant*, Proceedings of the London Mathematical Society s1-7 (1875/76), 208–212, [publisher record](https://doi.org/10.1112/plms/s1-7.1.208). Historical attribution only; the original full text was not inspected in this pass.
2. E. Altinisik, B. E. Sagan and N. Tuglu, *GCD matrices, posets, and nonintersecting paths*, author-hosted manuscript dated February 18, 2005, [full text](https://users.math.msu.edu/users/bsagan/Papers/Old/gcd.pdf), [arXiv record](https://arxiv.org/abs/math/0406155). Theorem 1.1 states the factor-closed product; Theorem 2.2 and the introduction explicitly place it in incidence-algebra and nonintersecting-path theory. This is direct prior art for both the identity and the proposed branch-of-mathematics bridge.
3. *The determinants of GCD matrices* (1990), [publisher record](https://doi.org/10.1016/0024-3795(90)90012-2). The accessible abstract states the product equality if and only if the set is factor closed. The article-body request returned HTTP 403, so no claim is made to have checked that paper's proof. The equality criterion is independently justified below.

This is a bounded source check, not an exhaustive literature survey. It is already sufficient to reject a novelty claim. The derivation below is self-contained exposition, not a claim to a new proof.

## 1. Definitions and factorization [Written argument, unformalized]

Let S={x_1,...,x_n} be a nonempty finite set of **distinct positive integers**, arranged increasingly. Let D be the union of their positive divisors. Define the n-by-|D| matrix E by E(i,d)=1 if d divides x_i and 0 otherwise. Define G(i,j)=gcd(x_i,x_j).

A set is factor closed when every positive divisor of each member is itself a member. It is GCD closed when the GCD of every two members belongs to the set. Factor closure implies GCD closure, but not conversely.

For every positive m, sum_{d|m} phi(d)=m: partition the integers 1,...,m according to gcd(k,m); the class with gcd(k,m)=m/d contains phi(d) elements. This includes phi(1)=1. Consequently

G = E diag(phi(d): d in D) E^T.

Indeed the (i,j) entry on the right is the sum of phi(d) over divisors common to x_i and x_j, hence over divisors of their GCD.

Let B=E_S, selecting the columns indexed by S in increasing order. Because a larger positive integer cannot divide a smaller one, B is lower triangular with diagonal 1. Thus det(B)=1. In particular E has full row rank. Since every phi(d)>0, the factorization also makes G positive definite: for nonzero v, E^T v is nonzero and its weighted sum of squares is positive.

## 2. Exact surplus formula and equality criterion [Written argument, unformalized]

Cauchy–Binet gives

 det(G) = sum_{T subset D, |T|=n} det(E_T)^2 product_{t in T} phi(t).

One way to see the weights without square roots is to apply Cauchy–Binet to E diag(phi) and E^T. Every summand is nonnegative. The T=S term has det(E_S)^2=1. Therefore

 det(G) >= product_{x in S} phi(x).

If S is factor closed then D=S, so only this one term exists and equality holds.

Conversely suppose d belongs to D but not S. Its incidence column v_d is nonzero because it divides at least one x_i. Write c=B^{-1}v_d, which is nonzero. Choose j with c_j nonzero. Replacing the j-th column of B with v_d gives determinant c_j det(B)=c_j by determinant multilinearity: every other component duplicates a remaining column and vanishes. This is a minor with column set T=(S minus {x_j}) union {d}; sorting T changes only its sign. Thus det(E_T)^2=c_j^2>0. All totient weights in this extra summand are positive, so the inequality is strict.

Hence equality holds **if and only if S is factor closed**. The proof provides a concrete extra-minor witness whenever a divisor is missing. Distinctness is essential to the invertible B argument; duplicates can make G singular. Zero or negative inputs are outside these definitions.

## 3. Small regressions [COMPUTED; direct arithmetic also displayed]

- S={1}: determinant 1, totient product 1.
- S={1,2,4}: factor closed; determinant 2, product 2.
- S={1,4}: GCD closed but not factor closed. G=[[1,1],[1,4]], determinant 3, product phi(1)phi(4)=2. This disproves replacing factor closure by GCD closure in the product formula.
- S={2,3}: determinant 2*3−1=5, product 2, surplus 3.
- S={2,4}: determinant 2*4−2*2=4, product 2, surplus 2.
- S={1,2,3,6}: factor closed; determinant 4, product 4.

For S={1,4}, the divisor set is {1,2,4}. Its E columns are (1,1)^T, (0,1)^T, (0,1)^T. The two nonzero 2-column minors contribute phi(1)phi(2)=1 and phi(1)phi(4)=2. The missing divisor 2 accounts for the entire surplus of 1.

## 4. Weighted boundary: positivity is not optional [Written argument, unformalized]

The same proof applies to M(i,j)=sum_{d|gcd(x_i,x_j)} g(d), with g(d)>0 for every d in D. Then det(M)>=product_{x in S}g(x), with equality exactly for factor-closed S. For a kernel f(gcd), the divisor weights are g=f*mu, the Dirichlet-convolution Möbius transform; positivity of f alone does not establish positivity of g.

With merely nonnegative g, the lower bound and factor-closed sufficiency survive but necessity can fail. For S={2}, choose g(1)=0 and g(2)=1. Then det(M)=1=g(2), despite the missing divisor 1. Thus a zero-weight missing divisor is invisible to this test. With signed weights, nonnegative-surplus reasoning is invalid altogether: S={2}, g(1)=−2, g(2)=1 gives det(M)=−1<1.

These are hypothesis checks, not new theories or purported extensions beyond existing weighted-incidence methods.

## 5. Reproducibility and limits

The standard-library script below was executed with exact rational Gaussian elimination on every nonempty subset of {1,...,8}: **255 sets checked, 44 equality cases**. For every set it checked the full Cauchy–Binet sum, the inequality, and equality equivalence to factor closure. Finite checks corroborate the examples; they do not replace the general argument. A separate mathematical review confirmed the replacement-column step and weighted caveats.

No Lean build or formalization was performed. Any later formalization belongs in the formalization role and must preserve the exact hypotheses; nothing here modifies existing theorem status or catalogues. This audit is complete: do not advance the product formula, its converse, or the incidence/path connection as novel. A future research direction needs a genuinely new, precise question and its own novelty screen.

### Exact verification script

```python
from fractions import Fraction as F
from itertools import combinations
from math import gcd,prod
import json

def det(a):
    a=[list(map(F,row)) for row in a]; n=len(a); out=F(1)
    for k in range(n):
        p=next((i for i in range(k,n) if a[i][k]),None)
        if p is None:return F(0)
        if p!=k:a[k],a[p]=a[p],a[k];out=-out
        q=a[k][k];out*=q
        for i in range(k+1,n):
            c=a[i][k]/q
            for j in range(k,n):a[i][j]-=c*a[k][j]
    return out

def divs(x):return {d for d in range(1,x+1) if x%d==0}
def phi(x):return sum(gcd(k,x)==1 for k in range(1,x+1))
def check(S):
    D=sorted(set().union(*(divs(x) for x in S)))
    G=[[gcd(x,y) for y in S] for x in S]
    lhs=det(G); base=prod(phi(x) for x in S)
    rhs=sum(det([[int(x%d==0) for d in T] for x in S])**2*prod(phi(d) for d in T) for T in combinations(D,len(S)))
    assert lhs==rhs and lhs>=base and ((lhs==base)==(set(S)==set(D)))
    return {'S':list(S),'det':int(lhs),'product_phi':base,'surplus':int(lhs-base)}
rows=[]
for n in range(1,9):
    for S in combinations(range(1,9),n):rows.append(check(S))
print(json.dumps({'sets_checked':len(rows),'equality_cases':sum(r['surplus']==0 for r in rows),'examples':[check(S) for S in [(1,),(1,2,4),(1,4),(2,3),(2,4),(1,2,3,6)]]},indent=2))

```
