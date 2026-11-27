# Exact size of the universal profile graph

For fixed excess s, ignoring the outside capacity limits (the single
universal graph for all t,u), the vertex count satisfies
$$
|V_{2k}|=\sum_{j=0}^{k}(k-j+1)^2\binom{2k}{j}
        = \frac{(k+2)4^k+2(2k+1)\binom{2k}{k}}{4},\qquad
|V_{2k+1}|=2|V_{2k}|.
$$
In particular this graph has Theta(s 2^s), not just the earlier
elementary O(s^2 2^s) bound. This does not make maximum clique polynomial
in s or find a general maximum clique complexity improvement.

Proof: For a center mask with m ones write p_h for its number of ones
in the first h positions. The walk X_h=2p_h-h has unit steps and ends at
D=2m-s. Its prefix compatibility with itself is
max_h X_h ≥ 2r + max(0,2j-s), where r is the missing initial mass and
j is full-set size above t. The outside mass is z=j+r-m ≥ 0. Substitute
j=m-r+z: the target level is H=max(2r,D+2z). In particular H≥0 and H≥D.

Reflect the walk after its first visit to H. Its new terminal height
is 2H-D≥H. Conversely every walk from 0 to 2H-D hits H, including the
case H=0 or terminal height exactly H, and the same reflection recovers
the original. Therefore for fixed (r,z,m) the vertex count is
choose(s,m-H) = choose(s,min(m-2r,s-m-2z)).
An out-of-range binomial is zero. For nonzero counts m≥2r and m≤s-2z
imply 0≤j≤s automatically, and also r+z≤floor(s/2).

Sum by a=r+z (a+1 pairs) and x=m-2r. The inner sum is
Σ_{x=0}^{s-2a} choose(s,min(x,s-2a-x)).
For s=2k this is 2Σ_{j<k-a} choose(2k,j)+choose(2k,k-a).
On exchanging sums the coefficient is (k-j+1)^2. For s=2k+1 the
inner sum is 2Σ_{j≤k-a} choose(2k+1,j), which by Pascal is exactly
twice the even inner sum. To evaluate the even formula, expand the
square. Symmetry gives Σ_{j≤k} choose(2k,j)=(4^k+C)/2 for C=choose(2k,k).
The first centered moment on that half is (k/2)C, by telescope of
(k-j)choose(2k,j)=k[choose(2k-1,j)-choose(2k-1,j-1)] for k≥1.
The second centered moment on the half is (k/4)4^k by symmetry and the
binomial variance k/2. This gives the stated expression; k=0 is immediate.

The formula is independent of the specific t,u and no priority claim is
made. Lean already proved directly the actual counts at s=4,5,6,7;
the all-s reflection and moment identity are not yet Lean-verified.

Formal status at 04:16 UTC: the exact partition of the actual duplicate-free
vertex list into feasible (r,z,m) buckets and the binomial cardinality of
each bucket are now Lean-verified. The theorem is
`IU.UniversalCount.vertexCount_sum` in `WalkGraphCount.lean`. The remaining
Lean work is a finite-sum reindexing and the closed-form evaluation above.
