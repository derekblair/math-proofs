# Lower bound for explicit fixed-support catalogues only

Treat the r=f+1 protected sets as edges of an n-vertex hypergraph.
A universal witness catalogue makes its transversal number at least
c+1; otherwise the smaller hitting set may be padded to a c-set with
no surviving witness. More generally any fixed-coordinate shift
witness must change at least f+1 positions, when the exact share
decoder can recover from losing any f positions and all other
secret-relevant input remains fixed. Erasing a smaller shift support
would give identical surviving inputs for two plaintexts. Shrinking
larger supports to r cannot hurt cover validity. This is not a lower
bound on reductions that program after observing disclosures or use
a hidden randomized support.

Choose a uniform s-set, 0≤s≤c, then add one vertex from each unhit
edge. The size of this hitting set is at most s plus the count of
unhit edges. Since every completed set must have size ≥c+1, taking
expectation gives
  W ≥ max_s (c+1−s) binom(n,r)/binom(n−s,r).
This is the classical transversal alteration method (see Noga
Alon, Graphs and Combinatorics 1990, primary paper
https://web.math.princeton.edu/~nalon/PDFS/Publications/Transversal%20numbers%20of%20uniform%20hypergraphs.pdf ).
Averaging is the s=c case. This also follows by residual restriction
and can be weaker numerically than rounded Schönheim recursion.
No novelty is claimed for the combinatorics.

Write b=n−c,d=c−s. For r≥2, the ratio of the d+1 term to the d
term is [(d+2)/(d+1)]·[(b+d+1−r)/(b+d+1)], so it is >1 iff
(r−1)d<b+1−2r. An exact maximizing d is therefore the value
ceil((b+1−2r)/(r−1)) clipped to 0..c (ties possible). For r=1
the bound is exactly c+1, also attained. In the fixed-fraction
slack and r=Θ(log n) regime, b=Θ(n) and d∼b/r, so
  binom(b+d,r)/binom(b,r)
    = product_(j=0..r−1) (1+d/(b−j)) = e^(1+o(1)).
Writing p=binom(b,r)/binom(n,r), any explicit catalogue needs
  W ≥ (1+o(1)) b/(e r p).
The simple random universally covering upper O(n/p) then differs
only by an O(log n) factor in that regime. This does not contradict
PRIVATE_WITNESS.md, whose reduction samples S implicitly and
deliberately does not require its support distribution to be a
polynomial-size explicit catalogue. At (n,c,r)=(130,63,7), averaging
is 122, the alteration bound is 484, and rounded Schönheim is 744;
existing explicit 4,678-witness portfolio is an upper, not optimum.
