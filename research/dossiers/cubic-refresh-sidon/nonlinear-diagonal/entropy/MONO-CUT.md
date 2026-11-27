# Thin-support direction sampling cannot close the exact refresh entropy gap

Let n be even, 2≤k≤n/2, and S a random k-subset of the n sites.
Assume the probability that S is wholly on one side of A|A^c is
the same for every m-subset A, where m=n/2. If n≥16k², every atom
of S has probability at most (8k²/n)^floor(k/2). Thus its min-entropy
and Shannon entropy are both at least floor(k/2) log₂(n/(8k²)).

For even t≤k, fix distinct x_i forming X and choose a uniform ordered
t-tuple of distinct y_i outside X. For each of the 2^t switches choose
one endpoint of each pair to put in A; fill A with the same uniformly
chosen (m−t)-subset of the n−2t other sites. The alternating sum of the
monochromatic probabilities vanishes by assumption. Condition on S,
then average over the filler. If S uses both endpoints of any pair,
it is never monochromatic. If S uses neither endpoint of a pair,
the opposite switches cancel. Otherwise S uses exactly one endpoint
per pair. In that case the only two possible switches are complementary
and have the same sign because t is even. Each contributes probability
p=binom(m−t,k−t)/binom(n−2t,k−t)>0 (the remaining support falls wholly
inside, respectively wholly outside, the filler). Therefore posterior
signs reduce to an exact balance of positive and negative total masses
among S with exactly one endpoint per pair.

Let M_t be the greatest probability of containing a fixed t-set, M_0=1.
Choose X attaining M_t. Conditional on X⊂S, the probability that the
random Y avoids S is p₀=binom(n−k,t)/binom(n−t,t)≥1−t(k−t)/(n−t)≥1/2.
This bounds the all-X contribution from below. For a fixed odd s-set
of swaps I, a negative contribution requires S to contain X outside I
and all s chosen Y coordinates. The probability of the latter,
conditional on S, is at most (k/(n−2t))^s by sampling without replacement.
Discarding all other positive terms gives
    M_t ≤ 2 sum over odd s≤t of binom(t,s)(k/(n−2t))^s M_(t−s).
For odd t, monotonicity gives M_t≤M_(t−1).

Take η=8k²/n≤1/2 and x=tk/(n−2t)≤η/4. Induct on d with t=2d
and M_0=1. For s=2j+1 we have M_(t−s)≤η^(d−j−1).
Divide the recurrence by η^d and bound binom(t,s)≤t^s/s!;
the ratio is at most (2x/η) sum_(j≥0)(x²/η)^j/(2j+1)!
≤ (1/2)/(1−1/32) < 1. Hence M_(2d)≤η^d; restrict any k-set
to its first 2floor(k/2) elements to obtain the atom bound.

## Application and scope

Over F_(2^r), consider zero-sum refresh directions supported on k=r+1
sites, giving r sites independent basis values and the last their sum.
Their balanced quotient vanishes exactly when the support is
monochromatic. Multiplication by an independent nonzero field scalar
makes every nonzero quotient value uniform. Mixing in the zero
vector with a fixed probability requires the monochromatic probability
to be constant in A, so this theorem applies to the active support
law. Exact privacy bounds the zero-vector mixture mass by 1/q, since
the zero quotient must have probability 1/q. Further, nonzero scalar
multiplication preserves support, so the refresh entropy is at least
(1−1/q) times the active support entropy. Thus in this sparse
direction architecture r=Theta(log n) requires Omega(log² n) bits;
no bound of this size is claimed for arbitrary refreshes. Written
proof, not yet Lean formalized or checked for priority.
