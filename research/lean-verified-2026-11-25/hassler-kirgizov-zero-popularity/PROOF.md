# Counterexample to Hassler–Kirgizov Conjecture 5.1
Source: https://arxiv.org/pdf/2511.02442 (v3, §5 and equation (1)).
Take m=5 and forbid every pattern except 12345, 54321, 12453, 24531, 45321, 21435, 13254. Call the resulting class A. Let p=24531 and q=21435. B additionally forbids p. Both nonempty for all n.

Consecutive signs (+ ascent, - descent) in the seven allowed length-five windows:
12345 ++++; 12453 +++-; 24531 ++--; 45321 +---; 54321 ----; 21435 -+-+; 13254 +-+-.
Consecutive windows share three signs. The first five constitute a one-way chain with loops at the ends; the last two form a separate two-cycle. Consequently any A permutation is unimodal (increase then decrease, including pure cases) or alternating. In a unimodal sequence, a 24531 window occurs at most once, and 21435 never occurs. In an alternating sequence 24531 never occurs.

The only alternating permutations are formed from the increasing list by reversing consecutive pairs, with either initial parity and leaving an uncoupled endpoint alone. Indeed take pairs at each descent. The local 21435 or 13254 order forces all values of one pair to be less than both values of the next; the same holds for boundary singletons. These comparisons each occur within a length-five window, all pairs and singletons are internally totally ordered, and thus the unique order is the increasing order of the blocks with each pair descending. Each template satisfies every allowed local window. Between the two alternating permutations, every index that is a window start contributes exactly once to 21435. Thus the total q count in A and B is n-4 for n>=5.

A contains arbitrarily many permutations. For n>=6 and each x in {1,...,n-4}, form the sequence
  x, n-3, n-1, n, n-2, [all remaining labels in decreasing order].
The unique central window 24531 exists because at least one remaining label is to the right of n-2. The preceding crossing window is 12453, the next crossing window when it exists is 45321, all further windows are 54321. Distinct x give n-4 distinct permutations. Therefore POP_A(p)=0 (at most one occurrence per permutation and normalization by n), and POP_A(q)=0 (at most (n-4)/(n*(n-4))=1/n).

B's unimodal permutations must peak at index 1, 2, n-1 or n (one-based), since two elements on each side would require 24531. Peak at the endpoints gives two pure permutations. At index 2, the first window is 45321, forcing the lone left label to be second-largest. At n-1, the last window is 12453, forcing the lone right label to be third-largest. In each case monotonicity sorts the long side, giving exactly one permutation and they satisfy all windows. Together with the two alternating permutations, |B_n|=6. Hence POP_B(q)=(n-4)/(6n) -> 1/6, contradicting POP_A(q)=0. This alternative q (alternating) avoids any need to count A exactly or use a binomial sum.

For independent exact enumeration, A's interior-peak subset has m=n-4 free labels, with a proper subset on the left and its nonempty complement on the right. Maximum n, largest left n-1, largest right n-2 and second largest left n-3 are fixed. So |A_n|=2^(n-4)+5. Python brute force through n=9 matches. The Lean proof does not rely on the Python enumeration. It proves the three limits, the literal source formulation and its negation. See README.md.
