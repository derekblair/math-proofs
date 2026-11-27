# A sharp directional bound for sorting probabilities in finite posets

Let \(P\) be a finite poset, \(x,y\) incomparable, and \(L\) a uniformly
random linear extension. With strict downsets \(D\) and strict upsets \(U\), put
\[
a=|D(y)\setminus D(x)|,\qquad b=|U(x)\setminus U(y)|.
\]
Then
\[
\Pr(y<_L x)\ge \binom{a+b+2}{a+1}^{-1}.
\]
The bound is sharp for every pair of nonnegative integers \(a,b\).
It is a bound for a specified pair and orientation, not a solution of the
general 1/3–2/3 conjecture.

## Proof

Put \(A=\{x\}\cup(U(x)\setminus U(y))\) and
\(B=\{y\}\cup(D(y)\setminus D(x))\). The sets are disjoint, since a common
element would imply \(x\leq_P y\). In the restriction of any extension to
\(A\cup B\), \(x\) is the first A and \(y\) the last B. Partition the
extensions into fibers by the absolute positions of all other elements
and the relative orders within \(A\) and within \(B\).

In the filtered word, take neighboring A and B letters in order AB, at
positions \(p<q\) in the full word. Moving the A letter to \(q\) and the B
letter to \(p\) preserves the partial order. The A letter cannot precede the
B letter in \(P\), because \(x\leq_P A\) and \(B\leq_P y\). An intervening
element \(z<_P B\) would satisfy \(z<_P y\) without \(z<_P x\), since \(z\)
is after \(x\) in the extension, and would belong to B. Likewise an
intervening element \(A<_P z\) would belong to A. Both are excluded by
adjacency in the filtered word. This rules out every violation from a
crossed pair and proves that all other fiber data stay fixed.

Repeat until every B precedes every A. This is the only word in its fiber
with \(y<_L x\). The original word is reconstructed from this representative
and the \(a+1\) B positions among the \(a+b+2\) filtered positions. The
resulting injection proves the bound. It also proves the same bound
conditional on any nonempty union of whole fibers, for example a compatible
assignment of absolute outsider positions.

For sharpness, take the disjoint union of two chains of orders \(b+1\)
and \(a+1\), with \(x\) the minimum of the first chain and \(y\) the
maximum of the second. All binary shuffle words occur, with exactly one
word putting \(y\) before \(x\).

## Individual fibers are principal path intervals

For a fiber with \(m=|A|+|B|\) filtered positions, write \(j(k)\) for the
number of B letters among the first \(k\). An outsider at a fixed slot
induces lower or upper bounds on \(j(k)\) at its filtered prefix length \(k\):
a required B predecessor or A successor gives a lower bound; a required
A predecessor or B successor gives an upper bound. The all-B-first word
is coordinatewise maximal and feasible, so all upper bounds are redundant.
For letters in their fixed group order, the cross precedence
\(B_i<_P A_h\) is equivalent to \(j(i+h-1)\geq i\); there are no cross
precedences in the other direction. The restrictions therefore take the
form of lower bounds. The pointwise minimum of two unit-step prefix paths
with the same endpoints is again such a path. Hence each fiber is the
principal interval from its least feasible path to the all-B-first path.
Its exact size can be counted by a grid recurrence with \(O((a+2)(b+2))\)
arithmetic states once the prefix bounds are available; the number of
fibers itself can be large.

## Verification and scope

- PosetPairShuffle.lean proves the full cardinality inequality for
  arbitrary finite partial orders (PosetFiber.choose_bound_for_rank_extensions).
  A linear extension is an order-respecting bijection onto Fin (Fintype.card α);
  the counted subset is exactly those with \(y\) earlier than \(x\).
  The hypothesis “not \(x\leq_P y\)” slightly generalizes incomparability:
  if \(y<_P x\), the inequality is trivial. The only kernel-reported axioms
  are propext, Classical.choice and Quot.sound. The sharp example and the
  conversion of actual poset fibers into path intervals are written proofs,
  not formalized endpoints; Lean separately checks arithmetic path closure.
- Run python3 corridor.py to enumerate 2,097,034 extension incidences
  across 2,552 ordered incomparable pairs and check 1,048,517 fibers
  against literal upward-closure paths. 56,262 fibers are proper
  nonsingleton intervals. This is an exact replay, not the proof.
- Background: Peczarski's [golden partition paper](https://doi.org/10.55016/ojs/cdm.v12i1.62349)
  describes incomparable elements associated with a pair; Jaldevik and
  Snellman's [blocking ideals](https://arxiv.org/abs/2501.11073) filter
  extensions by an ideal at a cutoff; lattice path representations appear
  in [Chan, Pak and Panova](https://arxiv.org/abs/2005.08390).
  Here the decomposition freezes outsider positions in an arbitrary poset.
  The literature check is not a priority claim.
