# Exact Lubell maxima for (t,u)-families at excess three

Wu–Feng's [Problem 1.3](https://arxiv.org/html/2607.07564v1#S1)
asks for the largest Lubell sum of a family satisfying
`|A ∩ B|≥t` and `|A ∪ B|≤n−u` for all pairs (including A=B).
Below is a sharp result for n=t+u+3, positive integer t,u. The
problem at arbitrary excess remains open here. Wu–Feng describe
their cylinder as a natural candidate, not a named conjecture.

Taking complements preserves the Lubell sum and swaps t and u;
assume 1≤t≤u. Write w_k=1/C(n,k). When u≥2 the exact value is
    w_t + (u+3) w_(t+1) + (u+2) w_(t+2).
When t=u=1 the Wu–Feng bound (n+1)/6 is attained by their cylinder.

## Structures and upper bound

Only levels t, t+1, t+2, t+3 occur, and at most one set in each of the
first and last levels can occur. Two different bottom sets would fail
intersection; two different top sets would fail the union bound.

If both endpoints occur, the bottom T is contained in the top V.
Every set contains T and lies in V, so the family is contained in
the cylinder with three free elements. Its Lubell sum is at most
    C = w_t+3w_(t+1)+3w_(t+2)+w_(t+3).

If only the bottom occurs, all members contain T. Outside T there
are N=u+3 points. Every singleton can occur. The pairs outside T
must be pairwise intersecting, or their unions would have 4 outside
points. A pairwise intersecting family of pairs is a star or lies in
a triangle: if two edges share a and there is an edge not through a,
its ends are the two other vertices, and no further edge can appear.
Thus its size is at most N−1 (since N≥4). A full star attains N−1,
with no constraints across singletons and pairs. This establishes
the bottom-only optimum
    L = w_t+(u+3)w_(t+1)+(u+2)w_(t+2).
The complementary top-only optimum is
    H = w_(t+3)+(t+3)w_(t+2)+(t+2)w_(t+1).

If neither endpoint occurs, the two middle layers separately are
cliques in Johnson graphs of weights t+1 and t+2, respectively:
at a fixed weight k, every distinct pair has size-k−1 intersection.
The elementary classification is that a Johnson clique either shares
a common (k−1)-set (a star), or lies in a fixed (k+1)-set (a top).
Indeed, start with X∪{a} and X∪{b}, |X|=k−1. A member outside the
star through X must contain a,b and all but one point of X. This
rules out every X∪{c} with c outside {a,b}∪X and all other non-star
members necessarily lie in X∪{a,b}. Singletons fit either bound when
their corresponding size is legal.

Thus the middle maxima separately are
  low layer ≤ max(u+3,t+2), high layer ≤ max(u+2,t+3).
If t<u, these are exactly the coefficients of L, excluding w_t.
If t=u, both bare maxima equal t+3, but they cannot occur together.
A full low star has all T∪{e} for e outside T. If a high set B omits
any member of T, pick e outside T∪B (n=2t+3>|T∪B|); this violates the
cross intersection. So every high set must contain T. A full high
top consists of all (t+2)-subsets of a fixed (t+3)-set, whose common
intersection is empty. Since t≥1 this is impossible. At least one
middle count is smaller by one, and their weighted sum is less
than max(L,H). This covers all families.

## Comparison

For t≤u, direct binomial ratios give
  (L−H)/w_(t+1) = (t+2)(u−t)(t+u+4)/((t+1)(u+1)) ≥ 0.
Also
  L−C = u w_(t+1)+(u−1)w_(t+2)−w_(t+3).
If u≥2, then w_(t+2)≤w_(t+1) and
  w_(t+3)/w_(t+2) = (t+3)/(u+1) ≤ 5/3 < u.
Hence L>C. If t=u=1, n=5 and C=1>9/10=L=H, as in the published
theorem. The displayed optimal construction and upper bound agree.

This is distinct from unweighted intersection–union product optimality.
The calculation is not a claim about other slack values, uniqueness, or
priority. The weighted clique controls are independent finite tests.

## Pinned Lean proof and replay

IU.Lubell.sharp_slack_three proves the sharp result in the original
(raw) Lubell sum for both parameter orders, positive t,u and
max(t,u) ≥ 2, including an attaining witness in the original family
model. The case t=u=1 above is already in Wu–Feng's paper, not newly
formalized here. Every new Lean source uses only standard axioms.
The inherited proof base is the sibling slack-two source archive.

Set MATHLIB_DIR to a compiled Mathlib at
d13f23b723b8a846827a245b89c10fc7d3f11612 and run ./replay.sh with
Lean 4.34.1 on PATH. LEAN_BIN can override the executable and
BASE_SOURCE_DIR the parent source directory. The independent check.py
validates the rational comparisons and uses a weighted clique
enumerator on the original graph at n≤8.
