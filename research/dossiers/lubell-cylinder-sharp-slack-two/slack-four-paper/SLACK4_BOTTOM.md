# Slack four, with a bottom member

Take positive integers t≤u and u≥2, n=t+u+4. Write w_i=1/C(n,t+i).
Among all (t,u)-families having a member T of size t, the exact best
Lubell weight is
  w_0 + (u+4) w_1 + C(u+4,2) w_2.
This is a conditional slice, not the full excess-4 problem.

Each member contains T; extras are subsets of N=u+4 sites with pairwise
unions of size at most four. If a four-set of extras exists, all extras
lie in it, and the entire Boolean cube on those four sites gives an
upper bound w0+4w1+6w2+4w3+w4. The asserted optimum is larger:
C(N,2)-6≥9, w3/w2=(t+3)/(u+2)≤5/4, and
w4/w2=(t+3)(t+4)/[(u+2)(u+1)]≤5/2, so the triple/four extras cost ≤7.5 w2.

Otherwise all singletons may be added, and only pairs and triples remain
to examine. Triples pairwise meet in at least two elements, so if there
are at least two they form a common-2-core star or lie in a 4-set top.
The same description trivially covers a single triple. Every pair may
be added independently exactly when it hits every triple.

* In a star with f distinct leaves, all 2N−3 pairs meeting its core
  qualify. The pairs missing the core must contain every leaf: N−3 more
  when f=1, one more when f=2, none for f≥3.
* In a top with f distinct triples, the six interior pairs qualify.
  An external-interior pair qualifies exactly when its interior site is
  in the intersection of all triples. Thus the count is
  6+(4−f)(N−4). For f=1,2 it equals the corresponding star count. For
  f≥3 it is bounded by the count 2N−3 of pairs meeting a core, and
  f≤4≤N−2.

Now f=1 costs at most (3N−6)w2+w3, f=2 costs (2N−2)w2+2w3,
and the remaining cases cost at most (2N−3)w2+(N−2)w3. All are strictly
less than C(N,2)w2: the respective gaps in the pair counts are
(N−3)(N−4)/2, (N−1)(N−4)/2, and (N−2)(N−3)/2; use N≥6 and w3/w2≤5/4.
Thus no triples or four-sets are optimum. All subsets of extras of size
at most two are admissible and attain the bound.

Without any bottom member a different product may be better. The
middle-block construction with (t+2)-site left threshold t+1 and
(u+2)-site right threshold one has layer counts
  (0, t+2, (t+2)(u+2)+1, u+2, 0).
This is not bounded by the bottom slice when t=u is large. The full
problem must treat the missing-bottom cases separately.
