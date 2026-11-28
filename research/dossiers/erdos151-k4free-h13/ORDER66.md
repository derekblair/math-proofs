# K₄-free Erdős #151 at orders 63–66 from the surveyed Ramsey bound

For every K₄-free graph with (63\le n\le66), the clique-transversal
bound (\tau(G)\le n-H(n)) follows from the already formalized
(H(n)=13) slice and the lower slices. The extra input is
(R(3,14)\ge67), the 2016 Kolodyazhny lower bound listed in
[Radziszowski, Small Ramsey Numbers, revision 18, Table Ia
and reference Kol2](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf).
The survey credits a personal communication and a public
author page; its underlying 66-vertex certificate was not retrieved or
replayed. The literature input is an explicit premise, not an axiom
added to Lean. A separately formalized 63-vertex witness already handles
order 63 without that premise.

The new Lean bridge transports triangle-independent guarantees from
a smaller vertex type to any larger vertex type, by restricting to
the image of an injection. A guarantee of 14 (or more) at an order
at most 66 would therefore contradict the surveyed order-66 witness.
The branches (k\le10), (k=11), (k=12), and (k=13) are dispatched
to the respective existing formal proofs. The other explicit published
inputs are the same Angeltveit upper bound (R(3,10)\le41) and Hall
locally-Petersen implications used in those proofs; their original
proofs are not replayed by this bridge.

This resolves the logical implication at all three additional orders,
not the full conjecture, order 61/62, or a new Ramsey-number bound.
