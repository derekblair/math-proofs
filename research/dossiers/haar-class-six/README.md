# Dyadic cycles in cubic Haar graphs of class six

[HaarClass6FiniteNoThree.any_ports](HaarClass6FiniteNoThree.lean) proves that if a finite group G has nilpotency class at most six and 3 does not divide its order, then any three distinct Haar ports force a simple power-of-two cycle of length at most 64 times the order of a Sylow 2-subgroup. For odd-order G this gives a simple dyadic cycle of length at most 64. If the normalized ports generate a subgroup of exact class six, the odd-order proof gives the 64-cycle directly. The full class-six case at order divisible by 3 is not claimed.

[HaarClass6HighGirth.any_ports](HaarClass6HighGirth.lean) also handles arbitrary group order, including infinite groups: if a cubic three-port Haar graph over a group of class at most six has no even simple cycle of length 4 through 32, it has a simple 64-cycle.

The new 64-port word uses alternating walks A and B of lengths 12 and 20, followed by their reverse walks. Their values agree as B = A² modulo the fourth lower-central subgroup. The error term therefore centralizes A in class six, so the full 64-step walk closes even without a girth premise. The formal class-three projection tables and odd order force all same-side vertices to be distinct when the projected third commutator V does not cube to one. A port swap treats U instead. The high-girth result uses the same closed word, with cyclic nonbacktracking checked separately. The even-order finite extension uses the existing Sylow-2 voltage lift. This is not the full Erdős–Gyárfás conjecture.

Burkhart's [odd-order Cayley theorem](https://arxiv.org/html/2611.05060v1) is about ordinary Cayley graphs, not cubic three-port Haar graphs. Exoo and Jajcay's [nilpotent voltage bound](https://www.sciencedirect.com/science/article/pii/S0195669810001757) is a girth bound, not a dyadic-cycle conclusion. No absolute priority is asserted.

Replay with Lean 4.34.1 and built mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612:

    bash verify.sh /path/to/mathlib4
