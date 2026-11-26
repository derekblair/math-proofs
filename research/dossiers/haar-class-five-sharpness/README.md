# Exact girth 36 for a class-five cubic Haar graph

[The Lean example](HaarClass5SharpGirth.lean) is the cubic Haar graph on two copies of the upper unitriangular 6×6 group over the field of 31 elements. Its ports are the identity and two matrices with first superdiagonal entries (14,22,19,2,14) and (28,11,15,24,13) and zero higher entries. It has a simple cycle of length 36 and no smaller cycle; its shortest simple power-of-two cycle has length 64. The ambient group has order 31¹⁵ and nilpotency class exactly five. Connectedness of the full graph is not asserted.

Together with [the class-five girth upper bound](../haar-dyadic-cycles/HaarClass5AnyPorts.lean), the example makes 36 the exact maximum girth for three distinct ports at nilpotency class at most five. It also makes 64 the exact optimal odd-order guarantee for the shortest dyadic cycle at this class. Neither assertion resolves the full Erdős–Gyárfás conjecture.

The lower bound verifies all 196,608 nonbacktracking length-17 prefixes starting at the same side and group identity. It checks injectivity for their exact matrix endpoints. A shorter even cycle supplies two distinct half-paths with the same endpoint and hence contradicts the check. Bipartiteness excludes odd cycles. The proof uses a reverse-owner table for efficient uniqueness checking; generation by Python is not trusted. Lean verifies all 768 shard obligations with kernel reduction and formally connects the packed matrix states to actual matrix multiplication and inverses.

## Replay on Linux

Use Lean 4.34.1, Python 3, sha256sum, and built mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612. Run:

    bash verify.sh /path/to/mathlib4

The script generates the large owner payload and proof obligations in a temporary directory, verifies their SHA-256 hashes, and checks each Lean source. No compiled data or downloaded certificate is used. This is a long, memory-heavy replay. Default concurrency is one; set HAAR_JOBS=2 only with enough memory.
