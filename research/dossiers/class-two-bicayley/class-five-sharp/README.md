# Lean-certified sharp class-five witness

For two rim ports in UT6(F17), the identity-connected component of
the one-matching bi-Cayley graph has a simple C64, and has no simple
C4, C8, C16 or C32. See `Ribbon5UT.fully_verified_sharp_component`
in `Ribbon5Complete.lean`. This certifies the 64 bound is sharp for
the finite odd class-at-most-five family. The ambient UT6 group is
exact class five; the chosen pair's nonzero fifth commutator is also
checked separately. No smaller nondyadic lengths are excluded by the
headline witness statement.

For each starting rim and each possible initial port, all reduced
length-16 half-walk endpoints are classified by one exact owner
lookup. Equal keys would force a common endpoint to have two
different certified initial ports. The representation need not be
injective as a general hash function; any collision that made a
label ambiguous would cause the kernel checks to fail. A shorter
even cycle can be split into equal-length halves and extended to
length 16 with the same admissible reduced suffix. Therefore the
same certificate excludes all four lengths.

The owner assembly has 96 small Lean shards, each using `decide +kernel`
and an abstract prefix-composition lemma. The entire certificate and
final theorem were checked with Lean 4.34.1 and standard axioms.
The optional C++ check is not part of the Lean proof.

From the parent dossier, run
`RIBBON_SHARP_FULL=1 SHARP_JOBS=2 bash replay-local.sh /path/to/built/mathlib4`.
Set the second argument to the upstream Haar source directory if it is
not alongside this dossier. The full owner replay is substantially
more expensive than the theorem-only replay; keep concurrency small
on a limited VM. The nested Haar matrix files are bundled as proof
dependencies. Optional generator inputs are local synthetic data.

`Ribbon5DerivedSharp.lean` also shows the 64 bound is sharp
within the odd nilpotent family whose derived subgroup has class
at most two. In any group of class at most five, the commutator of
two derived elements lies in its fourth lower-central term and
commutes with the derived subgroup.
