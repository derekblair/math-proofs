# Deciding additive powers at unit/expanding affine spectrum

## Exact statement

Let the images of a finite integer alphabet be closed in that alphabet. On the alphabet, assume that every letter's image length and sum are obtained by applying the same integer matrix \(M\) to \((1,x)\). Assume the starting letter is prolongable and its iterates have unbounded length. If one eigenvalue of \(M\) is \(+1\) or \(-1\) and the other has modulus greater than 1, there is a terminating Boolean procedure to determine whether the infinite prefix limit contains any additive \(p\)-power, for every supplied \(p\ge2\). This means \(p\) consecutive nonempty blocks with the same length and the same integer sum.

The exact Lean entry point is [`KNeutralExact.calculate_correct`](KNeutralExact.lean). Its natural-number argument `k` represents \(p=k+1\); its result covers occurrence at any finite position, including occurrences ending at an iterate boundary. It computes both integral eigenvectors, the finite states and edge inventory, and an explicit maximum absolute expanding stamp. Nonuniform images are allowed. [`KNeutralControl.reachable_nonuniform_cube`](KNeutralControl.lean) is a concrete cube with reachable image lengths 2, 3, and 4. The square-only procedure and examples remain available as special-case references.

## Proof structure

1. Trace the \(p+1\) cuts through letter-image offsets. Local order bits exclude inversion and enforce positive final lengths. The \(p-1\) consecutive second differences encode exact equality of the adjacent block vectors.
2. Expanding coordinates on an accepting path are bounded at every prefix by their zero terminal values. A single sign bit makes the neutral coordinates additive along each edge. Both conditions are imposed simultaneously on the same indexed path.
3. The finite path language has an effective semilinear commutative image. Edge-label addition is reduced to nonnegative integer feasibility, decided by a finite base-two carry automaton. The certificate includes exact path-language equivalence, not only soundness for finitely sampled words.

## Prior work and limits

[Currie–Mol–Rampersad–Shallit, Theorem 10 and Corollary 11](https://arxiv.org/html/2111.07857) and the [Andrade–Mol reformulation, Theorem 2.4](https://arxiv.org/html/2408.15390v2#S2.SS4), require both projected roots to be expansive. [Rao–Rosenfeld](https://www.lirmm.fr/~mrosenfeld/M114937.pdf) give an incidence-matrix criterion excluding unit-modulus eigenvalues; their general abelian Problem 5 is not settled here. The new case agrees with abelian powers on binary alphabets but not on general alphabets. The related [Box progressions paper](https://arxiv.org/abs/2605.20504) was checked for overlap. No earlier theorem with this entire branch was found in the sources checked; the dossier makes no absolute priority claim. The abstract graph/semilinear and digit-carry ingredients are established techniques (see [To](https://arxiv.org/abs/1002.1464) and [Boigelot–Wolper](https://orbi.uliege.be/bitstream/2268/18767/2/BW02-iclp.pdf)).

No claim about other spectra, general nonaffine fixed points, the minimum alphabet for avoiding additive squares, or a practical performance bound. The implementation is an exact but potentially very expensive reference procedure. Small vector-walk evaluations and an explicit Lean cube witness are not benchmarks for running the complete algorithm on nontrivial morphisms.

## Replay

Run `bash verify.sh /path/to/mathlib4` with Lean 4.34.1, Mathlib at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, and its dependency artifacts built or cached. `REPLAY-ORDER.txt` gives the standalone module order. The main theorem reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
