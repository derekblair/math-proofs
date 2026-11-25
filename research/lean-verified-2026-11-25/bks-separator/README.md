# A separator in overlap-two prescribed permutation packings

This is a proof of the concrete separator conjecture in item 5 of §7 of Blitvić, Kammoun, and Steingrímsson, [Permutations, Pattern Covers, Posets and Positivity, Part I](https://arxiv.org/pdf/2610.29846v1#page=47). It does not claim the requested broader classification of all patterns with separators.

Use one-based pattern letters and positions. If the overlap-two prefix is 1,a and the suffix is b,c, with 2<a<b<c−1<K−2, then for every number of prescribed copies J>2 the K-th physical position is comparable with all other positions and has an incomparable pair on each side. It is the last position of the first copy, also the second position of the next copy. The proof in fact does not need the upper gap restriction on c beyond c≤K.

The exact source theorem is `PackingSeparator.bks_section7_item5` in `SourceForm.lean`. Positions are a finite set of size K+(J−1)(K−2), identified with J*(K−2)+2 in the code. Edges are literal strict comparisons imposed by any occurrence window, using the original permutation to rank both positions. The reachability relation is its reflexive transitive closure. The Lean proof does not assume that a derived interval approximation is exact.

## Argument
Two shared points connect consecutive windows. The earlier shared right point lies below the later shared left point because a<b. The left point of each window is its minimum. The proposed separator is in the first two windows, so it compares to all vertices there directly. The shared points then give a chain from the separator into the minimum of every later window.

A rank strictly between 1 and a exists, and a rank strictly between b and c exists. At either of the first two joins, take the former rank in the next window and the latter rank in the previous window. They lie between the same two shared positions. To certify incomparability, the proof constructs two lexicographic assignments of scores to all physical positions. Each preserves every required strict window comparison. One assignment puts the first private vertex lower; the other puts it higher. The two joins give the required witnesses, below and above the separator.

## Verification
With Lean 4.34.1 on PATH and a built Mathlib v4.34.1 checkout, run:

    ./verify.sh /path/to/mathlib4

The script recompiles these project modules in a clean temporary directory, and independently replays them with leanchecker. The optional controls.py runs a separate direct finite reachability implementation and does not enter the proof.
