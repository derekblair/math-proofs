# Exact domination and zero forcing numbers of the independent-subdivision chain

This proves the two formulas conjectured in [Demonstrandum's report, Section 7](https://github.com/demonstrandum-research/artifacts/blob/main/problems/p2-factory/kills/davila-conj9/WRITEUP.md#7-extension-findings), for every k ≥ 2 in the exact independent-edge-subdivision chain studied there. The earlier Davila Conjecture 9 had already been refuted by that report; that refutation is not claimed here.

* Domination number: ⌊7k/3⌋.
* Zero forcing number: 3k+1.
* Consequence: no constant c bounds Z−γ above on connected cubic triangle-free graphs.

In Lean, see ZFChain.publishedChainConjecture and ZFChain.unboundedGap in ExactChain.lean. The vertex type uses index n=k−2 so k≥2 by construction. Each of k blocks starts as K₃,₃ with core vertices 0,1,2 and 3,4,5. Replace edge 0–3 by 0–6–3 in each block. Additionally replace edge 1–4 by 1–7–4 in each interior block. Each block except the last joins its largest port to port 6 of the next block. These labels and the bridge orientation agree with the independent-edge version of chain_study.py linked from the report. A port with no vertex (7 at an end block) is excluded from the vertex type. Reach uses the ordinary rule: a blue vertex with exactly one white neighbor can turn that neighbor blue. Applying allowed forces one at a time or all allowed forces in rounds gives the same closure: newly blue vertices only help a force unless its target is already blue.

## Proof outline

**Zero forcing lower bound.** Each isolated block has a small explicit collection of forts. A fort is a nonempty vertex set such that an outside vertex never has exactly one neighbor in it. The checked table shows any set of fewer than four vertices misses some fort. Given a successful global forcing sequence, augment the initial blue set in each block with every bridge-force target in that block. If the augmented set missed a local fort, no internal force could be the first to enter it, and no bridge force targets it. Thus every block needs at least four augmented blue vertices. At most k−1 vertices are added globally: a bridge cannot be used twice, since after one use both endpoints are blue. Therefore any forcing set has size at least 4k−(k−1)=3k+1.

**Zero forcing upper bound.** Choose vertices 0,1,3,4 in the first block and 0,1,4 in all later blocks. In the first, use forces 1→5, 0→6, 3→2. In each interior block, once its incoming port 6 is blue, use 0→5, 5→2, 2→3, 1→7. In the last, use 0→5, 1→3, 3→2 after port 6 turns blue. Once the current block is entirely blue, its outgoing port can force across the bridge. The local forcing sources are core vertices, so an external neighbor cannot invalidate any internal step.

**Domination lower bound.** Every block needs at least two selected vertices to dominate its six core vertices, which have no external neighbors. Call a block with at least three selected vertices high. The local table shows that a two-vertex selection cannot include a port; in an interior block, such a selection also leaves at least one port locally undominated. This port requires a selected port in an adjacent high block. Therefore all k−2 interior blocks are high or adjacent to a high block, so there are at least ⌈(k−2)/3⌉=⌊k/3⌋ high blocks. The total is at least 2k+⌊k/3⌋=⌊7k/3⌋.

**Domination upper bound.** Number the blocks 0,…,k−1. Declare residues 1 mod 3 high except when k≡2 mod 3, when residues 2 mod 3 are high instead. This creates exactly ⌊k/3⌋ high blocks, none at the ends, and gives every low interior block a high neighbor. High blocks choose 2,6,7. A low interior block immediately to the right of a high block chooses 1,4, leaving only its left port to the high neighbor. Other low interior blocks choose 0,3, leaving only their right port. Ends choose 0,3 and are internally dominated.

All local certificates are evaluated by Lean's kernel via decide. The general deductions, exact minima, graph degree, connectedness, and absence of triangles are Lean theorems. The independent Python check confirms valid forcing and domination witnesses through 60 blocks, with exact domination via local transfer DP.

## Reproduce

Use Lean 4.34.1 and Mathlib tag v4.34.1, commit d13f23b723b8a846827a245b89c10fc7d3f11612, with lake backed by the same Lean toolchain. In an existing checkout of that Mathlib revision, run:

    lake exe cache get Mathlib/Data/Fintype/Powerset.lean Mathlib/Tactic.lean Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean Mathlib/Combinatorics/SimpleGraph/Finite.lean
    /path/to/this/unpacked/verify.sh /path/to/mathlib4

The script copies modules to an empty temporary directory before compiling and requires both false-formula controls to be rejected. Optionally run python3 check_chain.py for the independent verification. The proof places no reliance on Python or an external solver.
