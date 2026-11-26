# A finite odd-order cubic Haar graph with least dyadic cycle length 128

The concrete three-port Haar graph in [HaarDerivedThree128.lean](HaarDerivedThree128.lean)
is over a finite odd-order group of derived length exactly three. It has a
simple 128-cycle and no simple 4-, 8-, 16-, 32-, or 64-cycle. Its ordinary girth is exactly 66. No universal
bound for derived length three is proved, and the full Erdős–Gyárfás conjecture
remains open.

The base group is `(F₅¹³ × F₅¹³) ⋊ C₁₃`. Its two nonidentity ports add
a lamp of separate types and shift by 1 and 4. Reduced half-word comparisons
exclude all base cycles shorter than 22. The largest check has 1,536 reduced
half-words; 48 independent Lean modules check their keys in blocks of 32. The lift is another lamp extension
over that base group, now with modulus 3. Its edge coordinates record signed
traversals of the projected two nonidentity port matchings. Conservation
recovers the signed traversals of the identity matching.

Every lifted simple cycle projects to a closed nonbacktracking walk whose
net edge counts are multiples of three. If its integral flow is nonzero,
a directed circulation cycle costs at least three traversals per edge.
If the flow is zero, use the abelian-girth bound: the nonbacktracking support
has three edge-disjoint arms of length 11, and each edge is traversed both
ways. Both cases force length at least 66. A shortest 22-cycle in the base
lifts in three rounds to a simple 66-cycle, proving exact ordinary girth.
The zero-flow inequality is
classical; see [Friedman, Izsak and Silberman](https://arxiv.org/abs/1511.03678).
The finite affine two-lamp model, its port choice, and the certified 128
witness are the concrete contribution here, not a priority claim for the
general homology-cover method.

The 128-cycle lifts a walk around two disjoint 22-cycles joined by a
10-edge bridge. It goes around the cycles in each direction and traverses
the bridge four times. Its base position and just two lamp coordinates
distinguish all 128 vertices. Two explicit commutators that do not commute
witness that the group is not metabelian.

Replay against cache-populated Mathlib at
`d13f23b723b8a846827a245b89c10fc7d3f11612`, with Lean 4.34.1:

```sh
python3 verify.py /path/to/pinned/mathlib4 -j 2
```

Independent exact Python controls: `python3 checks/base_search.py` and
`python3 checks/witness128.py`. They supplement the Lean proof.

## Exact-girth tower

[The tower theorem](HaarDerivedTower.lean) repeats the same mod-3 construction.
For every integer `k >= 0`, it gives a finite odd-order group of derived length
exactly `k + 2` and a cubic Haar graph with ordinary girth exactly `22 * 3^k`.
This is an exponential lower bound on any universal bound for power-of-two
cycle length in terms of derived length. It does not assert a power-of-two
cycle exists at every tower level; the explicit 128-cycle above is the
separately checked level `k = 1` example.
