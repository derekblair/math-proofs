# Sharp class-three result for cubic single-matching bi-Cayley graphs

Take two copies of a group with generators a and b. On one rim add edges
g--ga, on the other g--gb, and join corresponding vertices by a matching.
This is BiCay(G,{a,a⁻¹},{b,b⁻¹},{1}), not the Haar graph with all
three edges crossing the rims. If a and b both have order greater than two
(possibly infinite), the graph is simple cubic.

`RibbonClass3.odd_class3` proves C4, C8, C16 or C32 for finite odd groups of
nilpotency class at most three, as long as a,b≠1. Lower central series LS starts
at 0=G, so LS₃=⊥ is precisely the class bound. In the genuinely class-three
port case (`[c,a]` or `[c,b]` nontrivial for c=[a⁻¹,b⁻¹]), an actual C32 is forced.

The stronger theorem RibbonClass3.involution_free_class3 has the same conclusion for all groups without elements of order two, including infinite groups. The exact C32 theorem also works in a group with involutions if the chosen triple commutator has square distinct from identity. Indeed, if c² lay in the central third lower-central layer, commuting c² with the relevant rim generator would give [c,a]²=1 or [c,b]²=1. Thus the image of c in the class-two quotient has order greater than two as needed for separation.

Two alternating 16-rim-step words have sign strings 1111001001011000 and
1111000110100100, putting one spoke after each rim step. Both close in the
class-three collector. Pass to the quotient modulo LS₂. Conjugation by the
ports detects the first two exponents, whose differences have magnitude ≤2.
Then the commutator exponent is likewise detected when the first two agree.
Every remaining potential prefix clash differs by a single copy of [c,b]
in the first template, or [c,a] in the second. Choose the template with
nontrivial obstruction. If both are trivial, the prior class-two pair theorem
applies. Ghaffari–Mostaghim already used the class-two eight-letter word in
ordinary Cayley graphs (Aequationes Mathematicae 92 (2018), §2.4,
https://link.springer.com/article/10.1007/s00010-017-0518-3). Neither that
paper nor Burkhart's ordinary Cayley result (https://arxiv.org/abs/2611.05060)
states this layered class-three bound. No absolute priority claim.

`RibbonClass3SharpGraph.sharp` and `class_exact` verify sharpness with group
UT₄(F₁₁) and first-to-last superdiagonal coordinates
a=(1,0,1,0,0,0), b=(0,1,1,0,0,0). The graph has C32 but no C4/C8/C16.
RibbonClass3SharpGraph.connected_sharp proves the same exclusions and positive C32 in the connected component of the identity. Every component has the same cycle spectrum by left translation. The proof therefore does not rely on the two generators generating the whole ambient UT₄ group.

A candidate short cycle split into two equal half-walks would require two
nonbacktracking half-words with different initial ports but the same endpoint.
The all-edge DFS checks at most 384 endpoints per start rim. The generated
bitmasks merely nominate a first-port owner, and an equality of actual
endpoints necessarily gives the same computed owner; every actual endpoint
is validated in the Lean kernel against its owner's port. There is no
trust in the Python search or a hash collision assumption. For an independent
exact DFS, use sharp_scan.py and half_scan.py.

Replay with bash replay-local.sh /path/to/built/mathlib4. Haar support comes from the sibling haar-dyadic-cycles directory of the same repository and is not duplicated. The exact predecessor source blob hashes were matched to the default branch. See CLASS-THREE-AUDIT.md for independent review.

Kernel axioms: propext, Classical.choice, Quot.sound. Recreate mask source:
`python cert_owner.py > owner-values; python gen_lean.py`.
