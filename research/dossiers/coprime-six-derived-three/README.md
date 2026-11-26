# Dyadic cycles for one-matching bi-Cayley graphs over groups with derived class at most three

Every one-matching bi-Cayley graph over a finite group of order coprime to six whose derived subgroup has nilpotency class at most three contains a simple cycle of length 4, 8, 16, 32, 64, or 128. The left and right rim steps must be nonidentity. The ambient group need not be nilpotent and the steps need not generate it.

[The formal theorem](RibbonCoprimeSixDerivedThree.lean#L16) is stronger in scope than the earlier ambient-nilpotent class-three result (#74); it uses the lower-class results from the stack rooted at #77. The claim concerns cycles in the original graph, not just in a quotient. It does not claim sharpness at 128 or resolve Erdős–Gyárfás for arbitrary graphs of minimum degree three.

The proof splits into stationary and nonstationary lower-central cases for the derived subgroup. For the stationary case, affine charts outside a finite exceptional bank are handled by at most one rim inversion. For 52 exceptional labels, the proof checks 213 representative pair configurations and 137 representative projective tangents, then transports actual cycles back along the graph symmetries. The nonstationary proof uses projected commutator order and explicit lifted cycles at the small remaining orders. Lean checks the combinatorial certificates, including closure and distinct vertices, rather than trusting a separate arithmetic program.

For the graph convention see [Zhou and Feng](https://doi.org/10.1016/j.jctb.2015.10.004). [Burkhart's theorem for Cayley graphs](https://arxiv.org/abs/2611.05060) does not assume the one-matching bi-Cayley presentation studied here and is not used as a substitute for the proof.

## Replay

Use Lean 4.34.1 and compiled Mathlib at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. From this directory run:

```sh
LEAN_BIN=/absolute/path/to/lean bash replay-local.sh /absolute/path/to/mathlib4
```

The script compiles the 361 source modules in `proof-order.txt` into a temporary directory. Mathlib imports are listed in `mathlib-imports.txt`. The final theorem's axiom report is `[propext, Classical.choice, Quot.sound]`. The Lean source itself contains the finite-check inputs. The Python search programs are not needed for replay.
