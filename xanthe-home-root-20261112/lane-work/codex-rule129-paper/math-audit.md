# Mathematical convention audit

Prepared 2026-10-28 for `paper.tex`. This is an editorial audit, not a completed proof or Lean artifact.

## Exact automaton conventions

Use positions `x in Z`, times `n >= 0`, and the common single-live-cell seed `B_0(x) = S_0(x) = 1` exactly at `x = 0`. Here `B` evolves by Rule 126 and `S` by Rule 129.

- Rule 126 is zero exactly on the triples `000` and `111`; it is one on the other six triples.
- Rule 129 is one exactly on `000` and `111`; it is zero on the other six triples.
- Thus `f_129 = 1 - f_126`, and both local maps are invariant under complementing every input bit.
- Consequently, the exact reduction for these common initial data is `S_n(x) = 1 - B_n(x)` for **every `n >= 1`**. There is no alternating-time parity factor.
- At `n = 0`, both automata have the same seed, so the complementary-row identity does not hold. With complementary initial data it would hold already at time zero, but those would be different initial conditions.
- Rule 126 has zero background and support inside `[-n,n]`. Rule 129 has background one for every `n >= 1`, so its whole-line number of true cells is infinite. Any finite `count_S` must explicitly mean the count **inside the cone**. The supplied reports do not formally define their symbol `count_S`, so the paper must disclose its own convention rather than silently attribute a definition to those reports.

## OEIS domain issue

The references lane verified the OEIS entries. `A267442` has offset zero and starts with `a(0)=1`. `A043545(0)=0`. The equality can therefore only be asserted as the intended identity

`A267442(n) = A043545(n)` for `n >= 1`.

`A036987(n)` is the indicator of `n = 2^j - 1` for `j >= 0`, and `A043545(n)=1-A036987(n)`. Under the target characterization, `B_n(0)=A036987(n)` holds also at `n=0`, while `S_n(0)=1-A036987(n)` requires `n>=1`.

The references lane also found an existing OEIS conjecture of the Rule 129 identity (Mathar, January 17, 2016) and a published OEIS Rule 126 row-count formula at A071051. These must constrain the novelty wording.

## Precise lower-part union

For `n >= 1`, let `H=2^h` be the largest power of two not exceeding `n`, and put `L=n-H`. If `p=popcount(n)`, then `popcount(L)=p-1`. Define `k preceq L` to mean every binary one-bit of `k` is a one-bit of `L`, equivalently `k & L = k`.

The exact candidate union in the supplied reports is

`U(n) = union_{k preceq L} {n-2k, n-2k-1}`.

The target row assertion is `B_n(x)=1 iff |x| in U(n)`.

Elementary consequences of this definition, separate from the missing automaton-to-formula argument:

- There are `2^(p-1)` choices of `k`.
- The first and second entries have opposite parity. Within either family distinct `k` give distinct entries. Hence there are exactly `2^p` distinct entries in `U(n)`; collisions never occur.
- Its minimum is `n-2L-1 = H-L-1 >= 0`.
- Zero occurs exactly when `L=H-1`, equivalently `n=2H-1` is Mersenne. It is produced exactly once, by the second entry at `k=L`.
- In every non-Mersenne case, all elements are positive, so reflecting the candidate union gives `2^(p+1)` positions. In the Mersenne case the zero position is counted once, giving `2^(p+1)-1` positions. These become statements about actual automaton rows only once the target row assertion is established.
- At `n=2^p-1`, the lower part is `2^(p-1)-1`, all its submasks form the interval `0,...,2^(p-1)-1`, and `U(n)={0,...,n}`.
- At `T_p=3*2^(p-1)-1`, the leading power is `2^p` and the lower part is `2^(p-1)-1`; the candidate union has minimum `2^(p-1)`.

The threshold is an ordering fact: the smallest positive integer with `p` one-bits is `2^p-1`; any different such integer must have a bit at index at least `p`, and its other `p-1` bits contribute at least `2^(p-1)-1`. Thus the second-smallest is `T_p`. This also works at `p=1` with an empty lower part. The simultaneous assumptions `n>=T_p` and `n!=2^p-1` are redundant but may be retained to match the brief.

## Recommended binomial-parity roadmap

The candidate closed form is

`B_n(x) = binom(n, floor((n-|x|)/2)) mod 2` when `|x|<=n`, with zero outside the cone.

The upper index is **`n`, not `n-1`**. Already `n=2,x=0` distinguishes them: the row value is zero, `binom(2,1)=2` is even, and `binom(1,1)=1` is odd.

For `n>=1` and `|x|<=n`, put `k=floor((n-|x|)/2)`. Then `k<=floor(n/2)<H`, so the leading bit of `n` cannot occur in `k`. Lucas's theorem therefore gives

`binom(n,k) odd iff k preceq n iff k preceq L`.

By the definition of the floor, `|x|` is either `n-2k` or `n-2k-1`; this is exactly the lower-part union. At the center the candidate formula is `binom(n,floor(n/2)) mod 2`.

The real pending obligation is the identity between the nonlinear Rule 126 evolution and this binomial-parity formula, including its initial row, cone boundary, both signs of `x`, and recurrence. Rule 126 is not an additive rule, so Pascal's identity alone cannot be invoked as if the cellular update were XOR. A Lean development also needs explicit integer/natural coercions, the convention that out-of-range binomial coefficients vanish, and the `n=0` case before taking the center column.

The supplied reports mention supporting `closedform` and `recurrence` tranches but do not provide their statements or proofs. This candidate formula is consistent with their union; it must not be presented as a quoted frozen formal statement from those reports.

## Local editorial sanity check

During this audit, a direct in-memory Rule 126 evolution from the singleton seed was compared with `U(n)` for exactly `n=1,...,16`; all 16 rows agreed. The printed row counts were `3,4,7,4,8,8,15,4,8,8,16,8,16,16,31,4`. This modest new sanity check is separate from, and does not extend, the two supplied tranche reports. No Lean or proof suite was run.

## Numerical omissions in the supplied sources

- The consolidation attests completion for every `p=1,...,18` but omits the per-tier analytic-generation lists and direct-simulation ranges.
- It gives only the largest converse interval: at `p=18`, `2<=n<=512000`. It does not give the other 17 intervals.
- The threshold report explicitly enumerates the `p+1` integers with `p` one-bits drawn from indices `0,...,p`. For `p=18` these are 19 values, each below `2^19=524288`; the report's weaker bound is “<=524288.” This is not an assertion that every generation up to that ceiling was simulated.
- The threshold report states the pinned `math.comb` check was used for `n<=1000`, but does not list which comparisons or exact sample counts. Do not turn that cutoff into an exhaustive simulation interval.
- Both reports say the coordinator still needed to compile/commit/freeze the pin. The mandated front-page phrase “proof pinned and in preparation” must therefore be qualified as a brief-supplied project-status statement, not independently verified from these reports.

## Final review of `paper.tex`

Reviewed the draft after it was written on 2026-10-28. The target theorem, highest-bit/lower-part notation, Mersenne exception, positive-time complementation, cone-count convention, threshold arithmetic, and Lucas reduction are mathematically consistent. The main assertion is clearly labeled as a pending target, and the numerical evidence is distinguished from universal quantification. The OEIS index-zero discrepancy and the existing conjecture and row-count literature are disclosed.

One substantive strengthening is available in the prior-art discussion: the algebraic equivalence to the quoted A127872 formula need not remain a future obligation. For `n>=1` and `0<=k<=n`, put `m=n-k`. With out-of-range lower binomial indices interpreted as zero,

`[C(2n-1,m) - C(2n-1,m-2)] mod 2`

`= C(2n+1,m) mod 2`

`= C(n,floor(m/2)) mod 2`.

The first equality is Pascal's identity applied twice (the intervening coefficient has a factor of two); the second is the binary Lucas identity, equivalently `(1+z)^(2n+1)=(1+z)(1+z^2)^n` over the field of two elements. Therefore the quoted A127872 expression is exactly the candidate binomial formula on the right half of the row. Together with the elementary Lucas-to-submask conversion already in the roadmap, the lower-part union is an algebraic restatement of that catalogued candidate representation. This significantly limits any novelty claim about the formula itself; the pending mathematical issue remains its dynamical derivation and formalization. Recommended changes were sent to the parent; this audit does not edit `paper.tex`.

A minor precision improvement is to write “Once Target Theorem 1 is established” when introducing the conditional center-column consequence, so it explicitly includes the exceptional Mersenne clause rather than referring only to the displayed non-Mersenne support equality.
