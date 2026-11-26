# Independent audit: depth-stratified deterministic arbitrary-real 3SUM

Conditional on the cited preprint reductions/data structure, I recover the claimed O(n^1.9996227). Arithmetic is independently interval-certified; this is not an end-to-end Lean proof or a priority claim.

## Box-rate change

In [Majdoddin, arXiv:2610.17420v1](https://arxiv.org/html/2610.17420v1), §6, put L=ceil(cm), D=4^m, beta_e=binom(L,m-e)4^(L-m+e). For e1+e2=d put x=d/(2m). The standard upper and lower binomial entropy bounds and concavity of H give
  log2(beta_e1 beta_e2 / beta_0²) <= 2m b(c,x) + O(log m),
where b(c,x)=c[H((1-x)/c)-H(1/c)]/ln2 + 2x. For z∈[0,1], the derivative in c of cH(z/c) is -ln(1-z/c), bounded for fixed c>5, so rounding L/m from c incurs O(1) in the log numerator uniformly. The O(log m) term covers the lower binomial entropy bound on beta_0. Derivative of b in x is 2-log2((c-1+x)/(1-x))<0, with continuity at 1. For t=ceil(2 theta m), each ratio with d>=t is Õ(D^b(c,theta)). Sum over at most (m+1)^2 pairs.

Lemma 7.1(b) bounds boxes by (2m+1) sum over d>=t of beta'_d, with beta'_d = sum over e1+e2=d of beta_e1 beta_e2 from Lemma 6.1(b). This precedes the weaker geometric estimate used in Theorem 7.2. Thus identical preprocessing has box cost Õ(n²/D^gamma) for gamma=-b(c,theta). The Corollary 7.3 encoding and tile-fit inequalities work with this gamma in R'_c(gamma), and the query rate q remains unchanged. No new arithmetic instructions or coefficient growth are required.

## Bands

At dyadic depth j, |I|≍d/2^j; hence heavy width Õ(d^(12+delta)/2^j). For band i use P_i=12+delta-i delta/8 and eta_i=(i+1)delta/8. Group j/log2(d) into eight equal subintervals of [0,delta], permitting constant-factor boundary rounding. There are O(d^eta_i) intervals with padded width Õ(d^P_i). Aggregate light work across all intervals is Õ(n²/d^delta). Per band heavy preprocessing pays Õ(n²d^(eta_i-P_i gamma_i)); the band might receive every query, but only O(n²/d) requests exist globally, so queries pay Õ(n²d^(P_i q_i-1)). Sum a constant eight bands. Dense zero-fill is Õ(n d^max_i(P_i+eta_i)), below target. Strict width margin absorbs log padding into D<=n^epsilon for fixed epsilon<R'. Lex tags, the deterministic answer dictionary, and one extra permitted terminal dyadic level remain as in the independent prior audit.

Run python verify.py for exact Fraction intervals. The three minimum strict margins across bands exceed 1.4095e-7, 1.1028e-6, 1.3229e-5. With delta=.06222 and alpha=.006065, raw exponent is exactly 2-3773643/10^10 = 1.9996226357, allowing O(n^1.9996227).

## Exact leaf prior and comparable baselines

- Majdoddin already calls the unsplit Lemma 6.1(c) min(|U|alpha'_d,beta'_d) sum the exact leaf count and analyzes it numerically in Remark 6.2. This argument sharpens the split box bound and applies depth bands; it does not introduce exact leaf counting.
- For offline W, summing Lemma 6.1(c) over tiles and band intervals bounds order-x leaves by the minimum of total queries times D^a(x) and number of intervals times n²D^b(x), with a(x)=(H(x)+x ln4)/ln2. At the relevant crossing a increases and b decreases. Splitting at that crossing yields exactly the same global exponential envelope from this estimate; sum only logarithmically many leaf orders. Simply using the unsplit formula does not improve this worst-case guarantee. A further gain needs W structure, such as fewer occupied tiles/encodings or unequal loads which can be proved, not assumed.
- Numerical-only compare.py gets exponent about 1.99962674 for the unmodified reduction with the same entropy tail, versus ~1.99962816 with geometric tail; uniform interval accounting with the entropy tail gets about 1.99962454. These are feasible grid values, not globally optimized or certified maxima. Compare against both the closest same-tool method and the stated Chan et al. O(n^1.9998), without a priority claim.
