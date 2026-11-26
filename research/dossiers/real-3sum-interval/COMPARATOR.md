# Guaranteed improvement over the unmodified accounting

This comparison is about the exponents obtained by **substitution of Majdoddin's explicit Corollary 7.3 guarantees into the term-wise ledger of Chan et al. Theorem 5.9**. It is not an algorithmic lower bound, a claim about what could be achieved by combining other tools, or a public priority claim.

Set $p=12+2\delta$ in the unmodified ledger, and write $u=\delta/p$. The three terms (terminal strips, preprocessing, queries) bound the saving per unit of width exponent by
$$
 \min\{u,\gamma-u,1/12-q-u/6\}\le
 \min\{\gamma/2,(1-12q)/14\}.
$$
Indeed the first two constraints give $2x\le\gamma$, and the first and third give $(7/6)x\le 1/12-q$. The old width constraint is $p\alpha<R_c'(\gamma)$, so the saving is at most the right-hand side times $R_c'(\gamma)$. The statement bounds all parameters of that specific comparison, not just a numerical optimizer's best point.

The admissible Corollary 7.3 switching parameter is $0<\theta<0.8$. The query exponent $q(\theta)$ is increasing on that range by differentiating the entropy expression. It already exceeds $1/12$ at $\theta=0.01$, so only the smaller values need be checked for a positive saving. In the radius denominator put
$$
 B(c)=c\ln 5-(c/2)H(1/c)-(c-1)\ln 2.
$$
Both $B(c)$ and $\gamma(c,\theta)=\theta\log_2((c-1)/4)$ rise with their parameters on the relevant domain; the monotonicity of $B$ follows from the derivative in Majdoddin's Corollary 7.3. On each rectangular parameter box, use the lower corner to bound $B(c)$, $\gamma$ (in the radius), and $q$ from below. Use the opposite corner to bound $\gamma/2$ from above. This gives an enclosure of the entire box by exact rational logarithm intervals. With $c\ge128$ use $H(1/c)\le\ln2$ and $\theta\le 0.01$ to bound the expression by
$$
 \frac{\ln(c/4)}{200c(\ln5-\tfrac32\ln2)}.
$$
This decreases on the tail and is already small enough at 128.

The exact checker covers $5\le c\le128$, $0\le\theta\le0.01$ with 324 accepted boxes after 647 total visits, and proves a saving no larger than $0.0003737$ across this full ledger family. The revised exponent certifies saving $0.0003738$ even after allowing logs. The separation is small but strict under the stated comparison. Run python3 check_old_envelope.py. Lean checks the algebraic ledger envelope and width identity in OldEnvelope.lean; the logarithm-box coverage and calculus facts are not formalized there.
