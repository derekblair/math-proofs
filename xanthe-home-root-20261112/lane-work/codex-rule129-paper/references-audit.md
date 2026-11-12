# Reference and novelty audit

Retrieved 2026-10-28 UTC. Scope: the three requested OEIS entries, their directly relevant links, Lucas bibliography, and targeted searches for the Rule 126/129 characterization. This is a limited literature check, not a novelty certification.

## Corrections required before drafting

1. **The headline equality requires `n >= 1`.** A267442 has value 1 at index 0; A043545 has value 0 there. The OEIS conjecture itself explicitly restricts to `n > 0`.
2. **The identity is already publicly conjectured.** A267442 attributes `a(n) = A043545(n), n > 0` to R. J. Mathar on January 17, 2016. An assertion that the identity itself appears unpublished would be false.
3. **The Rule 126 count formula is prior art.** A071051 attributes the formula `2^(1+wt(n))`, less one at `n = 2^i - 1`, to N. J. A. Sloane on August 9, 2014. Sloane's 2015 paper also states it in Section 6.1.
4. **The central-column and binomial connections are already catalogued.** A071035 explicitly identifies A036987 as its central column and A127872 as its right half. A127872 includes a binomial-parity formula (below).
5. **Wolfram already discusses the qualitative center pattern.** A New Kind of Science (2002), page 641, describes Rule 129's center column in terms of powers of two; its drawing uses a row convention that must be reconciled with zero-based generation indices before translating that wording. Pages 269–270 discuss the Rule 126 / Rule 90 connection.

Recommended novelty language: the submask/Lucas mechanism is folklore-grade; the exact lower-part support formulation may be a useful explicit reformulation, and a complete checked derivation of the stated OEIS conjecture is the intended contribution. The identity, count formula, and qualitative middle-column pattern are not new statements. No proof or machine-checked artifact was located by this limited review, which does not establish their absence elsewhere.

## Requested OEIS entries

| Entry | Definition / indexing | Relevant material |
|---|---|---|
| [A267442](https://oeis.org/A267442) | Middle cell of Rule 129 from a single ON seed. Offset 0. Starts `1,0,1,0,1,1,1,0,...`. Author Robert Price, January 15, 2016. | Mathar's January 17, 2016 conjecture is restricted to positive `n`. Links a table for `n = 0..1000`; table length is not a proof. Internal revision header: `#13 Feb 16 2025 08:33:29`. |
| [A036987](https://oeis.org/A036987) | Fredholm–Rueppel sequence. Offset `0,1` (first index 0). Indicator of `n = 2^m - 1`, `m >= 0`; includes `n=0`. Starts `1,1,0,1,0,0,0,1,...`. | Records `a(n)=1-A043545(n)` attributed to Michael Somos, August 25, 2003. Recurrence `a(0)=1`, `a(n)=a(floor(n/2))*(n mod 2)` for positive `n`. Internal revision `#249 Oct 20 2026 10:37:15`. |
| [A043545](https://oeis.org/A043545) | Maximum minus minimum binary digit, using the ordinary expansion without leading zeros and representation `0` at zero. Offset `0,1`. Starts `0,0,1,0,1,1,1,0,...`. | Equals `1-A036987(n)` (Somos, August 25, 2003), or the indicator that `n` is not `2^m-1`. Paul Barry's June 7, 2006 formula uses parity of `binomial(n,floor(n/2))`. Internal revision `#55 Feb 24 2026 22:58:49`. |

Fetched internal pages are saved under `.firecrawl/oeis.org-A267442-internal.md`, `.firecrawl/oeis.org-A036987-internal.md`, and `.firecrawl/oeis.org-A043545-internal.md`.

The correct desired statements, pending the manuscript's derivation, are:

`Rule126(n,0) = A036987(n)` for `n >= 0`;

`Rule129(n,0) = 1 - A036987(n) = A043545(n)` for `n >= 1`;

`Rule129(0,0) = 1` must be handled separately. A267442 and A043545 are equal on positive indices, not identical as zero-indexed sequences.

## Additional OEIS and paper prior art

- [A071051](https://oeis.org/A071051), started by Hans Havermann, May 26, 2002, counts ON cells in the Rule 126 row. Sloane's August 9, 2014 formula is exactly `2^(wt(n)+1)-A036987(n)`. The entry links [N. J. A. Sloane, On the Number of ON Cells in Cellular Automata](https://arxiv.org/abs/1503.01168), submitted March 4, 2015; its [Section 6.1](https://arxiv.org/html/1503.01168v1#S6.SS1) states the Rule 126 formula. The manuscript should cite this directly when discussing novelty of the count corollary. Local files: `.firecrawl/oeis.org-A071051-internal.md`, `.firecrawl/arxiv.org-abs-1503.01168.md`, `.firecrawl/arxiv.org-html-1503.01168v1.md`.
- [A071035](https://oeis.org/A071035), Rule 126 triangle, rows of length `2n+1`, author Hans Havermann, May 26, 2002. Its cross-references identify A036987 as the central column and A127872 as the right half. Internal revision `#38 Feb 16 2025 08:32:46`. Local file `.firecrawl/oeis.org-A071035-internal.md`.
- [A127872](https://oeis.org/A127872), author Philippe Deléham, April 5, 2007, is a triangle obtained by reducing A039599 modulo 2. Mathematica code attributed to G. C. Greubel, April 18, 2017, gives, for `0 <= k <= n` and `n > 0`, `T(n,k) = (binomial(2n-1,n-k)-binomial(2n-1,n-k-2)) mod 2`, with `T(0,0)=1`. This is a catalogued binomial-parity formula for the right half identified by A071035; the entry does not supply a proof of the cellular-automaton connection. Local file `.firecrawl/oeis.org-A127872-internal.md`.

A071051 also links A. J. Macfarlane's PostScript manuscript, *Generating functions for integer sequences defined by the evolution of cellular automata...*. That document was not reviewed in this limited check; no novelty claim should assume it has been ruled out.

## Lucas sources

Two primary-source bibliography choices were verified:

1. Édouard Lucas, *Sur les congruences des nombres eulériens et des coefficients différentiels des fonctions trigonométriques suivant un module premier*, **Bulletin de la Société Mathématique de France 6** (1878), 49–54. DOI [10.24033/bsmf.127](https://doi.org/10.24033/bsmf.127). Bibliographic metadata directly verified at [NUMDAM](https://www.numdam.org/item/BSMF_1878__6__49_1/), saved as `.firecrawl/numdam-Lucas1878.md`.
2. Édouard Lucas, *Théorie des fonctions numériques simplement périodiques* (continued), **American Journal of Mathematics 1**, no. 3 (1878), 197–240. DOI [10.2307/2369311](https://doi.org/10.2307/2369311). Metadata verified at [JSTOR](https://www.jstor.org/stable/2369311), saved as `.firecrawl/jstor.org-stable-2369311.md`.

Romeo Meštrović's [2014 survey](https://arxiv.org/abs/1409.3820), *Lucas' theorem: its generalizations, extensions and applications (1878–2014)*, identifies the first source for Lucas's theorem and says the second states the result in Section XXI, pages 229–230, without proof. This is useful historical corroboration; do not describe the AJM passage itself as containing the original proof. Survey HTML saved as `.firecrawl/arxiv.org-html-1409.3820v1.md`.

The established binary specialization is `binomial(a,b) mod 2 = 1` exactly when every set bit of `b` is a set bit of `a`, for nonnegative `a,b` with the conventional zero extension outside `b <= a`.

## Wolfram sources

Stephen Wolfram, *A New Kind of Science*, Wolfram Media, 2002:

- [Page 55](https://www.wolframscience.com/nks/p55--more-cellular-automata/): all elementary rules from a single black cell, with Rules 126 and 129 mentioned as related by black/white interchange. Appropriate basic ECA reference.
- [Page 269](https://www.wolframscience.com/nks/p269--special-initial-conditions/) and [page 270](https://www.wolframscience.com/nks/p270--special-initial-conditions/): Rule 126 can emulate Rule 90 in blocks under suitable initial conditions, explaining the nested pattern from simple starts.
- [Page 641](https://www.wolframscience.com/nks/p641--computations-in-cellular-automata/): Rule 129 center-column zero/white positions described in terms of powers of 2. Cite as a prior qualitative observation; use the manuscript's own zero-based `n=2^m-1` convention explicitly.

All four pages were fetched and saved as `.firecrawl/wolframscience.com-nks-p*.md`. The phrase “Rudin-style ECA references” in the brief is not a specific bibliographic identifier. No speculative Rudin attribution was introduced; Wolfram supplies the requested ECA source.

## Search method and limitations

All searches used the installed Brave `bx` CLI. Known pages were read with the installed Firecrawl CLI. No software was installed and no GitHub content was written. Source caches and search results are confined to this workdir.

Saved searches:

- `references-search-oeis.json`: `OEIS A267442 A036987 A043545 Rule 129`.
- `references-search-novelty.json`: `"A267442" proof OR "Rule 129" "middle column"`.
- `references-search-support.json`: `"Rule 126" "submask" OR "binomial"` (noisy results; not used as positive evidence).
- `references-search-support-web.json`: raw ranked search for `"rule 126" binomial`.
- `references-search-submask-web.json`: raw ranked search for `"rule 126" submask`.
- `references-search-lucas.json`, `references-search-lucas-primary.json`, `references-search-wolfram.json`: targeted bibliography / Wolfram searches.

The novelty search surfaced the owner's current public `math-proofs` issue; it is not independent prior art and its additional computational range was not imported into this draft's two-report evidence record. Search results did not locate a separate explicit lower-part submask-support theorem, but search absence is weak evidence. This review is not a full literature search and did not review Macfarlane's linked manuscript or all linked triangle formulas. Therefore a blanket claim that the characterization or identity is unpublished is unsupported.

An initial guessed arXiv HTML URL for `1503.01168v2` returned a no-document page; the abstract page established that the available version is v1, which was then successfully read. That unsuccessful scrape is retained only as retrieval history, not as evidence about the paper.

## Review of the drafted paper.tex

Reviewed the initial complete manuscript on 2026-10-28 UTC. The OEIS offsets, 2016 conjecture attribution, 2014 row-count attribution, Sloane Section 6.1 citation, Lucas metadata, and Wolfram page references all agree with the inspected sources. The manuscript appropriately explains the `n=0` failure and does not claim a completed main proof.

Two recommended refinements were sent to the drafting agent:

1. The assertion that A127872 is the right half of Rule 126 is explicitly made in **A071035**, while A127872 itself is defined as a triangle modulo 2. Cite both entries for that connection, and describe the relation as catalogued rather than suggesting A127872 itself names Rule 126.
2. The equivalence between the Greubel formula and the manuscript's candidate closed form is already immediate from standard identities; there is no need to leave this comparison unresolved. With `t=n-k`, `n>0`, and `0<=k<=n`, modulo two one has

   `C(2n-1,t)-C(2n-1,t-2) = C(2n+1,t) = C(n,floor(t/2))`.

   The first congruence follows from `(1+z)^(2n-1)*(1+z^2)=(1+z)^(2n+1)` over `F_2`; the second is Lucas's theorem, since the least significant bit of `2n+1` is 1. This is exactly the candidate formula at absolute coordinate `k`. Consequently the lower-part submask union is an algebraic recoding of a catalogued right-half formula. The outstanding obligation is the derivation from the cellular-automaton dynamics and its formal verification, not this algebraic comparison.

Suggested cautious phrasing: “We did not locate this particular lower-part notation in the limited sources examined; its support formula is algebraically equivalent to a binomial formula already catalogued in OEIS.” The draft's existing qualified “appears unpublished” sentence is less precise and could obscure this equivalence. No source checked certifies absence of an existing complete derivation.
