# Paper delivery notes

Date: 28 October 2026 (UTC). Author named in manuscript: Derek Blair.

## Delivered draft

- `paper.tex`: self-contained standard `article` source; bibliography is embedded, with no external figures or bibliography database required.
- `paper.pdf`: compiled, nine-page preliminary preprint.
- `STATUS.md`: task progress and completion record.
- `math-audit.md`, `evidence-audit.md`, `references-audit.md`: independent reviews and source limitations. Public source snapshots are in `.firecrawl/`; the targeted Brave search records are retained in `references-search-*.json`.
- `compile-final.log`, `paper.log`, `verification.txt`, `paper.txt`, and `preview-*.png`: compilation, text extraction, and layout-review artifacts.

The manuscript includes the required author block and exact preliminary-draft text in a header comment and first-page footnote, an abstract, definitions and same-seed complementation, Target Theorem 1 with the lower-part union and Mersenne exception, the middle-column consequence, a clearly labelled proof roadmap, all 18 popcount tiers, the S1–S4 threshold checks, prior-art disclosures, and references.

## Corrections required by the source audit

These departures from the brief's suggested wording are necessary for mathematical and historical accuracy:

1. **The headline identity requires positive indices.** `A267442(0)=1`, while `A043545(0)=0`. The draft consistently states `A267442(n)=A043545(n)` for `n>=1`. Rule 126's middle-column identification with `A036987` includes `n=0`; the Rule 129 complement relation does not. See [A267442](https://oeis.org/A267442), [A036987](https://oeis.org/A036987), and [A043545](https://oeis.org/A043545).
2. **The identity is already a public conjecture.** A267442 records Mathar's conjecture dated 17 January 2016. It would be false to state that the identity itself appears unpublished. The draft instead attributes it and confines the unpublished-formulation observation to the exact lower-part presentation, with substantial qualification.
3. **Further prior art limits novelty.** [A071035](https://oeis.org/A071035) identifies `A036987` as the Rule 126 center column. [A071051](https://oeis.org/A071051) records the same row-count formula in Sloane's 2014 comment, also stated in [Sloane's 2015 paper, §6.1](https://arxiv.org/html/1503.01168v1#S6.SS1). [A127872](https://oeis.org/A127872) supplies a 2017 binomial formula. Equation (20) explicitly reduces that formula to the candidate used here by Pascal and Lucas. Accordingly, the support presentation is an elementary reformulation of catalogued algebra, and mathematical novelty is not established. The limited review did not examine every linked manuscript, including Macfarlane's.
4. **The required status footnote conflicts with the reports' pin status.** The exact requested phrase “Preliminary draft — Lean formalization in progress; computational evidence complete, proof pinned and in preparation.” is retained. An adjacent first-page scope paragraph explains that “complete” refers only to recorded finite checks and that “proof pinned” is wording supplied by the brief. Both reports still list compiling/committing/freezing the pin as a next step; no frozen pin or Lean artifact was supplied or audited. The draft does not certify pin completion.
5. **The finite Rule 129 count needs a cone convention.** Its background is one at every positive generation. The draft explicitly counts Rule 129 cells only in `[-n,n]`; otherwise its live-cell count is infinite. The reports do not define `count_S` independently, so this interpretation is disclosed.

The brief's phrase “Rudin-style ECA references” does not identify a particular work. No speculative Rudin citation was inserted. Wolfram's *A New Kind of Science*, pp. 55, 269–270, and 641, supplies verified ECA context. Lucas's original 1878 article is cited using verified NUMDAM metadata and DOI `10.24033/bsmf.127`.

## Exact evidence limitations and ambiguous numbers

The two supplied reports were preserved unchanged. They are summaries, not the raw tranche scripts or outputs. The draft attributes their completion claims rather than presenting them as experiments rerun in this writing lane.

- **Original analytic row samples:** omitted for popcounts 1–17. For popcount 18, the threshold report identifies the original generation list with the 19 values `{524287-2^j : 0<=j<=18}`. Table 1 marks all omissions.
- **Converse ranges:** only popcount 18's inclusive interval `2<=n<=512000` is given. The other 17 intervals cannot be reconstructed from the packet and are explicitly marked “not supplied.”
- **Simulation ranges:** none are specified for any tier. The popcount-18 bitset section's existence and success markers do not supply its range.
- **Threshold enumeration:** for each `p=1,...,18`, exactly `p+1` selected generations with `p` set bits below `2^(p+1)` are enumerated. This is not a sweep of all integers up to that ceiling. The popcount-18 report's “19 values <=524288” is a valid loose bound; the exact list runs from `262143` to `524286` with gaps. These exact endpoints are arithmetic consequences of the reported list, not new experimental coverage.
- **`math.comb` cutoff:** `n<=1000` is attached to S1 threshold checks, not a continuous simulation sweep. Among threshold endpoints it covers `p<=9` (`T_9=767`), not `p>=10` (`T_10=1535`). The draft does not extend that claim to S3 without evidence.
- **A minor source inequality:** a higher bit gives `n>=2^(p+1)>T_p`. The source's stronger wording “exceeds `2^(p+1)`” fails at `p=1,n=4`; the manuscript uses only the correct threshold comparison.
- **Success markers:** the 18 main tier outputs have both named markers according to the consolidation, with two occurrences for popcount 18's two sections. The four support tranches are only explicitly reported to have `ALL CHECKS PASS`; the draft does not add the second marker to them.
- **No universal inference:** completion of checks at popcounts 1–18 does not establish all generations at any fixed popcount, or the all-popcount target theorem. The paper states these limits beside the theorem and in the evidence section.

A small editorial check recorded in `math-audit.md` compared the candidate union with direct Rule 126 evolution for exactly generations 1–16; all agreed. This is excluded from the paper's supplied-tranche coverage claims and is not a proof or a replacement for the original evidence.

## What awaits the proof project

- Establish the equality between the actual nonlinear Rule 126 evolution and equation (14), the binomial-parity candidate. This is the unresolved dynamical step; Lucas and counting the candidate union do not supply it.
- Supply the frozen Lean statement, declaration names, dependency/axiom audit, and successful build evidence. Match the seed, positive-time complement reduction, integer coordinates, natural binomial indices, and generation-zero case.
- Finalize **Target Theorem 1**, its name and numbering, and whether the exceptional row and center-column consequence become separate Lean-facing lemmas or corollaries. All LaTeX references already resolve; “finalize” here concerns correspondence with the eventual proof.
- Replace the evidence table's missing cells only from original tranche reports/logs. Do not infer bounds from success markers or reuse the largest interval for other tiers.
- Complete the wider prior-art assessment before claiming novelty or presenting this as a proof-bearing preprint.
- **Figures:** none included, and none are needed to compile. A future Rule 126/129 spacetime diagram could illustrate the seed and exceptional rows after its indexing is matched to the formal statement. No figure or external asset is an outstanding requirement for this draft.

## Compilation and verification

Compiled with the preinstalled `pdflatex` (pdfTeX 1.40.28, TeX Live 2025/Debian). Command, run from this directory and repeated as needed to resolve references:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error paper.tex
```

Final output is **nine pages**. The final log has **no errors, warnings, undefined references or citations, or overfull/underfull boxes**. PDF text extraction confirmed the required footnote is on page 1. All 18 table thresholds and count values were checked against their exact formulas and independently against the reports. Labels and bibliography keys were checked for resolution; the manuscript contains neither “proved” nor “proven.” All nine rendered pages were inspected for legibility, clipping, table layout, equations, and bibliography flow.

All task files were written inside this workdir. No Lean invocation, installs, or GitHub writes were performed. No claim of a completed universal proof accompanies this delivery.
