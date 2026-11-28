# Faster directed disjoint (shortest) paths on DAGs via rectangular collision batching

Theorem (paper proof, independently audited): for each fixed k≥4 and ε>0, in the model and with the one-sided error of Cao–Qi–Wang, prescribed-terminal k-DP and real-weight k-DSP on DAGs admit expected running time
    O_k(m + n^{k−1+1/(4(k−2))+ε}).
For k=4 this is n^(25/8+ε)+input rather than n^(13/4+ε)+input; no claim for k=3 or cyclic directed graphs. The primary baseline is [Cao–Qi–Wang arXiv:2611.02154v1](https://arxiv.org/html/2611.02154v1), Theorems 4.1 / 4.7, §4.4 Proposition 4.5. Its symbolic O_k(m+n^{k−3+ω+ε}) yields k−3/4 with current all-field square bound 9/4. This is a new batching argument inside its first-collision circuit, not a new identity or reporting theorem.

## Algebraic primitive

Write A=k−2≥2 and δ=1/(4A). Use the all-field rectangular upper bound of [Amanov, van den Berg and Zuiddam, arXiv:2610.30054, Theorem 1.2 and Corollary 4.17](https://arxiv.org/html/2610.30054v1), which gives ω(A,1,1)≤A+1+1/(4A) by symmetry. Work over the fixed ground field F₂; hardwire one sufficiently large constant block rank decomposition of this rectangular tensor over F₂, with common short side B and long side B^A. Tensor-power/block recursion produces division-free formal bilinear programs for shape h^A×h by h×h, uniformly constructible in O(h^{A+1+δ+ε'}) time (round short side to a power of B), and the symmetric shapes by transposition/tensor leg permutation. This is the standard fixed-block rank-to-circuit argument: at each recursion node the constant linear combinations cost proportional to the total entries of its blocks; a rank decomposition needs at least the largest flattening size B^{A+1}; choose the base with a strict ε' slack to absorb a possible logarithmic factor. Thus the primitive uses constants from the fixed field and works by extension of scalars over the growing F_(2^q) used for identity testing. It is an exact formal polynomial identity for the derivative-based extraction. For long dimension L≥h^A, split it into ceil(L/h^A) tiles to obtain O(L h^{1+δ+ε'}) operations. Cyclic symmetry/transposition is valid for bilinear tensor rank and converts to formal division-free programs of the same order. All small h, including h=1 or 2, are covered by fixed padding or direct evaluation. Arbitrary real weights are used only in forming shortest-arc commodity masks by topological distance DP, not in this field arithmetic. Field-operation costs and any log factors are absorbed in ε as in the primary theorem.

## State and schedule

Keep the source's immutable finalized collision rows Λ_T(w;·), and accumulators for each row not yet finalized. Do NOT retain each source's full extension tensor Y_T^w at its leaf. Use the same chronological recursion on the ordered real vertices. At the split I=I₁⊔I₂, first finish I₁; then sequentially make the needed left-cohort extensions for all w∈I₁, and do the cross updates; then finish I₂. This retains causality: each prior w<v contributes exactly at its lowest split putting w on the left and v on the right. Below the invariant, every read of Λ_T(w;·) is finalized.

At one split put h=|I| (half-block dimensions O(h)), and use N=O(n) for all possible real and private vertices. Each cross update uses c_i<v, with v∈I₂, so every endpoint coordinate used by any Y_T^w in the formula is <v_r, the exclusive upper endpoint of I. Values at future endpoints ≥v_r are unnecessary. Abbreviate D=all indices <v_r, and J=I (real vertices only). If w∈I₁, every endpoint e∈D with e>w lies in J, even with private sources preceding the real order. Private sinks are after it and are handled below.

## Cohort coordinate transforms

For any fixed collision T, r=k−|T|≤k−2 is the count of outsider coordinates. For each axis i, a row for fixed w and other r−1 coordinates transforms according to the source kernel:
* e<w: copy the c=e coordinate unchanged;
* e=w: zero;
* e>w: sum over c<w and w<d≤e of value(c) X_i[c,d] N_i[d,e].
Here X is the weighted adjacency matrix and N_i the path-sum matrix of that label. The same equation holds after previous axis transforms because invalid c≥w on a still-untransformed axis stay zero, and each axis is independent, commuting with the others. If transforming on the truncated D-domain, input c and intermediate d cannot leave it, so exact restricted output equals restriction of the full transform.

Fuse all (w, other coords) as one row index, with at most h N^{r−1} rows. Mask input columns c≥w and multiply first by shared X[D,J] (inner dimension at most N). Mask intermediate columns d≤w in each row, then multiply by shared N_i[J,J]. Output only e∈J above w, reinstate copies below w, and set e=w to zero. This is a correct stacked contraction even when each row's threshold w differs, because masking is before/after the shared products. No commodity label is ever summed over by a matrix dimension except the loop over fixed T and i; the lane-specific vertex and arc masks are the original ones.

Pad the row count to L=h N^{k−3}, which is ≥h^{k−2}, and tile the long input dimension into O(N/h) blocks. Each of the O_k(1) first products costs O((N/h)L h^{1+δ+ε'}), hence O(N^{k−2}h^{1+δ+ε'}). Each second product is no larger. Forming/copying masks and tensor entries explicitly costs O_k(h N^{k−2}) per split. For r=0 just use the scalar Λ_[k](w). Reuse one extension per T at the split; release all after cross updates. This replaces the entire previous leaf kernel/transform step, not merely its arithmetic after formation of K.

After all real rows are finalized, do one extra cohort for root evaluation at private sinks: h=O(n), w ranges over all real rows, J includes all real vertices and private sinks, D all indices. Now every needed e>w lies in J and the same factorization computes final Y_T^w at the private sink endpoint tuple. This extra pass has the same total cost as the top split. No intermediate access to sink coordinates is needed while finalizing real rows.

## Collision updates

For each target pair S and source event T:
* If T=S, CQW already gives (h×h)(h×N^{k−2}). Permute dimensions to the primitive, with L=N^{k−2}. Cost O(N^{k−2}h^{1+δ+ε'}).
* Otherwise choose j∈T∖S, nonempty by |T|≥|S|=2. For each fixed tuple f of outsider coordinates except c_j, the factors P_f[v,w] and Q[w,c_j] are those of the source §4.4. Critically Q=N_j, restricted to the left rows w, independent of f. Vertically concatenate P_f into shape (h N^{k−3})×h, multiply by h×N shared Q, tile only Q's columns into O(N/h) blocks. Cost O(N^{k−2}h^{1+δ+ε'}). Scatter output with its exact tuple/label indices into the target accumulators, keeping c_i<v as before; doing the mask after summation is valid since it depends only on the destination. Zero-pad every illegal factor tuple or column outside D before forming P or Q, on both the same-event and different-event routes; do not read absent entries of Y. Those extra outputs never reach a legal c_i<v destination. The destination mask is applied only after summation.
* For |S|≥3 keep the source's direct updates, O_k(N^{k−1}) overall. They only require e<v_r and hence use the available left cohort.

Thus a recursion level costs O_k(N^{k−1}h^{δ+ε'}); summing geometrically over h≈n/2^depth gives O_k(N^{k−1+δ+ε'}). Dense indexing and masks cost at most O_k(N^{k−1} log n), absorbed. Finalized rows and accumulators occupy O_k(n^{k−1}) field cells, plus matrix multiplication workspace and current cohort; recursive temporary payloads can be freed before processing the right half. The path sums N_i can use the source's block recursion and the all-field square 9/4 upper bound, dominated for k≥4. Building the explicit formal circuit costs proportional to its size.

## Correctness and extraction

Induct on CQW's own accumulator invariant: leaves finalize Λ exactly, every split computes the exact cohort extension coordinates actually read by its cross updates, scatter retains every legal coefficient with the identical label/endpoint indexing, and each w<v update is counted once. Then the final sink cohort supplies the exact root formula. Thus the new circuit computes the identical disjoint-path polynomial over F_(2^q), with the same graph normalization and membership masks. Use CQW's Proposition 4.6 correlated extraction and topological median recursion *verbatim except circuit-size bound*. All regional subproblems are arbitrary commodity subgraphs of DAGs, which our circuit accepts; padding absent labels by private isolated trivial pairs works as in the source. Fixed k, ε and failure parameter c imply polynomial field size, and the same initial random evaluation gives failure ≤n^(−c) only on YES. Reporting never emits an invalid tuple; conditional on the nonzero initial value, extraction's randomness affects time but not correctness as in the paper. Per-level regional costs sum geometrically since exponent >2 and regions halve; normalized m contributions are absorbed by the same argument. Distinguish this from deterministic comparison-only k-DSP or any cyclic support claim.

## Verification and scope

[CohortRect.lean](CohortRect.lean) checks the scalar clipped two-factor
contraction and index stacking. It does not formalize the full algorithm
or its asymptotic proof. Use Lean 4.34.1 and Mathlib v4.34.1 with the
Mathlib and dependency build directories in LEAN_PATH.

Run `python collision_check.py` and `python check_axes.py` for exact
controls. The former compares finite circuits with direct contraction and
brute path tuples; neither substitutes for the paper runtime proof.
See the [independent audit](REVIEW.md).
