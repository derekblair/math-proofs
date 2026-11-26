# Audit and further contraction of deterministic real 3SUM rank moments

The source is Chan–Itakura–Ma–Yu [arXiv:2610.42012v1](https://arxiv.org/html/2610.42012v1), Problem 5.6 and Lemma 5.8, combined with Majdoddin [arXiv:2610.17420v1](https://arxiv.org/html/2610.17420v1), Corollary 7.3 (geometric) or the sharper box-count analysis in EXACT-BOX-TAIL.md (entropy). Conditional on those tools, the following yields exact deterministic O(n^1.9991653) without probability of error. It is not an end-to-end kernel verification or a priority claim.

## Drop all six positional labels

Fix two requested endpoints (i,p),(j,q), an allowable row interval I and a rank moment s in {0,1,2}. Write the rank expansion as a sum over left tuple (k,k_1,...,k_s) with k∈I and right tuple (l,l_1,...,l_s) with each coordinate in [d]. The first inequality compares A[i,k]−A[i,p] to B[j,q]−B[j,l]; every other compares A[i,k_r]−A[i,k] to B[j,l]−B[j,l_r]. Convert each to a strict ordinal integer inequality (shift RHS rank by 1 for a weak inequality). The unique minimal dyadic interval separating the two ranks gives each matched tuple a unique key J=(J_0,...,J_s).

For fixed J, *all* conditions on the left tuple, including k∈I, and *all* conditions on the right tuple are independent. Let L_I((i,p),J) count left tuples whose ranks fall in the prescribed left halves; let R(J,(j,q)) count right tuples whose ranks fall in the prescribed right halves. Then the exact moment is
  sum_J L_I((i,p),J) · R(J,(j,q)).
Proof: partition all satisfying paired tuples by the unique key J, then apply the Cartesian-product size formula separately to each key. This drops k,l as well as the four already separable witness coordinates; no real value is ever hashed, rounded or converted to an integer. Weight at most d³, and ranks/comparisons/tags behave as in the independent audit of the basic reduction. The other inequality and two smaller moments use the same notation with fewer coordinates. Sort emitted integer incidences by (endpoint,J) to accumulate arbitrary multiplicities deterministically. Distinct supports, not sums of weights, control adjacency-enumeration complexity.

## Global heavy/light ledger

For s=2 left construction/support is Õ(n |I|d²), and its sum across all eligible I is Õ(nd³). The right construction/support is Õ(nd³) and wholly independent of I (clocks for strict versus weak are separate constant cases). For d=n^alpha and fixed delta, classify a key as light solely by RIGHT support degree ≤ Δ≈n/d^(3+delta). Iterate each left support record across the neighboring right support list, multiplying weights and updating only the requested entries for that I. Aggregate light work at most Δ times the total left support, hence Õ(n²/d^delta); the shared right lists need no copying for light processing. A key with zero right support disappears. Heavy width is Õ(nd³/Δ)=Õ(d^(6+delta)), *uniform* over I; unlike the earlier 8+delta proposal there is no depth-specific improvement claimed from this ledger.

For each interval whose heavy answers are requested, pad dense X=L_I and Y=R to width D=Õ(d^p) with p=6+delta. A common right matrix can be reused as input, but the data structure preprocessing is paid separately for each I. There are O(d^delta) intervals and O(n²/d) total requested entries. Fill cost Õ(n d^(p+delta)) is negligible. With deterministic preprocessing Õ(n²/D^gamma) and Õ(D^q) per query the claimed bound follows from strict p gamma>2 delta, delta+p q<1 and alpha p<R. Polynomially bounded integer edge weights fit the backend's exact model; no random dictionary is used.

## Certified constants

Run python check_weighted_exponent.py. For geometric Corollary 7.3, c=11.30, theta=.01641, delta=.06792, alpha=.012186 gives raw 1.99917232688 and O(n^1.9991724). For entropy as previously justified, c=11.21, theta=.01641, delta=.06793, alpha=.012288 gives raw 1.99916527616 and O(n^1.9991653). All strict inequalities certified as Fractions using rigorous log intervals. The smaller savings from omitting only the four witness coordinates are also checked, as controls. An end-to-end real 3SUM implementation using the selected-entry tensor theorem has not been built here.
