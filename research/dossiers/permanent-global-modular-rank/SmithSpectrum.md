# Exact sharp p-adic permanent divisibility from the full Smith spectrum
**Theorem (written proof).** Let D=diag(d_1,…,d_n) be any specified integer Smith normal form (some d may be 0). For prime p let w_i=ν_p(d_i) with ν_p(0)=∞. The minimum permanent valuation over all integer matrices with this exact Smith form equals
L_p(w)= min_{α∈N^n, |α|=n, α_i=0 if d_i=0} [Σ_i w_i α_i + Σ_i ν_p(α_i!)].
If all d_i=0 and n>0, use min empty = ∞ and per=0. n=0 has per=1, bound 0. This strictly refines the rank-mod-p-only optimum by using higher invariant powers, but is not a statement that the permanent itself is Smith invariant. The lower-bound expansion is the permanent Cauchy–Binet identity, see [equation (58)](https://par.nsf.gov/servlets/purl/10398940); the point here is sharp attainment within each specified integer Smith orbit. No priority claim is made.

## Lower bound

 write A=UDV for unimodular integer U,V. Expand per as a sum over row-index choices f from U into internal indices. Group by α_i=|f^−1(i)|. For each f, group compatible column-index choices g with these same multiplicities. Exactly ∏α_i! permutations pair rows and columns with fixed same internal labels; terms have equal weight. Thus
  per(A)=Σ_{|α|=n} (∏d_i^α_i α_i!)·C_U(α)·C_V(α),
where C_U(α)=[X^α]∏_row Σ_i U_row,i X_i; C_V(α)=[X^α]∏_col Σ_i V_i,col X_i. Terms using zero invariant factor with positive exponent vanish. Every summand has valuation at least the objective, proving inequality.

## Attainment for the prescribed Smith form

Choose minimizing α whose support is maximal among all minimizers. Its positive α_i sum to n. Assign every index j with α_j=0 to exactly one used index i, in groups of size α_i−1 (possible as the sums match). For each used i form block
  d_i·J_{α_i} + diag(0, d_{j_1},…,d_{j_{α_i−1}}).
Subtract its first row from every other row, then subtract its first column from all other columns; result diag(d_i,d_j1,…). A block sum is unimodularly equivalent by integer operations to the exact specified D (permute diagonal indexing to restore order). Its permanent expansion for a block of size m is
  Σ_{S⊆assigned-unused indices} (m−|S|)! d_i^(m−|S|) ∏_{j∈S} d_j.
The S=∅ term has the valuation charged to α_i. Every nonempty S of finite d_j is strictly higher valuation: replacing |S| copies of active α_i by one on each j∈S is a valid full α-vector with larger support (because |S|≤m−1); having smaller objective contradicts minimum, equal objective contradicts maximal support. Zero d_j terms vanish. Thus no cancellation at lowest digit in each block, giving equality in the product. Both lower formula and witness construction efficient via O(n^3) simple additive-cost dynamic programming over total multiplicity n with support tie-break; straightforward integer arithmetic. Sharper than the general rank-only result; do not identify equality for an arbitrary matrix with that Smith form.

## Modular algorithm with supplied Smith factors

 compute per(A) mod p^h in polynomial workspace with runtime poly(input quantities) · Σ_{α: cost(α)<h} ∏(α_i+1). Precompute min suffix costs DP for remaining degree n. Enumerate only feasible prefixes with at least one extendable α of cost<h; every visited prefix is prefix of an actual surviving vector, so overhead polynomial per survivor. For each, use integer mixed forward differences to get C_U (divide factorial in Z) and get (∏α_i!)·C_V directly modulo p^h (no division). Weight by D powers and sum. If no survivor output zero. Arithmetic sizes polynomial because U,D,V are provided. The earlier rank-only algorithm uses only Gaussian elimination mod p and a real correction set; prefer it where full Smith factors are impractical. No arbitrary dense integer improvement claimed.

## Exact fixed divisor without prime factorization

 gcd{per(A): SNF(A)=D} = gcd_{|α|=n} ∏ |d_i|^{α_i}α_i!, with 0^0=1. For any prime the valuation of the right gcd is the minimum above, and an exact Smith-orbit witness reaches it, independently for each prime; no single simultaneous witness is needed or claimed. Compute this G without factoring: G_0(0)=1, G_0(t>0)=0, G_i(t)=gcd_{0≤a≤t}(G_{i−1}(t−a)|d_i|^a a!). Use gcd(0,0)=0, O(n³) big-integer gcds, poly-bit products. DP works because gcd distributes over scaling and splitting by final coordinate. For example, D=diag(2,4) at p=2 has weights (1,2). The three multiplicities (2,0),(1,1),(0,2) have costs 3,3,5. The sharp exponent 3 is strictly larger than the rank-zero bound 2. The diagonal D itself attains 3 in this example.

## Reproduction and scope

Run `node permanent-smith-valuation-replay.js`. The exact replay checks 360 spectral profiles, 1,440 unimodular transformations, attainment by the block witness, and the gcd recurrence against direct multiplicity enumeration. This supplement is a written proof plus exact replay; none of its Smith-spectrum statements is formalized in Lean. The correction-row expansion in the main dossier is unchanged.
