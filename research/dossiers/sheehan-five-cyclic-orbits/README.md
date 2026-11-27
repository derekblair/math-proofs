# Sheehan conjecture for five free cyclic orbits of odd prime order

**Theorem (written proof).** Let G be a finite simple 4-regular graph with a Hamilton cycle, admitting a cyclic automorphism group of odd prime order p acting freely with five vertex orbits. Then G has a second Hamilton cycle. The last residual family below is settled more generally for every odd cyclic sheet order n≥5. No assertion is made for arbitrary composite n in the other quotient types, nor for unrestricted Sheehan.

## Quotient reduction

Under assumed uniqueness, every automorphism preserves the given Hamilton cycle. The order-p automorphism therefore rotates that cycle, and the quotient of the cycle is C5 on the five orbits. The non-Hamiltonian edges form a 2-factor whose projected multigraph F is 2-regular; odd-order semiregularity ensures no edge is reversed by its stabilizer. Quotient undirected edge labels are voltage gains with plus sign in an orientation, negative in reverse, and introducing different parallel representatives of an oriented base edge introduces different gains. Write g for the nonzero total of the oriented original C5. A quotient Hamilton cycle lifts to a single Hamilton cycle precisely when its voltage is nonzero in F_p.

Exhaustively enumerate the residual cycle partitions of 5 and label each partition by the 120 permutations of the five quotient vertices, then deduplicate by the ten rotations and reflections of the red C5. The independently checked 17 types split as follows: 4 have adjacent loops, 8 of the remaining have at least two red-parallel alternatives, 3 of the remaining have a different underlying quotient Hamilton cycle with a parallel choice, 1 is K5 without repeated base edges, and 1 is the exceptional family below. The no-input replay sheehan-five-orbit-reduction-replay.js checks the partition, the 17 types, these tags, and the K5 identity.

* Adjacent loops yield the elementary [two-rim switch](#the-adjacent-rim-switch).
* If two red-parallel choices affect different edges, either one replacement has nonzero total voltage, or each individually changes the gain by −g and doing both gives −g≠0. If the choices affect the same red edge, they give different totals.
* A different underlying quotient cycle with a parallel choice gives two distinct total gains, one nonzero.
* In the simple K5, orient unordered edges from smaller to larger. Let [w] denote the integral signed edge vector of the cycle visiting the digits of w in order and returning to its first digit. Then
  [01234] = −3[01243]+5[01324]−[01342]+3[01423]−3[01432]−4[02134].
  This is a literal integer identity, with each cycle on the right different from the left. If all right gains vanish, so does g, contradiction.

Here are the canonical representatives (write an undirected edge as its two endpoint digits, including repeated digits for loops):

| First applicable argument | Residual representatives |
|:--|:--|
| Adjacent rims | 00,11,22,33,44; 00,11,22,34,34; 00,11,23,24,34; 00,11,24,24,33 |
| Two red-parallel choices | 00,12,12,34,34; 00,12,13,24,34; 00,12,14,23,34; 00,14,14,23,23; 01,01,23,24,34; 01,02,13,24,34; 01,02,14,23,34; 01,04,12,23,34 |
| Different cycle with a parallel choice | 00,13,13,24,24; 00,13,14,23,24; 01,03,13,24,24 |
| Simple complete graph | 02,03,13,14,24 |
| Fixed family | 00,12,14,24,33 |

The only residual F is loops at vertices 0,3 and a triangle on 1,2,4. Gauge the red edges 0→1→2→3→4 to gains zero and red 4→0 to gain 1 (multiply all residues by g^-1). If the residual parallel edge 1→2 does not have gain −1, substituting it already solves the graph. It remains to prove the following fixed family.

## The adjacent-rim switch

Let G be finite simple, and C a given Hamilton cycle invariant under an automorphism α of order m≥3 acting freely on vertices. Let C have k orbits, so |V|=km and α is a rotation on C (a reflection has order at most two). Its rotation step is a multiple of k, and the orbit of each vertex comprises exactly the vertices in its index class modulo k. The C-quotient is one cyclic ordering of those k orbits (allow two projected parallel C-edges when k=2). Orient C, choose successive orbits A,B (k≥2), and denote the consecutive red edge occurrences by A_i→B_i in their circuit order, i∈Z_m. Each non-C edge with both endpoints in A has, by invariance and transitivity on A, a full edge orbit A_i A_(i+a) for some nonzero a mod m. Same for B, with parameter b. Normalize signs to 0<a,b≤m/2; equality m/2 allowed if m even. These edges are outside C.

If a=b, cut the red spokes at indices 0,a and add the two corresponding rim edges. The two red path pieces are joined at both ends, so this is a distinct Hamilton cycle. Otherwise cut at the four indices 0,a,b,a+b. They are distinct modulo m because a,b are distinct positive and a+b<m. Add the A matching (0,a),(b,a+b) and the B matching (0,b),(a,a+b). Contract each of the four remaining red paths. Label a piece by the preceding removed spoke in the oriented circuit; B_i sits on piece i and A_i on the preceding piece. On the ordered set of four cut indices, the two perfect matchings have different crossing types: exactly the gain of larger magnitude gives the opposite pairing of sorted positions. The opposite pairing is fixed by rotating the four positions and the two other pairings are interchanged. Relabeling A endpoints by the cyclic predecessor therefore leaves one pairing opposite and one adjacent. They are distinct, so on the four path pieces their union is a single 4-cycle (instead of two doubled edges). Degree-two restoration then gives a distinct Hamilton cycle. This applies to any number of orbits whenever two consecutive quotient vertices have residual loops, i.e. each has a non-C internal edge orbit.

## Fixed family and switch semantics

Use vertices (i,j) with sheet i∈Z_n and base j∈{0,1,2,3,4}; the integer position 5i+j is the order around red C. The extra edges are rim gain a in base 0, rim gain b in base 3, parallel 1→2 gain −1, and 1→4 and 2→4 gains x and y. Orient rim signs so 1≤a,b≤(n−1)/2, and initially use representatives 0≤x,y<n. In this family prove another cycle for every odd n≥5. Reflection of the red vertices r↦3−r modulo 5n sends the parameters (a,b,x,y) to (b,a,−1−y,−1−x). This preserves the red cycle and the residual 1→2 label −1, so either marking may be used.

A chart records red cut tails D indexed 0 through k−1 and a perfect matching of their 2k ports, adding the indicated residual edges. Port 2i is the tail of cut i, port 2i+1 its red successor. The seven exact charts P,Q,R,S,T,U,V are in sheehan-five-orbit-seven-charts-replay.js. Each D entry is (base, coefficient vector of 1,a,b,x,y), and the port matching is recorded as B. Every blue edge is checked formally by subtracting the integer vectors and checking its base type. This makes its existence unconditional under specialization. D positions are distinct whenever their declared strict sorted order holds.

Delete the k red edges. The remaining red circuit gives k paths, possibly a singleton when two cut edges are consecutive. Its endpoint pairing pairs port 2i+1 to 2j where j is the next cut in circular order; call it P_red. The port graph is the union of that matching and B, hence 2-regular at the distinct abstract ports. It is connected iff B∘P_red has an orbit of size k starting at port 0: the port union cycles have even length and traversal two edges at a time visits one of the two equal parity classes of exactly that component. The chart table in the replay lists every allowed order and verifies each exact orbit. Uncontracting each red path yields a single spanning circuit in G. This is a simple graph Hamilton cycle, including if some red paths are singleton: distinct abstract port pairings reconstruct their vertices exactly once; if two new edges became the same blue edge in G, both endpoints would be singleton pieces and the two pieces would form an isolated component, contradicting k≥4 and connectivity. Added edges are genuinely nonred.

## Exhaustive order inequalities (no SMT required)

In each string, digits are cut indices from left to right in increasing lifted position. At a tied sheet compare base labels. All indicated ranges imply strict distinctness of full positions. The replay independently checks the formulas and these order choices on 772,079 labels for all odd n=5 through31, but this finite regression count is not used as an infinite argument.

1. **Central intervals.** If a≤x≤n−1−a, chart P has cuts (base,sheet) (0,0),(4,x),(4,x+a),(0,a), and order 0312. Ties at x=a are harmless since base 0 precedes 4. If b≤y≤n−1−b, use reflection and apply this same rule to x'=−1−y. Otherwise henceforth choose signed representatives −a≤x≤a−1 and −b≤y≤b−1.

2. **Open side intervals.** If x is neither 0 nor −a, use Q. Its six (base, sheet) pairs are (4,0),(4,−a),(1,−a−x),(0,1−a−x),(0,1−x),(1,−x). For 1≤x≤a−1, the only possibly zero sheet near the positive end occurs at x=1, where 1−x=0; the phases −a−x and 1−a−x reduce to n−a−x and n+1−a−x, with the second at most n−a (tie only for x=1), and the two −x phases are later except the stated zero. The order is 402315 for x=1 and 023154 for x≥2. If x=−t with 1≤t≤a−1, the first negative sheets reduce to n−a, n−a+t and n+1−a+t, except that the last of these becomes zero when t=a−1. The positive sheets t and t+1 occur strictly earlier than n−a. The orders are 305412 for t=a−1 and 054123 otherwise. If y is neither −1 nor b−1, reflection brings x' into the same Q range. The signed endpoints remaining are x∈{0,−a}, y∈{−1,b−1}.

3. **Mixed endpoints.**
   * x=0,y=−1. If a≥2, use R. Its sheets are 0,−a,−a−y,−a+x−y,x−y,−y with corresponding bases 4,4,1,4,4,1. Here they reduce to 0,n−a,n+1−a,n+1−a,1,1; hence 054123 (1 may tie n−a only if a=n−1, impossible). If b≥2 instead, reflect and apply the same. The remaining a=b=1 case uses T below.
   * x=0,y=b−1. If b≥2, S's sheets are 0,1−b,1−b,1−2b,1−2b,−b at bases 3,1,3,3,1,3. After reduction 1−2b comes first after zero (since 2b≤n−1), then −b, then 1−b. At both ties base 1 precedes 3, giving 043512. If b=1, reflect to the T family a=1,x=y=−1.
   * x=−a,y=−1 is the reflection of the preceding case.
   * x=−a,y=b−1 and a≠b. Reflect first if necessary to arrange a<b. Put q=2a+b−1. If q<n, R reduces its sheets to 0,n−a,n+1−a−b,n−q,n+1−a−b,n+1−b. Since a<b and b≥2, this gives 032451; when b=a+1 the last sheet ties n−a and the base-1 cut precedes the base-4 cut. If q≥n, reflect once more: now a>b and the new q exceeds n strictly. The sheet of cut 3 is 2n−q rather than n−q, and is strictly greater than the other sheets: relative to cut 5 the difference is n−2a≥1, and relative to cut 1 the difference is n+1−a−b≥2. Then R has order 024153. In this wrap region b≥2 since b=1 would imply q=2a<n.

4. **Last small families.**
   * For a=1,x=y=−1, T reduces its sheets to (0,n−1,0,b,b+1,b+2,b+1,1). Since b≤(n−1)/2 and n≥5, even b+2 is at most n−1, tied only at n5,b2 with base 0 before base 4. The resulting order is 20734651. The case b=1,x=y=0 is its reflection.
   * For a=b=1 and (x,y)=(0,−1), T has sheets (0,n−1,0,1,1,2,2,1) and order 20473561. For (x,y)=(−1,0) they are (0,n−1,n−1,0,1,2,1,0) and order 73046521.
   * For a=b, x=−a, y=a−1, the a=1 case was covered by T above. For a≥2 and 3a≤n, the sheets of U from index 0 to 7 are (0,n+1−a,n+1−2a,n+1−3a,n+1−2a,n−a,n+1−2a,n+1−a). Sorting them gives 03462517. If 3a>n, use V instead. Its sheets are (0,n−a,n+1−2a,n−2a,2n−3a,n−2a,n−a,n+1−a), giving 03526174. In the last comparison 2n−3a≥n+1−a since 2a≤n−1, and a possible tie puts base 4 after base 1.

This proves the infinite fixed-family claim by ordinary integer comparisons. The seven-chart script is only a compact exact check of constant port matchings and the finite-order regression, not an invocation of a solver.

## The prime-three case

Here a=b=1. The following literal Hamilton cycles cover all nine pairs; the final vertex in each row is joined back to the first. Each row uses positions 0 through 14 exactly once, and its edges can be read directly from the fixed-family gains.

| (x,y) | Hamilton vertex order |
|:--|:--|
| (0,0) | 0,1,2,3,4,5,6,7,9,8,13,14,12,11,10 |
| (0,1) | 0,14,7,6,9,2,1,4,3,8,13,12,11,10,5 |
| (0,2) | 0,14,2,1,4,3,13,8,7,6,9,12,11,10,5 |
| (1,0), (1,1), (1,2) | 0,10,11,12,13,14,6,7,8,9,1,2,3,4,5 |
| (2,0) | 0,14,1,2,4,6,7,9,8,3,13,12,11,10,5 |
| (2,1) | 0,5,4,6,7,14,1,2,9,8,3,13,12,11,10 |
| (2,2) | 0,1,2,3,4,6,5,10,11,7,8,9,12,13,14 |

## Reproduction and scope

Run the three self-contained scripts with Node.js:

- `node sheehan-five-orbit-reduction-replay.js` enumerates the 17 quotient types and checks the signed $K_5$ identity.
- `node sheehan-five-orbit-seven-charts-replay.js` checks the seven exact port matchings symbolically, the constant orders by finite permutation, and a separate finite regression of 772,079 profiles. The exhaustive inequalities above, not the regression, handle all odd sheet orders at least five in the fixed family.
- `node sheehan-five-orbit-bounded-replay.js` independently constructs alternative cycles on the finite fixed-family instances of prime sheet order up to 31 and checks literal graph adjacency, degree and spanning connectivity, including the $p=3$ cases.

The full result is restricted to five free cyclic orbits of odd prime size; only the fixed family is proved for all odd sheet sizes at least five. This is not a Lean formalization or a solution of unrestricted Sheehan. [Šajna and Wagner](https://doi.org/10.1002/jgt.21838) prove a second-cycle result for quartic graphs of odd order with automorphism group of size at least $2|V|/5$. At order $5p$ that requires $2p$ automorphisms, while the present hypothesis guarantees $p$. See also [Bonvicini, Pisanski, and Žitnik](https://arxiv.org/html/2504.16205v3) for related Hamiltonicity results for quartic bicirculants. No priority claim is made.
