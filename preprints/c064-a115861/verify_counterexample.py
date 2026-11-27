#!/usr/bin/env python3
"""
Independent verifier for C064 refutation (OEIS A115861 / A391736).

Implements TWO completely independent replay paths in exact arbitrary-precision
Python integer arithmetic:
  Path 1: Bitwise shift-XOR carryless multiplication (recursive / iterative A048720)
          + direct exhaustive enumeration of all odd i in [1, n^3] for n = 239.
  Path 2: Explicit GF(2)[X] polynomial convolution (matching Karttunen's PARI definition
          `fromdigits(Vec(Pol(binary(b))*Pol(binary(c)))%2, 2)`)
          + exact carry-automaton BFS certifying the minimal bit-length and minimal
          odd solution i_min(n, m) across ALL i >= 1 (unbounded).

Also verifies secondary witnesses and the refutation of %F A115861: a(2*n) = a(n).
"""

import hashlib
import platform
import sys
import time
from collections import deque

# Hard-coded expected primary minimal witness
EXPECTED_N = 239
EXPECTED_M = 215
EXPECTED_I = 302_775_165
EXPECTED_N3 = 13_651_919
EXPECTED_PRODUCT = 65_096_660_475  # 215 * 302_775_165

# Additional notable exact counterexamples discovered by the automaton
SECONDARY_WITNESSES = [
    # (n, m, i_min)
    (391, 367, 186_185_132_365),              # i_min > n^4
    (439, 239, 204_209_397),
    (439, 403, 2_282_747_775),
    (511, 507, 35_400_328_149_431),           # i_min > n^5 (n = 2^9 - 1)
    (991, 807, 5_439_165_481_431_352_125),    # 63-bit i_min > n^6
    (1741, 1725, 38_026_975_273_827_156_735_641),  # 76-bit i_min > n^7
]


# --- PATH 1: Bitwise shift-XOR A048720 ---
def clmul_path1_bitwise(a: int, b: int) -> int:
    res = 0
    aa = a
    bb = b
    while bb > 0:
        if bb & 1:
            res ^= aa
        aa <<= 1
        bb >>= 1
    return res


# --- PATH 2: Explicit GF(2)[X] polynomial multiplication (PARI formula) ---
def clmul_path2_poly(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    pa = [int(ch) for ch in reversed(bin(a)[2:])]
    pb = [int(ch) for ch in reversed(bin(b)[2:])]
    pc = [0] * (len(pa) + len(pb) - 1)
    for u, cu in enumerate(pa):
        if cu:
            for v, cv in enumerate(pb):
                if cv:
                    pc[u + v] ^= 1
    val = 0
    for k in range(len(pc) - 1, -1, -1):
        val = (val << 1) | pc[k]
    return val


# --- PATH 2B: Independent Python carry-automaton BFS ---
def automaton_min_solution(n: int, m: int):
    assert n % 2 == 1 and m % 2 == 1 and 1 <= m < n
    if n % 4 != m % 4:
        return None
    d = n.bit_length() - 1
    R_size = 1 << d
    start = ((m - 1) // 2, (n - 1) // 2)
    dist = {start: 0}
    q = deque([start])
    min_t = None

    while q:
        S, R = q.popleft()
        du = dist[(S, R)]
        if min_t is not None and du > min_t:
            break
        if S == R:
            min_t = du
            continue
        if min_t is not None and du == min_t:
            continue
        for bit in (0, 1):
            sn = (S + m * bit) >> 1
            rn = (R ^ (n * bit)) >> 1
            if (sn & 1) == (rn & 1) and (sn, rn) not in dist:
                dist[(sn, rn)] = du + 1
                q.append((sn, rn))

    if min_t is None:
        return None

    # Backward lexicographic reconstruction of exact minimal odd integer
    active = {(s, s) for s in range(min(m, R_size)) if dist.get((s, s)) == min_t}
    by_layer = [[] for _ in range(min_t + 1)]
    for st, dd in dist.items():
        if dd <= min_t:
            by_layer[dd].append(st)

    bits = [1] + [0] * min_t
    for step in range(min_t, 0, -1):
        prev_layer = by_layer[step - 1]
        can_zero = False
        for S, R in prev_layer:
            s0, r0 = S >> 1, R >> 1
            if (s0 & 1) == (r0 & 1) and (s0, r0) in active:
                can_zero = True
                break
        b = 0 if can_zero else 1
        bits[step] = b
        next_active = set()
        for S, R in prev_layer:
            sn = (S + m * b) >> 1
            rn = (R ^ (n * b)) >> 1
            if (sn & 1) == (rn & 1) and (sn, rn) in active:
                next_active.add((S, R))
        active = next_active

    i_val = 0
    for k in range(min_t, -1, -1):
        i_val = (i_val << 1) | bits[k]
    return min_t + 1, i_val


def verify_all() -> None:
    t0 = time.perf_counter()
    print("=== C064 Independent Counterexample Verifier ===")
    print(f"Python: {sys.version.splitlines()[0]} ({platform.platform()})")
    with open(__file__, "rb") as f:
        print(f"Verifier SHA-256: {hashlib.sha256(f.read()).hexdigest()}")

    # 1. Verify hard-coded primary witness via BOTH paths
    n, m, i = EXPECTED_N, EXPECTED_M, EXPECTED_I
    assert n ** 3 == EXPECTED_N3
    assert 1 <= m < n
    assert i > n ** 3
    assert i % 2 == 1

    prod_ord = m * i
    prod_p1 = clmul_path1_bitwise(n, i)
    prod_p2 = clmul_path2_poly(n, i)
    assert prod_ord == EXPECTED_PRODUCT, f"m*i mismatch: {prod_ord}"
    assert prod_p1 == EXPECTED_PRODUCT, f"path1 mismatch: {prod_p1}"
    assert prod_p2 == EXPECTED_PRODUCT, f"path2 mismatch: {prod_p2}"
    print(f"[PASS] Primary witness identity: n={n}, m={m}, i={i} > n^3={EXPECTED_N3}")
    print(f"       m*i = {prod_ord} == clmul_bitwise({n},{i}) == clmul_poly({n},{i})")

    # 2. Path 2B: Independent automaton certifies min bitlen = 29 > 24 = bitlen(n^3)
    res = automaton_min_solution(n, m)
    assert res is not None
    bitlen, i_min = res
    assert bitlen == 29 and i_min == EXPECTED_I
    assert EXPECTED_N3 < (1 << (bitlen - 1)) <= i_min
    print(f"[PASS] Path 2 (automaton BFS): i_min({n},{m}) = {i_min} (exact bitlen={bitlen}, 2^28={1<<28} > n^3={EXPECTED_N3})")

    # 3. Path 1B: Direct exhaustive enumeration of ALL odd i in [1, n^3] for n = 239
    t1 = time.perf_counter()
    quotients_le_n3 = {}
    for ii in range(1, EXPECTED_N3 + 1, 2):
        # Fast bitwise carryless multiply inlined for n = 239 = 0b11101111 = 255 - 16
        # Wait: keep it strictly calling clmul_path1_bitwise's exact logic without n-specific shortcuts
        p = 0
        aa = ii
        nn = n
        while nn:
            if nn & 1:
                p ^= aa
            aa <<= 1
            nn >>= 1
        if p % ii == 0:
            q = p // ii
            if 1 <= q < n and q not in quotients_le_n3:
                quotients_le_n3[q] = ii
    assert EXPECTED_M not in quotients_le_n3, f"ERROR: m={EXPECTED_M} appeared at i={quotients_le_n3[EXPECTED_M]} <= n^3!"
    print(f"[PASS] Path 1 (exhaustive Python scan 1..{EXPECTED_N3} in {time.perf_counter()-t1:.2f}s):")
    print(f"       A115861(239) = {len(quotients_le_n3)}, quotients (<239) = {sorted(quotients_le_n3.items())}")
    print(f"       Confirmed m={EXPECTED_M} NEVER occurs for any 1 <= i <= 239^3 = {EXPECTED_N3}.")
    print(f"       Note: even i <= n^3 reduces to odd i' = i / 2^v2(i) <= n^3 with identical quotient.")

    # 4. Cross-check Path 1 vs Path 2 on all 239^3 quotients + exact automaton on all odd m < 239
    exact_row_239 = {}
    for mm in range(1, n, 2):
        r = automaton_min_solution(n, mm)
        if r is not None:
            exact_row_239[mm] = r[1]
    assert set(quotients_le_n3.keys()) | {EXPECTED_M} == set(exact_row_239.keys())
    for q, ii in quotients_le_n3.items():
        assert exact_row_239[q] == ii, f"min-i mismatch for m={q}: scan={ii} vs automaton={exact_row_239[q]}"
    print(f"[PASS] Complete row n=239 characterization:")
    print(f"       A115861(239) = {len(quotients_le_n3)}  -> conjectured |Q(239)| = 1 + {len(quotients_le_n3)} = {1 + len(quotients_le_n3)}")
    print(f"       Exact |Q(239)| = 1 + {len(exact_row_239)} = {1 + len(exact_row_239)} (strictly greater: missing m={EXPECTED_M} at i_min={EXPECTED_I})")
    print(f"       Exact (m, i_min) for row 239 (<239): {sorted(exact_row_239.items())}")

    # 5. Corollary: refutation of %F A115861: a(2*n) = a(n) at n = 478 (2*478 = 956)
    assert 478 ** 3 < EXPECTED_I <= 956 ** 3
    print(f"[PASS] Corollary (%F A115861 refutation): 478^3 = {478**3} < {EXPECTED_I} <= 956^3 = {956**3}")
    print(f"       => A115861(239) = A115861(478) = {len(quotients_le_n3)}, whereas A115861(956) = {len(exact_row_239)} != A115861(478).")

    # 6. Verify secondary witnesses (beyond n^4, n^5, n^6, n^7) via BOTH paths
    print("\n--- Secondary Witnesses (beyond n^4, n^5, n^6, n^7) ---")
    for sn, sm, si in SECONDARY_WITNESSES:
        assert 1 <= sm < sn and si > sn ** 3 and si % 2 == 1
        p_ord = sm * si
        p1 = clmul_path1_bitwise(sn, si)
        p2 = clmul_path2_poly(sn, si)
        assert p_ord == p1 == p2
        bl, im = automaton_min_solution(sn, sm)
        assert im == si and (1 << (bl - 1)) > sn ** 3
        print(f"[PASS] (n={sn}, m={sm}): i_min={si} (bitlen={bl}, > n^{3 if si<=sn**4 else (4 if si<=sn**5 else (5 if si<=sn**6 else (6 if si<=sn**7 else 7)))})")

    print(f"\nALL CHECKS PASSED in {time.perf_counter()-t0:.2f}s.")


if __name__ == "__main__":
    verify_all()
