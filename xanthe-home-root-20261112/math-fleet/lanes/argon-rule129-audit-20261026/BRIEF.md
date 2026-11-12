# BRIEF — Argon High research lane: independent audit of the Rule 129 / Rule 126 proof strategy

Lane: argon-rule129-audit-20261026 · Harness: agy, model gemini-4-argon-high · Machine: xanthe · Pool: google-ai-ultra
Type: RESEARCH ONLY. No coding, no repo writes, no GitHub writes. Deliverable: DOSSIER.md in this directory, written incrementally, ending with the marker DOSSIER COMPLETE.

## Input under audit
The predecessor lane argon-rule129-screen produced DOSSIER.md (copied into this directory as SCREEN-DOSSIER.md; read it in full). Its claims to audit:
1. Mathar's conjecture A267442(n)=A043545(n) (n>0) is UNPROVED in literature and proof assistants; novelty ruling (c) first proof, with mandatory folklore disclosure (A071035 %Y, A267366 Koeppl 2022, Sloane 2015, Macfarlane 2016).
2. Exact reduction: the conjecture is logically equivalent to C_126(n,0)=A036987(n) for all n>=0, via complementation C_129 = 1 - C_126 (n>=1) and A043545 = 1 - A036987.
3. Route A proof strategy: global closed form B(n,x) = (choose(n, floor((n-|x|)/2)) mod 2 = 1) for |x|<=n, proved by one induction using Lemma A1 (f126(a,a,b)=f126(a,b,b)=f126(a,b,a)=a xor b), Lemma A3 (central choose parity via Lucas), Lemma A4 (complementation bridge).

## Your tasks
1. ADVERSARIAL AUDIT of Route A: check every induction case in Lemma A2 by hand for small n (n=0..6, all x) against direct simulation values you state explicitly in a table; flag any case split that is incomplete, any floor/parity identity that fails at a boundary (x=0, x=n, x=n+1, u even/odd boundaries), and any hidden use of truncated Nat subtraction. Verdict per lemma: SOUND / SOUND-WITH-REPAIR (give the repair) / FLAWED (give a concrete counterexample (n,x)).
2. REDUCTION AUDIT: re-derive the complementation identity and the A043545 = 1 - A036987 identity from the primary OEIS definitions quoted in SCREEN-DOSSIER.md; state whether either step assumes what it proves.
3. PIN-FREEZE READINESS: assess the DRAFT pin manifest in SCREEN-DOSSIER.md section 5 against these gates: verbatim source quotes present, strongest published form stated, exact theorem names, axiom allowlist [propext, Classical.choice, Quot.sound], trust policy forbidding native_decide/ofReduceBool/custom axioms, delta vs source = NONE. List every item that must change before a coordinator may freeze it, and any statement-file hazard (e.g. the noncomputable a036987 via Classical, the a043545 foldl definition at n=0, ecaRule testBit encoding vs Wolfram bit order).
4. End with a "What this audit does NOT show" section: an audit of a strategy sketch is not a proof and not a Lean verification.

## Rules
- Every verdict names its evidence inline (a computed table entry, a quoted line, a counterexample).
- Do not import the predecessor lane's conclusions; re-derive or recompute what you rely on.
- Research only: web/OEIS reading and reasoning.
