# Public-source priority audit, 25 November 2026

These checks looked for the exact propositions, not just title matches. They were run before the
Lean work and repeated on X afterwards. No earlier claim of these resolutions was found. This is not
a claim of exhaustive priority: an uncatalogued proof, unpublished note or unindexed repository
could come first. Mathematical verification and historical priority are separate questions.

Sources checked for every row unless noted:

- Web search (Firecrawl and Exa), by conjecture number with "Written on the Wall", "Graffiti.pc" or
  "Graph Brain", and by the invariant phrases. This included site searches of x.com, MathOverflow,
  aiproofwatch, ProbXiv and Palomar.
- X full-archive search, by number, source and statement keywords.
- GitHub global code and issue search (conjecture numbers, `GraphConjectureN`, exact GBP
  right-hand-side strings), and the issues and pull requests of google-deepmind/formal-conjectures.
- The live official WOWII list (updated 19 November 2026): every WOWII row below is still `open`,
  with no comment and no counterexample link.
- The [AI Village Graffiti verification worklog](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/main/README.md),
  searched by number.
- The Palomar registry, Kuberwastaken/c5-k4 (verdicts of 26 August 2026 for WOWII and the GBP
  lower-bound sweep of 12 August 2026), txmy/ultra-mathematician, and the siddhantdubey "Codex
  Worklog" gist.
- For GBP: all issues and comments of `math1um/objects-invariants-properties`. Issue
  [#421](https://github.com/math1um/objects-invariants-properties/issues/421) is still open and
  unedited.
- About 870 connected graphs published earlier as counterexamples for other conjectures (worklog,
  gist, formal-conjectures, Kuberwastaken constructions) and the 33,030 graphs in the GBP project
  database were tested against each WOWII and GBP statement.

| Scope | Findings and limits |
| --- | --- |
| Boriboon–Kittipassorn Conjecture 4 | arXiv:2508.17569 is still at v1 and Semantic Scholar lists no citations. The paper says the case `3 ≤ d ≤ n − 3` is open. Nothing in web, GitHub, formal-conjectures, X, aiproofwatch, vibemathed, demonstrandum-research or trureturing. |
| *Automated Conjecturing III* §3.2 | Web search for the exact property string returns only the paper. The GBP database has no counterexample among its 7,891 graphs. Nothing in GitHub issues, the worklog, formal-conjectures, Palomar or X. |
| WOWII 382c, 393d, 394 | None found. Kuberwastaken marks all three as holding. The 2-domination paper of DeLaViña et al. settles 382e but not 382c. formal-conjectures #7266 and PR #7380 cover 393a–c only. |
| WOWII 392c | On 24 August 2026 an AI Village worklog entry remarked in passing that 392c fails at `n = 8` on `G?`@F{`. That graph satisfies the printed statement with equality, and Graffiti.pc tested all graphs with `n ≤ 10`. The remark was a misreading and nothing was claimed. Kuberwastaken marks 392c as holding. |
| WOWII 395a | None found. The worklog and formal-conjectures #7330 and #7337 concern 395b. |
| GBP #15, #18, #19, #29, #35, #45, #80 | None found. Kuberwastaken's sweep marks these as not violated. |
| GBP #47, #62, #64, #70, #84, #85 | Nobody has claimed these. Graphs published earlier for unrelated conjectures already violate #47, #64, #70, #84 and #85. Graphs in the GBP project's own database violate #62, #70 and #84, but the database stores no independence number for them. The claim here is the first explicit refutation and the first formal proof, not the first appearance of a violating graph. |

Not included because an earlier claim exists or the statement is unclear: WOWII 444, 422b and
425e (siddhantdubey gist, 23 July 2026); 399b (formal-conjectures #8220); 442 and 267 (AI Village
worklog); 398 (fails on `P₅` as printed, probably a transcription error); 431c (ambiguous).
