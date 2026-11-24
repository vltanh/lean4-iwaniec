# Credits

How this formalization was made, from the run log and the session transcripts.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization, named the project
  and gave its purpose: a result of lean4-morrey needs a part of the paper. From that, the main
  session set the first priority (the quasiconvexity of the Burkholder function for `1 < p < 2`)
  and chose the toolchain and the packages, those of lean4-morrey.
- **Formalization:** AI systems, in one Claude Code session (Claude Code 2.1.330, Claude Agent SDK):
  - a main session, Claude Fable 5.2, which:
    - gave the task and relayed decisions;
    - checked the composition with lean4-morrey;
    - wrote the four project documents to disk from the lead agent's text, and corrected them after their review;
  - a lead agent, Claude Opus 5.5, which ran the procedure;
  - ten sub-agents launched by the lead, all Claude Opus 5.5;
  - one more sub-agent, Claude Opus 5.5, launched by the main session to review the documents.

  There was no earlier draft.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill. The local copy used is not a git checkout, so its commit is not recorded.
- **Review:** no person has reviewed the proofs. Independent agents, each starting from the TeX source and not from the provers' notes, checked:
  - the statements against the TeX and against the cited sources;
  - the proofs against the paper;
  - the documents against the TeX, the sources on disk, the code and the literature.

## First formalization (23 November 2026)

How it was made:
- **Phase 0–2 (lead).**
  - Fetched the paper's TeX source, PDF and abstract page from arXiv, and the TeX of the cited works of Baernstein–Montgomery-Smith and Guerra.
  - Set up the project on the toolchain and the package pins of lean4-morrey, with built packages copied from lean4-morrey.
  - Wrote the inventory and the routes of the paper's proofs.
- **Phase 3.**
  - The lead stated every result with `sorry` and wrote the Challenge.
  - An independent sub-agent reviewed the statements: no statement was false; two minor fixes were applied.
  - The baseline was committed.
- **Phase 4–5.** Seven sub-agents proved the results in parallel, each against a private snapshot of the build:
  - the bridges and Lemma 3;
  - the support functions, Kinderlehrer–Stampacchia and the existence of the projection;
  - Lemma 4;
  - the periodic toolkit and Theorem 1;
  - the identities of Baernstein–Montgomery-Smith, the first assertion of Corollary 2 and the quasiconvexity for lean4-morrey;
  - the upper bound for `‖𝒮‖_p`;
  - the lower bound.

  One helper lemma was found false (a support-function lemma lacking `K.Nonempty`), with a counterexample. The main session approved the added hypothesis. No statement of the paper changed.
- **Phase 6.**
  - The lead integrated the work, ran the audit and the route check, and ran Comparator.
  - An independent sub-agent compared the proofs with the paper. It found one departure described without its label (the transference step for the norm), now labelled.
- **Phase 7.** A sub-agent did the cleanup:
  - removed an unused hypothesis of a helper;
  - merged duplicates;
  - gave Mathlib-style names to the general helpers.

  The route check still passed.
- **Phase 8–9.**
  - The lead prepared the Palomar metadata and workflows; Palomar's local checks pass.
  - The harness kept sub-agents from writing report files. So, after its hand-back, the lead returned the text of the four documents in a second hand-back, an independent sub-agent reviewed them, and the main session wrote them to disk and applied the review. The four documents:
    - [`README.md`](../../README.md);
    - [`docs/Agazzi/REPORT.md`](REPORT.md);
    - this file;
    - `NEXT.md`.
  - The repository was published on GitHub at the author's request, so that lean4-morrey can require it. No preflight was run.

Figures, from the start (23 November 2026, 19:44 CST) to the lead's first hand-back (21:25 CST), which ended the Lean work. The later work on the documents is not included. They come from `session_stats.py` on the session's transcripts:
- **Elapsed time:** 1.67 h (first event 19:44:39 CST, last 21:24:56 CST).
- **Sub-agents:**
  - 13 in the transcripts: this project's eleven (the lead and the ten it launched, all Claude Opus 5.5), and two that the main session ran for lean4-morrey in the same window (Claude Fable 5.2);
  - at most 9 running at once;
  - 5.0 h of sub-agent work in total.
- **Sub-agents' tool calls and tokens:** 882 tool calls; 1.40M output tokens, 5.13M input tokens, 133M cache reads.
- **Main session's tool calls and tokens:** 193 tool calls; 0.45M output tokens, 0.76M input tokens, 96M cache reads.
- **Model calls:**
  - Claude Fable 5.2: 186 in the main session and 133 in the two sub-agents of lean4-morrey;
  - Claude Opus 5.5: 618, all in this project's agents.

What the figures leave out or include beyond this project:
- the work after 21:25 CST: the lead's writing of the documents as text, their independent review (one more sub-agent on Claude Opus 5.5), and the main session's writing them to disk and correcting them;
- the main session's own work in the same window on lean4-morrey, and its two sub-agents there, which the figures include;
- pauses;
- cost, which was not tracked.
