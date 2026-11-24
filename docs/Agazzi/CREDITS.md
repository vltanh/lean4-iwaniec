# Credits

How this formalization was made, from the run log and the session transcripts.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization and named the
  project. The main session set the first priority (the quasiconvexity of the Burkholder
  function) and chose the toolchain and the package pins.
- **Formalization:** AI systems, in one Claude Code session (Claude Code 2.1.330, Claude Agent SDK):
  - a main session, Claude Fable 5.2, which:
    - gave the task and relayed decisions;
    - wrote the four project documents to disk from the lead agent's text, and corrected them after their review;
  - a lead agent, Claude Opus 5.5, which ran the procedure;
  - ten sub-agents launched by the lead, all Claude Opus 5.5;
  - one more sub-agent, Claude Opus 5.5, launched by the main session to review the documents.

  There was no earlier draft. The second round (below) was made in the same Claude Code session, by a lead agent and six sub-agents, all Claude Opus 5.5.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill. The local copy used is not a git checkout, so its commit is not recorded.
- **Review:** no person has reviewed the proofs. Independent agents, each starting from the TeX source and not from the provers' notes, checked:
  - the statements against the TeX and against the cited sources;
  - the proofs against the paper;
  - the documents against the TeX, the sources on disk, the code and the literature.

## First formalization (23 November 2026)

How it was made:
- **Phase 0–2 (lead).**
  - Fetched the paper's TeX source, PDF and abstract page from arXiv, and the TeX of the cited works of Baernstein–Montgomery-Smith and Guerra.
  - Set up the project on that toolchain and those pins, with built packages copied from an existing build.
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
  - the identities of Baernstein–Montgomery-Smith, the first assertion of Corollary 2 and quasiconvexity in the sense of `CalculusOfVariations`;
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
  - The repository was published on GitHub at the author's request. No preflight was run.

Figures, from the start (23 November 2026, 19:44 CST) to the lead's first hand-back (21:25 CST), which ended the Lean work. The later work on the documents is not included. They come from `session_stats.py` on the session's transcripts:
- **Elapsed time:** 1.67 h (first event 19:44:39 CST, last 21:24:56 CST).
- **Sub-agents:**
  - 13 in the transcripts: this project's eleven (the lead and the ten it launched, all Claude Opus 5.5), and two that the main session ran for other work in the same window (Claude Fable 5.2);
  - at most 9 running at once;
  - 5.0 h of sub-agent work in total.
- **Sub-agents' tool calls and tokens:** 882 tool calls; 1.40M output tokens, 5.13M input tokens, 133M cache reads.
- **Main session's tool calls and tokens:** 193 tool calls; 0.45M output tokens, 0.76M input tokens, 96M cache reads.
- **Model calls:**
  - Claude Fable 5.2: 186 in the main session and 133 in the two sub-agents of other work;
  - Claude Opus 5.5: 618, all in this project's agents.

What the figures leave out or include beyond this project:
- the work after 21:25 CST: the lead's writing of the documents as text, their independent review (one more sub-agent on Claude Opus 5.5), and the main session's writing them to disk and correcting them;
- the main session's own work in the same window on another project, and its two sub-agents there, which the figures include;
- pauses;
- cost, which was not tracked.

## Second round (24 November 2026)

The author asked for two changes:
- remove the departure in the upper bound `‖𝒮‖_p ≤ p* − 1`: replace the bound on the torus and transference by the planar arguments that the paper cites, those of Baernstein–Montgomery-Smith and Guerra;
- move the general code into the packages:
  - the toolkit of `Agazzi/Basic/` into lean4-calculus-of-variations;
  - the case `n = 1` of Dragičević's lower bound (from `External/Lehto/`) into lean4-harmonic-analysis;
  - the Cauchy transform that the planar argument needs into lean4-harmonic-analysis.

How it was made:
- **Lead.** The main session (Claude Opus 5.5) gave the task to a lead agent (Claude Opus 5.5). The lead:
  - read the sources of the planar argument (Baernstein–Montgomery-Smith, §1; Guerra, proofs of the corollaries labelled `cor:beurling` and `cor:beurling-lp`);
  - chose the dense class and fixed the statement of the package theorem that the project calls;
  - prepared the package clones for building, with copies of built dependencies;
  - wrote the new proof of the upper bound in [`Agazzi/Corollary2/Norm.lean`](../../Agazzi/Corollary2/Norm.lean) and the statement of remark (b) in `External/`;
  - updated the project's imports and names to the packages;
  - ran the checks, and Comparator with in-project copies of the packages;
  - wrote the documents.
- **Sub-agents.** Three, all Claude Opus 5.5, each in one package, without access to the project's build:
  - the toolkit of `Agazzi/Basic/` into lean4-calculus-of-variations, as stand-alone modules (no statement changed);
  - the case `n = 1` of Dragičević's lower bound into lean4-harmonic-analysis, next to the case `n = 2`, with a lemma shared by both;
  - the Cauchy transform on the dense class and Guerra's cut-off argument (`‖𝒮‖_p` as the best constant of `‖∂u‖_p ≤ C ‖∂̄u‖_p` on `C_c^∞`) in lean4-harmonic-analysis, in a separate worktree.

  The first two ran at the same time. The lead merged the third one's branch into the package and checked the three packages' work against the brief.
- **Follow-up 1: Guerra's dense class.** The third sub-agent's proof of remark (b) used a dense class of Schwartz functions with Fourier transform supported off `0`, for economy. The author's rule is that a departure that is not forced is a proof to rewrite, so the proof was redone along Guerra's lines, with Guerra's class `C_c^∞` and the Cauchy kernel. The lead fixed the definitions and the statements; three more sub-agents (Claude Opus 5.5) worked in parallel, each in its own worktree of lean4-harmonic-analysis:
  - the Cauchy–Pompeiu formula `C (∂̄g) = g`, by polar coordinates;
  - the smoothness, derivatives and decay of the Cauchy transform;
  - the regularity of `𝒮 g`, a Liouville lemma, and the `C_c^∞` cut-offs of Schwartz functions with `L¹` convergence of the Fourier transforms.

  The lead:
  - wrote the identity `∂ (C g) = 𝒮 g`, by Liouville's theorem;
  - wrote Guerra's cut-off step for `C g` and the density step;
  - merged the work into one commit.

  The Fourier-supported route is recorded among the package's shorter proofs.
- **Follow-up 2: the torus route as a shorter proof.** At the author's request, the bound on the torus and the transference step, removed earlier in the round, were restored from the history as an alternative proof ([`Agazzi/Corollary2/NormTorus.lean`](../../Agazzi/Corollary2/NormTorus.lean)), not used by [`corollary2_norm`](../../Agazzi/Corollary2/Norm.lean#L378).
- **Commits.** Each package has local commits of this round, not yet published. The project requires the two packages by local path until they are published and pinned.

Figures, from the start of the round (24 November 2026, 08:40 CST) to the end of the Lean work, the checks and these documents (10:19 CST), from `session_stats.py` on the transcripts of the lead and of its six sub-agents:
- **Elapsed time:** 1.65 h.
- **Sub-agents:** 6, at most 3 running at once, 1.23 h of work in total.
- **Sub-agents' tool calls and tokens:** 350 tool calls; 0.51M output tokens, 1.38M input tokens, 57M cache reads.
- **Lead's tool calls and tokens:** 238 tool calls; 0.32M output tokens, 1.70M input tokens, 91M cache reads.
- **Model calls:** Claude Opus 5.5: 229 by the lead and 320 by its sub-agents.

What the figures leave out:
- the main session's own work in this round, whose transcript also holds work on another project in the same window;
- the lead's last edits, checks and commits after 10:19 CST;
- cost, which was not tracked.

