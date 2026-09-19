# INBOX — routed reading, not yet triaged into a PLAN-*.md

Items landed here from sibling-project triage. Promote into a scoped
PLAN-*.md/TODO-*.md (or discard) once read; don't let this file become
a second backlog.

---

## Routed from le-harnais triage — 2026-08-29

- **TauCeti** `***` — an AI-welcome Lean library downstream of Mathlib: AI handles
  implementation and review, humans write the statements. Fits: closest published analogue
  to leanlift's own AI-assisted Lean workflow (harness proposes, Lean kernel gates).
  https://www.linkedin.com/posts/kim-morrison-219962b_github-taucetiprojecttauceti-an-ais-welcome-share-7493109906728755205-eqom/
- **Vero** ★ — benchmark testing agents on formal verification of whole software repositories.
  Also harness-eval relevant (flag both ways). Fits: directly comparable to leanlift's
  code→Lean verification pipeline at repo scale, not just single kernels.
  https://www.linkedin.com/posts/dawn-song-51586033_github-sunblaze-ucbvero-share-7496715967276699648-ZH8a/
- **Palomar registry** — public registry/archive for formalized mathematics (noted twice,
  19 and 26 Aug). Fits: a natural discovery/publication surface for leanlift's proof output.
  https://www.linkedin.com/posts/kim-morrison-219962b_today-were-launching-the-palomar-registry-share-7495690597379538944-kXYb/
- **Lean AI formalization leaderboard** — ranks AI systems on Lean formalization tasks.
  Fits: leanlift's harness is a directly comparable entrant/benchmark target.
  https://www.linkedin.com/posts/oleg-m%C3%BCrk-5634b71_lean-ai-formalization-leaderboard-share-7496030945225887745-iZid/
- **TLA+ and automated theorem proving** ("TLA+ vs lean4 style") — model-checking style
  compared with Lean proof style. Fits: leanlift's model axis already spans PRISM/CTMC
  checking alongside Lean proof; directly relevant methodology comparison.
  https://www.linkedin.com/posts/ahelwer_tlaplus-share-7497683334643396608-paOs/
- **Verified generational GC for OCaml** (MSR RiSE blog) — a verified generational garbage
  collector. Fits: worked example of verified systems code, adjacent to leanlift's
  Rust→Lean sound-path proof lane.
  https://www.linkedin.com/posts/nikhil-swamy-11031019b_new-on-the-rise-blog-a-verified-generational-share-7497682749391056896-01iX/

## Routed from le-harnais triage — 2026-09-19 (16 Sep notes edition, §6)

- **con-leche / con-ron** `***` (de Moura / Breitner) — con-leche: an external Lean checker
  proven *in Lean* to be consistent (cannot accept a proof of False), built in under a month
  with AI after the soundness issue. con-ron: the Rust port, with **Aeneas proving the core
  Rust implementation equivalent to con-leche** — a different compiler+runtime checking the
  same thing. Fits: this is leanlift's shape exactly (Lean theorem + verified Rust checker);
  study Aeneas usage for the Rust→Lean sound-path lane.
  https://www.linkedin.com/posts/leonardo-de-moura-26a27b5_leanlang-leanprover-lean4-share-7503750589478424576-jOAJ/ ·
  https://www.linkedin.com/posts/leonardo-de-moura-26a27b5_the-lean-checker-con-leche-has-a-new-share-7505118460868218880-wbe9/
- **Hex adds nauty** `***` (Lean FRO) — full formalisation of McKay's `nauty` graph-isomorphism
  solver in the Hex computer-algebra library. Fits: worked example of formalising a hard-in-
  theory/fast-in-practice algorithm; candidate reference for the algorithm-lifting lane.
  (LinkedIn, verified; no short link recorded)
- **AxQM** `***` (arXiv 2609.05157) — textbook-scale benchmark for formal proof synthesis in a
  library of physics. Fits: an eval target beyond Mathlib-style maths; overlaps the quantum
  sibling — flag both ways.  https://arxiv.org/abs/2609.05157
- **Fermat's Last Theorem in Lean 4** ★ (Anthropic) — complete machine-checked proof on Mathlib
  (Lean 4.33.1); PROOF-PATH.md maps each step to its Lean theorem. Fits: the proof-path
  document format is a model for leanlift's proof provenance output.
  https://github.com/anthropics/fermats-last-theorem
- **MathGraph** (Sanchez) — #1 on the Lean Kernel Arena: verifies instruction-normalised Mathlib
  in 2.3 min vs 32.9 for Lean's kernel (~14×), nanoda lineage. Fits: a faster external checker
  for leanlift's verify step; compare with con-leche on trust vs speed.
  https://www.linkedin.com/posts/hesanchez_leanlang-leanprover-lean4-share-7504351921873473536-BiS1/
- **SHADOWBENCH** (Hyeon, EMNLP 2026) — reliable automatic evaluation of *semantic alignment* in
  autoformalisation: type-checks ≠ means the informal statement. Fits: leanlift's lean lane has
  no alignment metric; this is the missing gate between "Lean accepts" and "statement is right".
  https://www.linkedin.com/posts/david-hyeon-aaa81617_emnlp2026-autoformalization-formalverification-share-7500452587421151233-mR8Y/
- **VeriCodeGen** (NeurIPS 2026 workshop, Atlanta, Dec) — autoformalisation, LLM-guided proof
  search, verified refactoring, end-to-end guarantee evaluation. Fits: venue/reading list for
  the leanlift write-up.  https://vericodegen.github.io/
- **matrix-math-publish** — machine-checked ω ≤ 2.371281376990…: exact rational witness verified
  by an independent exact Rust checker *and* closed as a Lean 4 theorem. Fits: the Rust-
  checker-plus-Lean-theorem structure is leanlift's.  https://github.com/bsd-developer/matrix-math-publish
- **tzap** — Rust quantum-circuit optimiser with a Lean 4 badge (Lean-verified Rust tool).
  Fits: leanlift shape; also quantum sibling.  https://github.com/qqq-wisc/tzap
- **Hex — algebraic numbers** (Morrison) — computations in a fixed number field or arbitrary
  algebraic numbers in ℂ.  https://lnkd.in/p/gfPjPt5U
- **OpenAI Lean repos** — ten-proofs (sphere-packing / binary-code bounds), NavierStokesAndEuler
  (finite-time blow-up formalised), LongGapsBetweenPrimes. Fits: large formalisation corpora
  as regression/eval material.  https://github.com/openai/ten-proofs ·
  https://github.com/openai/NavierStokesAndEuler · https://github.com/openai/LongGapsBetweenPrimes
- **Category Theory for Software Diagnostics** (Vostokov) — book entirely AI-synthesised from his
  CT-for-debugging work; user tagged "liftlean and more". Curiosity shelf.  https://lnkd.in/p/gseP2R9B
- **Prove2Me** ★ — [title only], link unrecoverable; user to supply.
