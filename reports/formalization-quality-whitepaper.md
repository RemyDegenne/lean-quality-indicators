# Auditing formalization quality in Lean libraries

We have run audits of formalization quality across seven major Lean corpora. **Mathlib is the clear leader on the measures studied**, with a substantial gap to Lean Pool, Anthropic’s FLT project, OpenAI’s released mathematics corpus, and—in preliminary results—AxiomMath’s CFSG. Tau Ceti sits close to Mathlib on repeated machinery, but the larger Opus sample finds more than twice Mathlib’s unnecessary-hypothesis rate. Formal Frontier is close on the theorem audits, although it falls between Mathlib and the other projects on repeated proof machinery.

These are local measures of formalization quality: unnecessary assumptions, overlap with existing results, and repeated reasoning. They provide evidence about particular aspects of library design and maintenance. They do not measure the mathematical importance, difficulty, coverage, or overall fidelity of a formalization. The findings are evaluated by AI judges; it would be good, but expensive, to test correlation with human judgements. Note that the judges can read the library, but can not compile Lean or use tools (this is necessary for cheaply auditing the large libraries).

We sample theorems or complete source files from pinned library snapshots, and give judges access to the source and relevant dependencies. The tables show **Opus 5.5 high** and **Sonnet 5.5 high**, using first passes. Rémy’s Opus unnecessary-hypothesis samples cover 1,000 theorems from each of the original five libraries. Coverage varies elsewhere. Cross-model and repeated-pass checks support the broad unnecessary-hypothesis pattern (Opus/Sonnet flag correlation is 0.86 on 1,600 shared targets) but model independence is less established for the other measures.

Each cell shows flagged / sampled, the flag rate, and a 95% interval for sampling uncertainty. A dash means no judgments. CFSG figures use its completed 30-target pilots; an expansion to 300 targets per audit is running.

## 1. Unnecessary hypotheses

This audit asks whether an argument can be deleted while leaving the rest of a theorem’s statement unchanged. It includes redundant assumptions and unnecessary typeclass instances. Weakening an assumption or generalizing the statement falls outside the rubric.

| Library | Opus | Sonnet |
|---|---:|---:|
| Mathlib | 31/1,000 · **3.1%** [2.2%, 4.4%] | 6/300 · **2.0%** [0.9%, 4.3%] |
| Tau Ceti | 68/1,000 · **6.8%** [5.4%, 8.5%] | 12/300 · **4.0%** [2.3%, 6.9%] |
| Formal Frontier | 34/1,000 · **3.4%** [2.4%, 4.7%] | 12/300 · **4.0%** [2.3%, 6.9%] |
| Lean Pool | 150/1,000 · **15.0%** [12.9%, 17.3%] | 39/300 · **13.0%** [9.7%, 17.3%] |
| Anthropic FLT | 203/1,000 · **20.3%** [17.9%, 22.9%] | 52/300 · **17.3%** [13.5%, 22.0%] |
| OpenAI Math | 17/100 · **17.0%** [10.9%, 25.5%] | 15/100 · **15.0%** [9.3%, 23.3%] |
| AxiomMath CFSG | — | 4/30 · **13.3%** [5.3%, 29.7%] |

Both models flag Tau Ceti about twice as often as Mathlib. The Opus samples give a more precise comparison: 6.8% versus 3.1%, with 95% intervals that do not overlap. Formal Frontier (3.4%) remains close to Mathlib under Opus. Tau Ceti still has substantially fewer flags than Lean Pool and Anthropic FLT. OpenAI Math has a separate 100-theorem Opus pilot; CFSG has no Opus judgments for this audit yet. Judges inspect sources but cannot compile proposed replacements. [Detailed results](https://github.com/kim-em/lean-quality-indicators/blob/b235c6613/runs/main/unnecessary-hypotheses/audit-comparison.md).

## 2. Results already available in Mathlib

This audit looks for a result already supplied by a single declaration in Mathlib, Batteries or Lean core, either directly or through an instantiation giving a one- or two-line proof. Generic logical principles applied to project-specific definitions do not qualify. The four 1,000-target Opus runs use Rémy’s earlier duplication prompt.

| Library | Opus | Sonnet |
|---|---:|---:|
| Tau Ceti | 50/1,000 · **5.0%** [3.8%, 6.5%] | 35/1,000 · **3.5%** [2.5%, 4.8%] |
| Formal Frontier | 46/1,000 · **4.6%** [3.5%, 6.1%] | 45/1,000 · **4.5%** [3.4%, 6.0%] |
| Lean Pool | 68/1,000 · **6.8%** [5.4%, 8.5%] | 58/1,000 · **5.8%** [4.5%, 7.4%] |
| Anthropic FLT | 137/1,000 · **13.7%** [11.7%, 16.0%] | 118/1,000 · **11.8%** [9.9%, 13.9%] |
| OpenAI Math | 1/100 · **1.0%** [0.2%, 5.4%] | 2/100 · **2.0%** [0.6%, 7.0%] |
| AxiomMath CFSG | — | 2/30 · **6.7%** [1.8%, 21.3%] |

Anthropic FLT stands out here with a high flag rate; the differences among the other external corpora are smaller. OpenAI Math has few duplication flags despite its higher unnecessary-hypothesis rate, illustrating that the measures capture different properties. Some flagged declarations already use their Mathlib counterpart and provide a deliberate named interface. Each finding therefore raises a question about whether that additional API earns its place. Search completeness and the project’s mathematical overlap with Mathlib also affect the rate. [Detailed results](https://github.com/kim-em/lean-quality-indicators/blob/b235c6613/runs/main/duplicates-mathlib-inclusive/audit-comparison.md).

## 3. Repeated proof machinery

This audit searches a complete file for substantial mathematical reasoning repeated across at least two proofs. A finding must propose a shared lemma and show how both proofs would use it, with an improvement in readability and maintenance. Routine calculations and thin wrappers are excluded.

| Library | Opus | Sonnet |
|---|---:|---:|
| Mathlib | — | 60/372 · **16.1%** [12.7%, 20.2%] |
| Tau Ceti | — | 64/372 · **17.2%** [13.7%, 21.4%] |
| Formal Frontier | — | 128/372 · **34.4%** [29.8%, 39.4%] |
| Lean Pool | — | 180/372 · **48.4%** [43.4%, 53.5%] |
| Anthropic FLT | — | 189/372 · **50.8%** [45.7%, 55.9%] |
| OpenAI Math | 48/100 · **48.0%** [38.5%, 57.7%] | 154/372 · **41.4%** [36.5%, 46.5%] |
| AxiomMath CFSG | — | 12/30 · **40.0%** [24.6%, 57.7%] |

The initial Sonnet flags put Mathlib and Tau Ceti together, Formal Frontier in the middle, and the remaining corpora higher. The judges are *not* asked to compile their proposals, so these flag rates only represent potential refactorings. File length and organization affect opportunities to find repetition, and compiling proposed refactorings remains an important next step. We ran a small scale pilot that checked proposed refactorings more carefully; fewer survived scrutiny at Tau Ceti relative to all the other libraries. [Detailed results](https://github.com/kim-em/lean-quality-indicators/blob/b235c6613/runs/file-quality-pilot-2026-10-21/reports/repeated-proof-machinery-comparison.md), [follow-up validation](https://github.com/kim-em/lean-quality-indicators/blob/b235c6613/runs/repeated-machinery-validation-2026-10-27/validation-report.md).
