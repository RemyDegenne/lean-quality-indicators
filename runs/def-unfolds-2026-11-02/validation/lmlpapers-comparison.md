# Source backend against the ilean reference: LMLPapers (local build)

Reference: `runs/def-unfolds-2026-11-02/validation/lmlpapers-ilean` (ilean). Compared: `runs/def-unfolds-2026-11-02/validation/lmlpapers-source` (source).

23 files whose build index does not match the source are left out on both sides.

## Definitions

- found by both: 1,659
- only in the reference: 0
- only in the compared output: 0

## Explicit unfoldings (definitions found by both)

| Category | Scope | Reference | Compared | Matched | Precision | Recall |
|---|---|---:|---:|---:|---:|---:|
| unfold | all | 296 | 296 | 296 | 100.0% | 100.0% |
| unfold | outside file | 42 | 42 | 42 | 100.0% | 100.0% |
| unfold | outside directory | 6 | 6 | 6 | 100.0% | 100.0% |
| simp | all | 407 | 406 | 406 | 100.0% | 99.8% |
| simp | outside file | 65 | 65 | 65 | 100.0% | 100.0% |
| simp | outside directory | 11 | 11 | 11 | 100.0% | 100.0% |
| rw | all | 251 | 249 | 249 | 100.0% | 99.2% |
| rw | outside file | 51 | 51 | 51 | 100.0% | 100.0% |
| rw | outside directory | 9 | 9 | 9 | 100.0% | 100.0% |
| eq_def | all | 0 | 0 | 0 | – | – |
| eq_def | outside file | 0 | 0 | 0 | – | – |
| eq_def | outside directory | 0 | 0 | 0 | – | – |
| all | all | 954 | 951 | 951 | 100.0% | 99.7% |
| all | outside file | 158 | 158 | 158 | 100.0% | 100.0% |
| all | outside directory | 26 | 26 | 26 | 100.0% | 100.0% |

Missed (in the reference only), first 3:

- `Bandits.GaussianTS.index` at `LMLPapers/LeanMachineLearning/Online/Bandit/GaussianTS.lean:182` (simp)
- `ProbabilityTheory.rademacherMeasure` at `LMLPapers/LeanMachineLearning/ForMathlib/Probability/Distributions/Rademacher.lean:125` (rw)
- `ProbabilityTheory.twoPoint` at `LMLPapers/LeanMachineLearning/ForMathlib/Probability/Distributions/TwoPoint.lean:72` (rw)

## Uses (definitions found by both)

| Scope | Reference uses | Compared uses | Ratio | Spearman per definition |
|---|---:|---:|---:|---:|
| all | 14,914 | 14,180 | 0.951 | 0.980 |
| outside file | 8,278 | 7,718 | 0.932 | 0.967 |
| outside directory | 4,190 | 3,849 | 0.919 | 0.955 |

Individual uses, matched by definition, file and line:

| Scope | Reference | Compared | Matched | Precision | Recall |
|---|---:|---:|---:|---:|---:|
| all | 14,869 | 14,135 | 14,134 | 100.0% | 95.1% |
| outside file | 8,233 | 7,673 | 7,672 | 100.0% | 93.2% |
| outside directory | 4,168 | 3,827 | 3,827 | 100.0% | 91.8% |

Uses in the compared output only (every 1th of 1):

- `Degenne2019Non.Setting.rules` at `LMLPapers/Papers/NeurIPS2019/Degenne2019Non/Theorem2.lean:37`

Largest differences in total uses:

| Definition | Reference | Compared |
|---|---:|---:|
| `Bandits.PEGame.RoundInfo` | 58 | 13 |
| `Learning.MDP.Episodic.stepLaw` | 167 | 123 |
| `Lee2026Unified.mdp` | 226 | 190 |
| `Chen2026Calibeating.Forecast` | 58 | 28 |
| `Learning.MDP.Episodic.Policy.extend` | 45 | 15 |
| `Bandits.PEGame.GameState` | 42 | 18 |
| `Frongillo2026Toward.pbar` | 38 | 14 |
| `Learning.MDP.env` | 62 | 39 |
| `Learning.simplex` | 560 | 538 |
| `Learning.OnlineLearner.state` | 28 | 10 |
| `Learning.MDP.Episodic.Policy` | 172 | 157 |
| `Learning.MDP.Episodic.regret` | 15 | 0 |
| `Bandits.MultiAnswerTask.optWeightsSet` | 22 | 8 |
| `Bandits.MultiAnswerTask.oracleWeights` | 22 | 9 |
| `Learning.MDP.Episodic.Episode` | 80 | 67 |

## Library indicators (definitions found by both)

| Group | Where | Measure | Reference | Compared |
|---|---|---|---:|---:|
| def/abbrev | outside file | definitions used | 1017 | 986 |
| def/abbrev | outside file | definitions unfolded | 89 | 89 |
| def/abbrev | outside file | share unfolded | 8.8% | 9.0% |
| def/abbrev | outside file | unfoldings | 158 | 158 |
| def/abbrev | outside file | unfoldings per 100 uses | 1.91 | 2.05 |
| def/abbrev | outside dir | definitions used | 511 | 477 |
| def/abbrev | outside dir | definitions unfolded | 20 | 20 |
| def/abbrev | outside dir | share unfolded | 3.9% | 4.2% |
| def/abbrev | outside dir | unfoldings | 26 | 26 |
| def/abbrev | outside dir | unfoldings per 100 uses | 0.62 | 0.68 |
| instance | outside file | definitions used | 0 | 0 |
| instance | outside file | definitions unfolded | 0 | 0 |
| instance | outside file | share unfolded | – | – |
| instance | outside file | unfoldings | 0 | 0 |
| instance | outside file | unfoldings per 100 uses | – | – |
| instance | outside dir | definitions used | 0 | 0 |
| instance | outside dir | definitions unfolded | 0 | 0 |
| instance | outside dir | share unfolded | – | – |
| instance | outside dir | unfoldings | 0 | 0 |
| instance | outside dir | unfoldings per 100 uses | – | – |
