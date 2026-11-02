# Explicit unfoldings of definitions: LMLPapers (local build)

Backend: `ilean`. Source: `../LMLPapers` at `ad748994552c`.
Files scanned: 1,037.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (1,661 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 1,224 | 431 | 35.2% | 6,657 | 799 | 254 | 344 | 201 | 0 | 12.00 |
| outside file | 1,029 | 94 | 9.1% | 8,344 | 172 | 45 | 68 | 59 | 0 | 2.06 |
| outside directory | 516 | 20 | 3.9% | 4,200 | 26 | 6 | 11 | 9 | 0 | 0.62 |

## instance (12 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 0 | 0 | – | 0 | 0 | 0 | 0 | 0 | 0 | – |
| outside file | 0 | 0 | – | 0 | 0 | 0 | 0 | 0 | 0 | – |
| outside directory | 0 | 0 | – | 0 | 0 | 0 | 0 | 0 | 0 | – |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `Learning.tsallisEntropy` | def | `LMLPapers/LeanMachineLearning/Online/Bandit/SimplexFTRL.lean` | 10 | 2 | 95 | 97 |
| `Learning.Betting.subgaussianTest` | def | `LMLPapers/LeanMachineLearning/Betting/Wealth.lean` | 7 | 3 | 60 | 61 |
| `Learning.Betting.fixedWealth` | def | `LMLPapers/LeanMachineLearning/Betting/Wealth.lean` | 6 | 3 | 46 | 51 |
| `Learning.Betting.wealth` | def | `LMLPapers/LeanMachineLearning/Betting/Wealth.lean` | 6 | 4 | 77 | 91 |
| `Learning.MDP.shiftRounds` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Markov.lean` | 6 | 2 | 17 | 23 |
| `Learning.Betting.empMean` | def | `LMLPapers/LeanMachineLearning/Betting/Strategies.lean` | 4 | 2 | 11 | 16 |
| `Learning.RepeatedGame.gameEnv` | def | `LMLPapers/LeanMachineLearning/Game/RepeatedGame.lean` | 4 | 3 | 31 | 31 |
| `Learning.RepeatedGame.psmr` | def | `LMLPapers/LeanMachineLearning/Game/RepeatedGame.lean` | 4 | 2 | 22 | 22 |
| `Learning.ocoRegret` | def | `LMLPapers/LeanMachineLearning/Online/Convex/Regret.lean` | 4 | 4 | 24 | 63 |
| `Bandits.Linear.noise` | def | `LMLPapers/LeanMachineLearning/Online/Bandit/Linear/Noise.lean` | 3 | 3 | 10 | 39 |
| `Learning.Betting.agrapaFraction` | def | `LMLPapers/LeanMachineLearning/Betting/Strategies.lean` | 3 | 2 | 14 | 14 |
| `Learning.Betting.empVar` | def | `LMLPapers/LeanMachineLearning/Betting/Strategies.lean` | 3 | 2 | 4 | 7 |
| `Learning.MDP.Episodic.entropicVarV` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Entropic.lean` | 3 | 1 | 22 | 22 |
| `Learning.MDP.Episodic.occupancyMeasure` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Episodic.lean` | 3 | 2 | 9 | 12 |
| `Learning.MDP.Episodic.stateAction` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Episodic.lean` | 3 | 2 | 6 | 9 |
| `Learning.ZeroSumGame.mixedUtility` | def | `LMLPapers/LeanMachineLearning/Game/ZeroSum.lean` | 3 | 1 | 8 | 21 |
| `ProbabilityTheory.twoPoint` | def | `LMLPapers/LeanMachineLearning/ForMathlib/Probability/Distributions/TwoPoint.lean` | 3 | 2 | 11 | 21 |
| `Bandits.Linear.ucbIndex` | def | `LMLPapers/LeanMachineLearning/Online/Bandit/Linear/Ridge.lean` | 2 | 1 | 8 | 10 |
| `Bandits.pseudoRegret` | def | `LMLPapers/LeanMachineLearning/Online/Bandit/Adversarial.lean` | 2 | 2 | 15 | 21 |
| `Learning.Betting.hedgeFraction` | def | `LMLPapers/LeanMachineLearning/Betting/Strategies.lean` | 2 | 1 | 8 | 8 |
| `Learning.Betting.ktFraction` | def | `LMLPapers/LeanMachineLearning/Betting/Strategies.lean` | 2 | 2 | 8 | 10 |
| `Learning.MDP.Episodic.entropicVarQ` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Entropic.lean` | 2 | 1 | 7 | 8 |
| `Learning.MDP.Episodic.occupancy` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Episodic.lean` | 2 | 2 | 20 | 20 |
| `Learning.MDP.Episodic.statesLaw` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Episodic.lean` | 2 | 2 | 5 | 10 |
| `Learning.MDP.transVec` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Vec.lean` | 2 | 2 | 6 | 12 |
| `Learning.RepeatedGame.externalRegretAgainst` | def | `LMLPapers/LeanMachineLearning/Game/RepeatedGame.lean` | 2 | 1 | 6 | 9 |
| `Learning.RepeatedGame.stationaryReward` | def | `LMLPapers/LeanMachineLearning/Game/RepeatedGame.lean` | 2 | 1 | 6 | 8 |
| `Learning.ZeroSumGame.rowGap` | def | `LMLPapers/LeanMachineLearning/Game/ZeroSum.lean` | 2 | 1 | 6 | 8 |
| `Learning.ftrlValue` | def | `LMLPapers/LeanMachineLearning/Online/Bandit/SimplexFTRL.lean` | 2 | 1 | 27 | 29 |
| `Learning.gram` | def | `LMLPapers/LeanMachineLearning/DesignMatrix.lean` | 2 | 2 | 6 | 17 |

## Most unfolded outside its directory

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `Learning.ocoRegret` | def | `LMLPapers/LeanMachineLearning/Online/Convex/Regret.lean` | 3 | 3 | 22 | 63 |
| `ProbabilityTheory.gaussianWidth` | def | `LMLPapers/LeanMachineLearning/ForMathlib/Probability/GaussianWidth.lean` | 2 | 1 | 5 | 40 |
| `ProbabilityTheory.twoPoint` | def | `LMLPapers/LeanMachineLearning/ForMathlib/Probability/Distributions/TwoPoint.lean` | 2 | 1 | 9 | 21 |
| `Real.expSubOneSub` | def | `LMLPapers/LeanMachineLearning/ForMathlib/Analysis/SpecialFunctions/PoissonCramer.lean` | 2 | 1 | 42 | 56 |
| `Real.softmax` | def | `LMLPapers/LeanMachineLearning/ForMathlib/Analysis/SpecialFunctions/LogSumExp.lean` | 2 | 2 | 40 | 75 |
| `Bandits.Linear.noise` | def | `LMLPapers/LeanMachineLearning/Online/Bandit/Linear/Noise.lean` | 1 | 1 | 2 | 39 |
| `Bandits.MultiAnswerTask.oracleWeights` | def | `LMLPapers/LeanMachineLearning/Identification/MultiAnswer.lean` | 1 | 1 | 17 | 22 |
| `InformationTheory.klBerReal` | def | `LMLPapers/LeanMachineLearning/ForMathlib/InformationTheory/KullbackLeibler/Bernoulli.lean` | 1 | 1 | 6 | 39 |
| `Learning.MDP.EmpiricalModel.count` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Empirical.lean` | 1 | 1 | 6 | 16 |
| `Learning.MDP.EmpiricalModel.empReward` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Empirical.lean` | 1 | 1 | 3 | 4 |
| `Learning.MDP.EmpiricalModel.empTrans` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/MDP/Empirical.lean` | 1 | 1 | 4 | 9 |
| `Learning.MarketMaking.gain` | def | `LMLPapers/LeanMachineLearning/Online/MarketMaking.lean` | 1 | 1 | 4 | 13 |
| `Learning.PhasedAlg.phaseFeedback` | def | `LMLPapers/LeanMachineLearning/SequentialLearning/Algorithms/Phased.lean` | 1 | 1 | 2 | 7 |
| `Learning.TD.sampleVec` | def | `LMLPapers/LeanMachineLearning/ReinforcementLearning/TD/Linear.lean` | 1 | 1 | 2 | 5 |
| `Learning.designSet` | def | `LMLPapers/LeanMachineLearning/DesignMatrix.lean` | 1 | 1 | 13 | 28 |
| `Learning.envDensity` | def | `LMLPapers/LeanMachineLearning/SequentialLearning/EnvDensity.lean` | 1 | 1 | 2 | 11 |
| `Learning.linRegret` | def | `LMLPapers/LeanMachineLearning/Online/Convex/Regret.lean` | 1 | 1 | 19 | 39 |
| `Learning.openSimplex` | def | `LMLPapers/LeanMachineLearning/ForMathlib/Analysis/Convex/Simplex.lean` | 1 | 1 | 12 | 13 |
| `Learning.priorExpWeights` | def | `LMLPapers/LeanMachineLearning/Online/Convex/ExpWeights.lean` | 1 | 1 | 2 | 12 |
| `Real.logSumExp` | def | `LMLPapers/LeanMachineLearning/ForMathlib/Analysis/SpecialFunctions/LogSumExp.lean` | 1 | 1 | 4 | 30 |

## Diagnostics

- declaration range not on its name: 162
- module without source: 115
