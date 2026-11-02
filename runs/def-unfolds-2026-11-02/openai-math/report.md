# Explicit unfoldings of definitions: OpenAI Math

Backend: `source`. Source: `repos/openai-math/lean` at `1581d4cbdd69`.
Files scanned: 121,797.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (1,117,060 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 1,050,006 | 316,591 | 30.2% | 5,290,373 | 711,112 | 442,038 | 245,599 | 23,429 | 46 | 13.44 |
| outside file | 322,130 | 145,562 | 45.2% | 9,393,492 | 597,987 | 236,695 | 342,343 | 18,801 | 148 | 6.37 |
| outside directory | 109,261 | 32,351 | 29.6% | 4,394,029 | 264,123 | 126,932 | 132,734 | 4,409 | 48 | 6.01 |

## instance (21,062 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 1,004 | 15 | 1.5% | 1,724 | 22 | 5 | 17 | 0 | 0 | 1.28 |
| outside file | 846 | 10 | 1.2% | 5,684 | 12 | 7 | 5 | 0 | 0 | 0.21 |
| outside directory | 246 | 1 | 0.4% | 2,359 | 3 | 0 | 3 | 0 | 0 | 0.13 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `OAI.MUB6.difference` | def | `OAI/Analysis/MutuallyUnbiased/Matrix/Hadamard.lean` | 46223 | 90 | 233114 | 233119 |
| `OAI.MUB6.tripleCharges` | def | `OAI/Analysis/MutuallyUnbiased/MixedMoments/MixedShifts.lean` | 46218 | 87 | 138655 | 138661 |
| `OAI.MUB6.Certificate.Sparse.eval` | def | `OAI/Analysis/MutuallyUnbiased/Certificate/Algebra.lean` | 13317 | 451 | 95609 | 95639 |
| `OAI.MUB6.mergeFirst` | def | `OAI/Analysis/MutuallyUnbiased/Moments/MomentContraction.lean` | 12371 | 50 | 55640 | 55644 |
| `OAI.MUB6.Certificate.Integer.Sparse.eval` | def | `OAI/Analysis/MutuallyUnbiased/Certificate/Integer.lean` | 12197 | 558 | 95586 | 95596 |
| `OAI.InternalCatalan.barrierComplex` | def | `OAI/NumberTheory/Catalan/Energy/BarrierTailPairRational.lean` | 4074 | 301 | 6512 | 6568 |
| `OAI.InternalCatalan.barrierConjugatePair` | def | `OAI/NumberTheory/Catalan/Energy/BarrierTailPairRational.lean` | 2332 | 298 | 2335 | 2357 |
| `OAI.PolynomialVacuumAlgebra.exchangeTable` | def | `OAI/Combinatorics/PolynomialVacuum/Algebra/Table.lean` | 2082 | 12 | 2082 | 2083 |
| `OAI.InternalCatalan.barrierV2Tail` | def | `OAI/NumberTheory/Catalan/Energy/BarrierTailPairRational.lean` | 1672 | 208 | 6521 | 6535 |
| `OAI.SharpPlanar.IntegerIntervals.precision` | def | `OAI/Analysis/PlanarPacking/Intervals.lean` | 1626 | 22 | 1634 | 1677 |
| `OAI.MUB6.doubleCharges` | def | `OAI/Analysis/MutuallyUnbiased/MixedMoments/MixedShifts.lean` | 1533 | 85 | 4599 | 4603 |
| `OAI.InternalCatalan.barrierOctantMultiplier` | def | `OAI/NumberTheory/Catalan/Energy/BarrierComplexOctantRange.lean` | 1163 | 294 | 1163 | 1168 |
| `OAI.InternalCatalan.barrierOctantRotate` | def | `OAI/NumberTheory/Catalan/Energy/BarrierComplexOctantRange.lean` | 1163 | 294 | 1170 | 1187 |
| `OAI.SharpPlanar.normalizedH` | def | `OAI/Analysis/PlanarPacking/BernsteinBoxes.lean` | 1094 | 24 | 1096 | 1097 |
| `OAI.SharpPlanar.sourcePower` | def | `OAI/Analysis/PlanarPacking/BernsteinBoxes.lean` | 1094 | 24 | 6151 | 6151 |
| `OAI.MUB6.Balanced` | def | `OAI/Analysis/MutuallyUnbiased/Matrix/Definitions.lean` | 1074 | 82 | 3139 | 3141 |
| `OAI.InternalCatalan.manuscriptIntervalScale` | def | `OAI/NumberTheory/Catalan/Polynomial/ManuscriptRationalIntervals.lean` | 781 | 277 | 792 | 796 |
| `OAI.InternalCatalan.manuscriptIntervalAdd` | def | `OAI/NumberTheory/Catalan/Polynomial/ManuscriptRationalIntervals.lean` | 780 | 277 | 791 | 794 |
| `OAI.InternalCatalan.manuscriptLogHInterval` | def | `OAI/NumberTheory/Catalan/Analysis/ManuscriptNormLogVGroup056.lean` | 774 | 275 | 776 | 785 |
| `OAI.InternalCatalan.manuscriptScaledLogInterval` | def | `OAI/NumberTheory/Catalan/Analysis/ManuscriptNormLogVGroup056.lean` | 774 | 275 | 781 | 792 |
| `OAI.PolynomialVacuumAlgebra.t` | def | `OAI/Combinatorics/PolynomialVacuum/Algebra/Target.lean` | 749 | 19 | 898 | 906 |
| `OAI.PolynomialVacuumAlgebra.T` | def | `OAI/Combinatorics/PolynomialVacuum/Algebra/Target.lean` | 743 | 19 | 1234 | 1240 |
| `OAI.YauCounterexamples.Euclidean` | abbrev | `OAI/Geometry/SmoothYau/Model.lean` | 733 | 116 | 2701 | 2725 |
| `OAI.InternalCatalan.manuscriptAtanInterval` | def | `OAI/NumberTheory/Catalan/Analysis/ManuscriptNormLogVGroup056.lean` | 713 | 238 | 715 | 727 |
| `OAI.InternalCatalan.manuscriptArgInterval` | def | `OAI/NumberTheory/Catalan/Analysis/ManuscriptNormLogVGroup056.lean` | 711 | 237 | 713 | 724 |
| `OAI.InternalCatalan.manuscriptPiQuarterInterval` | def | `OAI/NumberTheory/Catalan/Analysis/ManuscriptNormLogVGroup056.lean` | 711 | 237 | 713 | 721 |
| `OAI.InternalCatalan.manuscriptWeightedComplexLogInterval` | def | `OAI/NumberTheory/Catalan/Analysis/ManuscriptNormLogVGroup056.lean` | 711 | 237 | 1424 | 1436 |
| `OAI.Laughlin.Certificate.arithmeticScale` | def | `OAI/Analysis/Laughlin/FourBody/Integral.lean` | 680 | 18 | 680 | 682 |
| `OAI.InternalCatalan.barrierP2Tail` | def | `OAI/NumberTheory/Catalan/Energy/BarrierTailPairRational.lean` | 659 | 94 | 2730 | 2741 |
| `OAI.PolynomialVacuumAlgebra.exchangeDenominator` | def | `OAI/Combinatorics/PolynomialVacuum/Algebra/Target.lean` | 641 | 21 | 795 | 796 |

## Most unfolded outside its directory

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `OAI.MUB6.difference` | def | `OAI/Analysis/MutuallyUnbiased/Matrix/Hadamard.lean` | 46223 | 90 | 233112 | 233119 |
| `OAI.MUB6.tripleCharges` | def | `OAI/Analysis/MutuallyUnbiased/MixedMoments/MixedShifts.lean` | 46218 | 87 | 138655 | 138661 |
| `OAI.MUB6.Certificate.Sparse.eval` | def | `OAI/Analysis/MutuallyUnbiased/Certificate/Algebra.lean` | 13317 | 451 | 95600 | 95639 |
| `OAI.MUB6.mergeFirst` | def | `OAI/Analysis/MutuallyUnbiased/Moments/MomentContraction.lean` | 12371 | 50 | 55640 | 55644 |
| `OAI.MUB6.Certificate.Integer.Sparse.eval` | def | `OAI/Analysis/MutuallyUnbiased/Certificate/Integer.lean` | 12193 | 555 | 95521 | 95596 |
| `OAI.InternalCatalan.barrierComplex` | def | `OAI/NumberTheory/Catalan/Energy/BarrierTailPairRational.lean` | 3951 | 299 | 6322 | 6568 |
| `OAI.InternalCatalan.barrierConjugatePair` | def | `OAI/NumberTheory/Catalan/Energy/BarrierTailPairRational.lean` | 2332 | 298 | 2334 | 2357 |
| `OAI.InternalCatalan.barrierV2Tail` | def | `OAI/NumberTheory/Catalan/Energy/BarrierTailPairRational.lean` | 1672 | 208 | 6515 | 6535 |
| `OAI.MUB6.doubleCharges` | def | `OAI/Analysis/MutuallyUnbiased/MixedMoments/MixedShifts.lean` | 1533 | 85 | 4599 | 4603 |
| `OAI.InternalCatalan.barrierOctantMultiplier` | def | `OAI/NumberTheory/Catalan/Energy/BarrierComplexOctantRange.lean` | 1163 | 294 | 1163 | 1168 |
| `OAI.InternalCatalan.barrierOctantRotate` | def | `OAI/NumberTheory/Catalan/Energy/BarrierComplexOctantRange.lean` | 1163 | 294 | 1167 | 1187 |
| `OAI.MUB6.Balanced` | def | `OAI/Analysis/MutuallyUnbiased/Matrix/Definitions.lean` | 1073 | 81 | 3137 | 3141 |
| `OAI.InternalCatalan.manuscriptIntervalAdd` | def | `OAI/NumberTheory/Catalan/Polynomial/ManuscriptRationalIntervals.lean` | 779 | 276 | 788 | 794 |
| `OAI.InternalCatalan.manuscriptIntervalScale` | def | `OAI/NumberTheory/Catalan/Polynomial/ManuscriptRationalIntervals.lean` | 779 | 276 | 788 | 796 |
| `OAI.Laughlin.Certificate.arithmeticScale` | def | `OAI/Analysis/Laughlin/FourBody/Integral.lean` | 680 | 18 | 680 | 682 |
| `OAI.InternalCatalan.barrierP2Tail` | def | `OAI/NumberTheory/Catalan/Energy/BarrierTailPairRational.lean` | 658 | 93 | 2725 | 2741 |
| `OAI.Laughlin.Certificate.GramCompute.ZFast` | def | `OAI/Analysis/Laughlin/FourBody/GramCompute.lean` | 610 | 111 | 1220 | 1221 |
| `OAI.MUB6.Certificate.PairSemantics.value0` | def | `OAI/Analysis/MutuallyUnbiased/PairSemantics/Values0.lean` | 561 | 69 | 1128 | 1132 |
| `OAI.InternalCatalan.barrierScaledLogRat` | def | `OAI/NumberTheory/Catalan/Energy/BarrierLogRatConstants.lean` | 497 | 58 | 525 | 529 |
| `OAI.InternalCatalan.barrierWeightedComplexLogRat` | def | `OAI/NumberTheory/Catalan/Energy/BarrierLogRatConstants.lean` | 449 | 57 | 3854 | 3857 |
| `OAI.InternalCatalan.barrierArgApproxRat` | def | `OAI/NumberTheory/Catalan/Energy/BarrierLogRatConstants.lean` | 448 | 57 | 452 | 455 |
| `OAI.TuringRigidity.BoundedSetTheory.Formula.Eval` | def | `OAI/Computability/DegreeRigidity/Syntax/BoundedSetTheory.lean` | 340 | 218 | 468 | 608 |
| `OAI.ScalarConductivity.centralThickness` | def | `OAI/Analysis/Conductivity/Geometry/BoxEnergyPoincare.lean` | 288 | 45 | 983 | 1046 |
| `OAI.LowSpaceSubsetSum.inputScale` | def | `OAI/Combinatorics/LowSpaceSubsetSum/Counting/Magnitudes.lean` | 269 | 145 | 1788 | 1830 |
| `OAI.UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt` | def | `OAI/Computability/UniqueGames/Reduction/MachineTransfer.lean` | 263 | 70 | 514 | 559 |
| `OAI.MUB6.Certificate.MixedSemantics.nodeValue4092` | def | `OAI/Analysis/MutuallyUnbiased/MixedSemantics/Values63.lean` | 251 | 76 | 752 | 754 |
| `OAI.MUB6.Certificate.MixedSemantics.nodeValue4091` | def | `OAI/Analysis/MutuallyUnbiased/MixedSemantics/Values63.lean` | 220 | 65 | 659 | 661 |
| `OAI.MUB6.Certificate.MixedSemantics.nodeValue4084` | def | `OAI/Analysis/MutuallyUnbiased/MixedSemantics/Values63.lean` | 215 | 68 | 644 | 646 |
| `OAI.MUB6.Certificate.PairSemantics.raw7981` | def | `OAI/Analysis/MutuallyUnbiased/PairSemantics/Canonical249.lean` | 206 | 34 | 206 | 211 |
| `OAI.PartitionPilot.Forcing.BoundedFormula.Truth` | def | `OAI/SetTheory/PartitionPrinciple/Definability/PresentedGroupCodes.lean` | 204 | 104 | 563 | 1102 |

## Diagnostics

- ambiguous name: 39,144
- field notation: 566,834
- names declared in several files: 15,098
