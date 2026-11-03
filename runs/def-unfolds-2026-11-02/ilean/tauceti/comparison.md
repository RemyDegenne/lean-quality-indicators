# Source backend against the ilean reference: Tau Ceti

Reference: `runs/def-unfolds-2026-11-02/ilean/tauceti` (ilean). Compared: `runs/def-unfolds-2026-11-02/tauceti` (source).

## Definitions

- found by both: 26,884
- only in the reference: 0
- only in the compared output: 0

## Explicit unfoldings (definitions found by both)

| Category | Scope | Reference | Compared | Matched | Precision | Recall |
|---|---|---:|---:|---:|---:|---:|
| unfold | all | 1,501 | 1,501 | 1,501 | 100.0% | 100.0% |
| unfold | outside file | 32 | 32 | 32 | 100.0% | 100.0% |
| unfold | outside directory | 11 | 11 | 11 | 100.0% | 100.0% |
| simp | all | 10,018 | 9,972 | 9,965 | 99.9% | 99.5% |
| simp | outside file | 774 | 772 | 772 | 100.0% | 99.7% |
| simp | outside directory | 244 | 243 | 243 | 100.0% | 99.6% |
| rw | all | 8,003 | 7,989 | 7,986 | 100.0% | 99.8% |
| rw | outside file | 235 | 234 | 234 | 100.0% | 99.6% |
| rw | outside directory | 123 | 123 | 123 | 100.0% | 100.0% |
| eq_def | all | 130 | 130 | 130 | 100.0% | 100.0% |
| eq_def | outside file | 16 | 16 | 16 | 100.0% | 100.0% |
| eq_def | outside directory | 16 | 16 | 16 | 100.0% | 100.0% |
| all | all | 19,652 | 19,592 | 19,582 | 99.9% | 99.6% |
| all | outside file | 1,057 | 1,054 | 1,054 | 100.0% | 99.7% |
| all | outside directory | 394 | 393 | 393 | 100.0% | 99.7% |

Missed (in the reference only), first 15:

- `CategoryTheory.Equivalence.extAddEquiv` at `TauCeti/Algebra/Homology/Ext/Equivalence.lean:55` (simp)
- `Polynomial.psc` at `TauCeti/RingTheory/Polynomial/Subresultant/Basic.lean:174` (rw)
- `Polynomial.signedPsc` at `TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean:70` (simp)
- `Polynomial.signedPsc` at `TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean:71` (simp)
- `Polynomial.signedPsc` at `TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean:78` (simp)
- `Polynomial.signedPsc` at `TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean:86` (simp)
- `Polynomial.signedPsc` at `TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean:95` (simp)
- `Polynomial.signedPsc` at `TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean:102` (simp)
- `Polynomial.signedPsc` at `TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean:110` (simp)
- `Polynomial.signedPsc` at `TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean:120` (simp)
- `Polynomial.signedPsc` at `TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean:122` (simp)
- `Polynomial.subresultantMatrix` at `TauCeti/RingTheory/Polynomial/Subresultant/Basic.lean:84` (simp)
- `Polynomial.subresultantMatrix` at `TauCeti/RingTheory/Polynomial/Subresultant/Basic.lean:94` (simp)
- `Polynomial.subresultantMatrix` at `TauCeti/RingTheory/Polynomial/Subresultant/Basic.lean:106` (simp)
- `Polynomial.subresultantMatrix` at `TauCeti/RingTheory/Polynomial/Subresultant/Basic.lean:115` (simp)

Spurious (in the compared output only), first 10:

- `TauCeti.ContinuousCohomology.res` at `TauCeti/RepresentationTheory/Homological/ContCohomology/Functoriality.lean:114` (simp)
- `TauCeti.spinSixTransvectionFirstVector` at `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/SpecialLinear.lean:737` (simp)
- `TauCeti.spinSixTransvectionFirstVector` at `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/SpecialLinear.lean:745` (simp)
- `TauCeti.spinSixTransvectionFirstVector` at `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/SpecialLinear.lean:753` (simp)
- `TauCeti.spinSixTransvectionLift` at `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/SpecialLinear.lean:734` (rw)
- `TauCeti.spinSixTransvectionLift` at `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/SpecialLinear.lean:742` (rw)
- `TauCeti.spinSixTransvectionLift` at `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/SpecialLinear.lean:750` (rw)
- `TauCeti.spinSixTransvectionSecondVector` at `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/SpecialLinear.lean:737` (simp)
- `TauCeti.spinSixTransvectionSecondVector` at `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/SpecialLinear.lean:745` (simp)
- `TauCeti.spinSixTransvectionSecondVector` at `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/SpecialLinear.lean:753` (simp)

## Uses (definitions found by both)

| Scope | Reference uses | Compared uses | Ratio | Spearman per definition |
|---|---:|---:|---:|---:|
| all | 593,785 | 545,581 | 0.919 | 0.979 |
| outside file | 376,220 | 338,857 | 0.901 | 0.974 |
| outside directory | 168,839 | 147,960 | 0.876 | 0.960 |

Individual uses, matched by definition, file and line:

| Scope | Reference | Compared | Matched | Precision | Recall |
|---|---:|---:|---:|---:|---:|
| all | 593,785 | 545,581 | 544,901 | 99.9% | 91.8% |
| outside file | 376,220 | 338,857 | 338,362 | 99.9% | 89.9% |
| outside directory | 168,839 | 147,960 | 147,810 | 99.9% | 87.5% |

Uses in the compared output only (every 45th of 680):

- `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv` at `TauCeti/AlgebraicTopology/Homotopy/Whitehead.lean:87`
- `Subgroup.LinearizingCoordinate.discCoordinate` at `TauCeti/Analysis/Complex/Fuchsian/Elliptic/Linearizing.lean:294`
- `TauCeti.ClassFieldTheory.NormalLayer.H` at `TauCeti/NumberTheory/ClassFieldTheory/Formation/AbsoluteArtinMap.lean:321`
- `TauCeti.DoubledQuiver.map` at `TauCeti/RepresentationTheory/Quiver/Zigzag/Basic.lean:304`
- `TauCeti.GraphTwistedIndex.Group` at `TauCeti/GroupTheory/SpecificGroups/CFSG/Assembly/GraphTwisted.lean:189`
- `TauCeti.GridCommutationHexagonBetween.toGridRectangleBetween` at `TauCeti/KnotTheory/Grid/Commutation/Homotopy/InitialPair/Weight.lean:129`
- `TauCeti.GridCommutationHexagonBetween.toGridRectangleBetween` at `TauCeti/KnotTheory/Grid/Commutation/Homotopy/MixedPair.lean:555`
- `TauCeti.GridCommutationHexagonBetween.toGridRectangleBetween` at `TauCeti/KnotTheory/Grid/Commutation/Homotopy/PentagonPair.lean:371`
- `TauCeti.Hodge.HodgeStructure.internalHom` at `TauCeti/Geometry/Hodge/InternalHom/Basic.lean:568`
- `TauCeti.IsNonUnitalDGAlgebra.toAInfinityAlgebra` at `TauCeti/CategoryTheory/AInfinity/Opposite.lean:90`
- `TauCeti.PathAlgebra.single` at `TauCeti/RepresentationTheory/Quiver/PathAlgebra/Basic.lean:540`
- `TauCeti.PathAlgebra.single` at `TauCeti/RepresentationTheory/Quiver/Zigzag/Skew/Basis.lean:317`
- `TauCeti.TraceFormulaMatrixModule.right` at `TauCeti/NumberTheory/ModularForms/LevelOne/TraceFormula/MatrixModule.lean:242`
- `TauCeti.WedgeSum.base` at `TauCeti/AlgebraicTopology/FundamentalGroup/WedgeSum.lean:253`
- `TauCeti.completedGroupAlgebra.of` at `TauCeti/Topology/Algebra/Group/Profinite/CompletedGroupAlgebra/Module.lean:153`

Largest differences in total uses:

| Definition | Reference | Compared |
|---|---:|---:|
| `TauCeti.GridRectangleBetween.top` | 1041 | 87 |
| `TauCeti.GridRectangleBetween.bottom` | 1045 | 98 |
| `TauCeti.Place.integers` | 1840 | 936 |
| `TauCeti.GridRectangleBetween.IsEmpty` | 894 | 39 |
| `TauCeti.freeProP` | 2604 | 1801 |
| `TauCeti.ValuationSpectrum.valuation` | 702 | 1 |
| `TauCeti.HopfIdeal.toIdeal` | 1336 | 639 |
| `TauCeti.GridRectangleBetween.toGridRectangle` | 825 | 306 |
| `TauCeti.ValidLieTypeIndex.Closure` | 564 | 74 |
| `TauCeti.Place.ord` | 1022 | 560 |
| `TauCeti.GridRectangle.coveredSquares` | 501 | 54 |
| `TauCeti.Place.restrict` | 1099 | 775 |
| `TauCeti.PDCode.crossing` | 490 | 174 |
| `TauCeti.Place.ResidueField` | 564 | 279 |
| `TauCeti.DynkinType.rank` | 885 | 612 |

## Library indicators (definitions found by both)

| Group | Where | Measure | Reference | Compared |
|---|---|---|---:|---:|
| def/abbrev | outside file | definitions used | 15312 | 14775 |
| def/abbrev | outside file | definitions unfolded | 308 | 308 |
| def/abbrev | outside file | share unfolded | 2.0% | 2.1% |
| def/abbrev | outside file | unfoldings | 1057 | 1054 |
| def/abbrev | outside file | unfoldings per 100 uses | 0.28 | 0.31 |
| def/abbrev | outside dir | definitions used | 9070 | 8504 |
| def/abbrev | outside dir | definitions unfolded | 119 | 118 |
| def/abbrev | outside dir | share unfolded | 1.3% | 1.4% |
| def/abbrev | outside dir | unfoldings | 394 | 393 |
| def/abbrev | outside dir | unfoldings per 100 uses | 0.23 | 0.27 |
| instance | outside file | definitions used | 297 | 289 |
| instance | outside file | definitions unfolded | 0 | 0 |
| instance | outside file | share unfolded | 0.0% | 0.0% |
| instance | outside file | unfoldings | 0 | 0 |
| instance | outside file | unfoldings per 100 uses | 0.00 | 0.00 |
| instance | outside dir | definitions used | 203 | 198 |
| instance | outside dir | definitions unfolded | 0 | 0 |
| instance | outside dir | share unfolded | 0.0% | 0.0% |
| instance | outside dir | unfoldings | 0 | 0 |
| instance | outside dir | unfoldings per 100 uses | 0.00 | 0.00 |
