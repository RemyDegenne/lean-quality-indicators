# Explicit unfoldings of definitions: Tau Ceti

Backend: `ilean`. Source: `repos/tauceti` at `e8b7b600c36c`.
Files scanned: 16,726.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (23,273 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 22,750 | 8,772 | 38.6% | 217,300 | 18,575 | 1,468 | 9,235 | 7,758 | 114 | 8.55 |
| outside file | 15,312 | 308 | 2.0% | 375,302 | 1,057 | 32 | 774 | 235 | 16 | 0.28 |
| outside directory | 9,070 | 119 | 1.3% | 168,318 | 394 | 11 | 244 | 123 | 16 | 0.23 |

## instance (3,611 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 172 | 12 | 7.0% | 265 | 20 | 1 | 9 | 10 | 0 | 7.55 |
| outside file | 297 | 0 | 0.0% | 918 | 0 | 0 | 0 | 0 | 0 | 0.00 |
| outside directory | 203 | 0 | 0.0% | 521 | 0 | 0 | 0 | 0 | 0 | 0.00 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `TauCeti.GridRectangleBetween.sideColumns` | def | `TauCeti/KnotTheory/Grid/Rectangle/Basic.lean` | 51 | 16 | 93 | 97 |
| `TauCeti.zigzagVertexIdempotent` | abbrev | `TauCeti/RepresentationTheory/Quiver/Zigzag/Projective/Basic.lean` | 29 | 7 | 166 | 182 |
| `TauCeti.AlgebraicGeometry.WeilDivisor.coeff` | def | `TauCeti/AlgebraicGeometry/WeilDivisor/Basic.lean` | 24 | 17 | 395 | 446 |
| `TauCeti.Quiver.AffineE8.coordinateCount` | abbrev | `TauCeti/RepresentationTheory/Quiver/AffineE8/Basic.lean` | 22 | 1 | 38 | 38 |
| `TauCeti.GridPentagonRectangleDecomposition.pentagon` | abbrev | `TauCeti/KnotTheory/Grid/Commutation/Decomposition.lean` | 20 | 7 | 594 | 623 |
| `TauCeti.GridRectanglePentagonDecomposition.pentagon` | abbrev | `TauCeti/KnotTheory/Grid/Commutation/Decomposition.lean` | 20 | 8 | 811 | 847 |
| `TauCeti.IntegralLattice.signature` | abbrev | `TauCeti/LinearAlgebra/IntegralLattice/Signature.lean` | 19 | 12 | 47 | 55 |
| `TauCeti.PopaZagier.weight₃` | def | `TauCeti/NumberTheory/ModularForms/LevelOne/TraceFormula/ExplicitElement/Basic.lean` | 16 | 4 | 21 | 32 |
| `TauCeti.PopaZagier.weight₄` | def | `TauCeti/NumberTheory/ModularForms/LevelOne/TraceFormula/ExplicitElement/Basic.lean` | 16 | 4 | 20 | 31 |
| `TauCeti.Relator.commInvInv` | def | `TauCeti/GroupTheory/Presentation/Relator.lean` | 16 | 13 | 109 | 115 |
| `TauCeti.AlgebraicGeometry.WeilDivisor.pointDifference` | def | `TauCeti/AlgebraicGeometry/WeilDivisor/Basic.lean` | 15 | 6 | 51 | 89 |
| `TauCeti.ValidLieTypeIndex.rank` | abbrev | `TauCeti/GroupTheory/SpecificGroups/CFSG/Index.lean` | 15 | 4 | 276 | 291 |
| `TauCeti.zigzagBimoduleTensor` | abbrev | `TauCeti/RepresentationTheory/Quiver/Zigzag/Braid/Tensor.lean` | 15 | 1 | 25 | 34 |
| `TauCeti.IntegralLattice.dualCarrier` | abbrev | `TauCeti/LinearAlgebra/IntegralLattice/Dual/Basic.lean` | 14 | 10 | 254 | 280 |
| `TauCeti.PopaZagier.chainWeight₄` | def | `TauCeti/NumberTheory/ModularForms/LevelOne/TraceFormula/ExplicitElement/Basic.lean` | 14 | 2 | 15 | 23 |
| `TauCeti.ValidLieTypeIndex.dynkinType` | abbrev | `TauCeti/GroupTheory/SpecificGroups/CFSG/Index.lean` | 14 | 4 | 205 | 217 |
| `TauCeti.Bialgebra.AugmentationIdeal` | abbrev | `TauCeti/Algebra/AlgebraicGroup/Tangent/Cotangent.lean` | 13 | 5 | 68 | 91 |
| `TauCeti.G2ShortRoot.raisingMatrix` | def | `TauCeti/Algebra/Lie/G2/ShortRoot/Basic.lean` | 13 | 4 | 37 | 47 |
| `TauCeti.TypeDSpinCarrier.signSet` | abbrev | `TauCeti/Algebra/Lie/Orthogonal/TypeD/SpinCarrier/Basic.lean` | 12 | 4 | 48 | 55 |
| `TauCeti.G2ShortRoot.loweringMatrix` | def | `TauCeti/Algebra/Lie/G2/ShortRoot/Basic.lean` | 11 | 3 | 33 | 43 |
| `TauCeti.Green.curl` | def | `TauCeti/Analysis/Green/Basic.lean` | 10 | 8 | 118 | 123 |
| `TauCeti.PopaZagier.weight` | def | `TauCeti/NumberTheory/ModularForms/LevelOne/TraceFormula/ExplicitElement/Basic.lean` | 10 | 4 | 19 | 36 |
| `TauCeti.Green.circulationFun` | def | `TauCeti/Analysis/Green/Basic.lean` | 9 | 8 | 128 | 132 |
| `TauCeti.GridRectanglePentagonDecomposition.rectangle` | abbrev | `TauCeti/KnotTheory/Grid/Commutation/Decomposition.lean` | 9 | 4 | 805 | 830 |
| `TauCeti.GroupPresentation.generatorCount` | abbrev | `TauCeti/GroupTheory/Presentation/GroupPresentation.lean` | 9 | 5 | 21 | 30 |
| `TauCeti.IntegralLattice.sigNeg` | abbrev | `TauCeti/LinearAlgebra/IntegralLattice/Signature.lean` | 9 | 7 | 45 | 62 |
| `TauCeti.IntegralLattice.sigPos` | abbrev | `TauCeti/LinearAlgebra/IntegralLattice/Signature.lean` | 9 | 7 | 42 | 53 |
| `TauCeti.Multiquadratic.IsEvenPrimeDiscriminant` | def | `TauCeti/NumberTheory/Multiquadratic/EvenPrimeDiscriminant.lean` | 9 | 7 | 218 | 233 |
| `TauCeti.Multiquadratic.primeDiscriminantRadicand` | def | `TauCeti/NumberTheory/Multiquadratic/Prime/Discriminants.lean` | 9 | 4 | 135 | 167 |
| `TauCeti.CommHopfAlgCat.pointsFppfGroupObject` | def | `TauCeti/Algebra/AlgebraicGroup/Fppf/GroupObject.lean` | 8 | 1 | 35 | 41 |

## Most unfolded outside its directory

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `TauCeti.GridRectangleBetween.sideColumns` | def | `TauCeti/KnotTheory/Grid/Rectangle/Basic.lean` | 50 | 15 | 90 | 97 |
| `TauCeti.zigzagVertexIdempotent` | abbrev | `TauCeti/RepresentationTheory/Quiver/Zigzag/Projective/Basic.lean` | 22 | 1 | 51 | 182 |
| `TauCeti.AlgebraicGeometry.WeilDivisor.coeff` | def | `TauCeti/AlgebraicGeometry/WeilDivisor/Basic.lean` | 16 | 11 | 221 | 446 |
| `TauCeti.Relator.commInvInv` | def | `TauCeti/GroupTheory/Presentation/Relator.lean` | 16 | 13 | 109 | 115 |
| `TauCeti.IntegralLattice.dualCarrier` | abbrev | `TauCeti/LinearAlgebra/IntegralLattice/Dual/Basic.lean` | 14 | 10 | 223 | 280 |
| `TauCeti.Bialgebra.AugmentationIdeal` | abbrev | `TauCeti/Algebra/AlgebraicGroup/Tangent/Cotangent.lean` | 10 | 3 | 33 | 91 |
| `TauCeti.GroupPresentation.generatorCount` | abbrev | `TauCeti/GroupTheory/Presentation/GroupPresentation.lean` | 9 | 5 | 10 | 30 |
| `TauCeti.CommHopfAlgCat.pointsFppfGroupObject` | def | `TauCeti/Algebra/AlgebraicGroup/Fppf/GroupObject.lean` | 8 | 1 | 18 | 41 |
| `TauCeti.Multiquadratic.primeDiscriminantRadicand` | def | `TauCeti/NumberTheory/Multiquadratic/Prime/Discriminants.lean` | 8 | 3 | 47 | 167 |
| `TauCeti.CommHopfAlgCat.baseChange` | abbrev | `TauCeti/Algebra/AlgebraicGroup/CommHopfAlgCat/BaseChange.lean` | 7 | 7 | 342 | 372 |
| `TauCeti.ContCohomology.H1pi` | abbrev | `TauCeti/RepresentationTheory/Homological/ContCohomology/LowDegree.lean` | 7 | 4 | 15 | 27 |
| `CategoryTheory.CommMon.sectionsPresheaf` | def | `TauCeti/AlgebraicGeometry/Modules/Algebra/Sections.lean` | 6 | 1 | 27 | 49 |
| `TauCeti.AlgebraicGeometry.WeilDivisor.pointDifference` | def | `TauCeti/AlgebraicGeometry/WeilDivisor/Basic.lean` | 6 | 2 | 15 | 89 |
| `TauCeti.CommHopfAlgCat.pointsPresheafGrp` | def | `TauCeti/Algebra/AlgebraicGroup/Fppf/GroupObject.lean` | 6 | 1 | 10 | 43 |
| `TauCeti.CommHopfAlgCat.quotientPointsHom` | def | `TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Points/Basic.lean` | 6 | 6 | 223 | 254 |
| `TauCeti.Deck.subgroupFiberOrbitClass` | def | `TauCeti/AlgebraicTopology/UniversalCover/Deck/SubgroupFiberOrbit/Basic.lean` | 6 | 1 | 39 | 101 |
| `TauCeti.Multiquadratic.oddPrimeDiscriminant` | def | `TauCeti/NumberTheory/Multiquadratic/Prime/Discriminant/Basic.lean` | 6 | 1 | 66 | 93 |
| `TauCeti.Relator.conj` | def | `TauCeti/GroupTheory/Presentation/Relator.lean` | 6 | 3 | 90 | 96 |
| `TauCeti.Relator.div` | def | `TauCeti/GroupTheory/Presentation/Relator.lean` | 6 | 3 | 80 | 86 |
| `TauCeti.ClassData.rowsOfMap` | def | `TauCeti/RepresentationTheory/CharacterTable/Dixon/ClassData/Basic.lean` | 5 | 4 | 17 | 24 |
| `TauCeti.DynkinType.f4ShortRootAdjointMatrixBaseChange` | abbrev | `TauCeti/Algebra/Lie/F4/ShortRoot/Modular/Action.lean` | 5 | 3 | 49 | 50 |
| `TauCeti.GridState.pointSet` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 5 | 2 | 226 | 286 |
| `MvPowerSeries.pairSubstitution` | abbrev | `TauCeti/RingTheory/MvPowerSeries/Substitution.lean` | 4 | 1 | 96 | 115 |
| `TauCeti.GridDiagram.OSet` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 4 | 3 | 120 | 137 |
| `TauCeti.GridDiagram.XSet` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 4 | 3 | 186 | 213 |
| `TauCeti.GridDiagram.swapColumns` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 4 | 3 | 234 | 249 |
| `TauCeti.GridDiagram.swapRows` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 4 | 3 | 13 | 28 |
| `TauCeti.GridRectangleBetween.AvoidsMarkings` | def | `TauCeti/KnotTheory/Grid/Rectangle/Basic.lean` | 4 | 3 | 16 | 24 |
| `TauCeti.GridState.swapColumns` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 4 | 4 | 204 | 239 |
| `TauCeti.powerClassQuotient` | abbrev | `TauCeti/Algebra/Group/PowerClassGroup/Basic.lean` | 4 | 2 | 54 | 59 |

## Diagnostics

- declaration range not on its name: 2,868
- definition found through its references: 27
- use range not on the name (notation or stale): 25,628
