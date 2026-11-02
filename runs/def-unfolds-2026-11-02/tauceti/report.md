# Explicit unfoldings of definitions: Tau Ceti

Backend: `source`. Source: `repos/tauceti` at `e8b7b600c36c`.
Files scanned: 16,726.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (23,273 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 22,552 | 8,753 | 38.8% | 206,461 | 18,518 | 1,468 | 9,191 | 7,745 | 114 | 8.97 |
| outside file | 14,775 | 308 | 2.1% | 337,956 | 1,054 | 32 | 772 | 234 | 16 | 0.31 |
| outside directory | 8,504 | 118 | 1.4% | 147,446 | 393 | 11 | 243 | 123 | 16 | 0.27 |

## instance (3,611 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 172 | 12 | 7.0% | 263 | 20 | 1 | 9 | 10 | 0 | 7.60 |
| outside file | 289 | 0 | 0.0% | 901 | 0 | 0 | 0 | 0 | 0 | 0.00 |
| outside directory | 198 | 0 | 0.0% | 514 | 0 | 0 | 0 | 0 | 0 | 0.00 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `TauCeti.GridRectangleBetween.sideColumns` | def | `TauCeti/KnotTheory/Grid/Rectangle/Basic.lean` | 51 | 16 | 52 | 56 |
| `TauCeti.zigzagVertexIdempotent` | abbrev | `TauCeti/RepresentationTheory/Quiver/Zigzag/Projective/Basic.lean` | 29 | 7 | 160 | 176 |
| `TauCeti.AlgebraicGeometry.WeilDivisor.coeff` | def | `TauCeti/AlgebraicGeometry/WeilDivisor/Basic.lean` | 24 | 17 | 222 | 269 |
| `TauCeti.Quiver.AffineE8.coordinateCount` | abbrev | `TauCeti/RepresentationTheory/Quiver/AffineE8/Basic.lean` | 22 | 1 | 38 | 38 |
| `TauCeti.GridPentagonRectangleDecomposition.pentagon` | abbrev | `TauCeti/KnotTheory/Grid/Commutation/Decomposition.lean` | 20 | 7 | 433 | 455 |
| `TauCeti.GridRectanglePentagonDecomposition.pentagon` | abbrev | `TauCeti/KnotTheory/Grid/Commutation/Decomposition.lean` | 20 | 8 | 642 | 668 |
| `TauCeti.IntegralLattice.signature` | abbrev | `TauCeti/LinearAlgebra/IntegralLattice/Signature.lean` | 19 | 12 | 29 | 36 |
| `TauCeti.PopaZagier.weight₃` | def | `TauCeti/NumberTheory/ModularForms/LevelOne/TraceFormula/ExplicitElement/Basic.lean` | 16 | 4 | 21 | 32 |
| `TauCeti.PopaZagier.weight₄` | def | `TauCeti/NumberTheory/ModularForms/LevelOne/TraceFormula/ExplicitElement/Basic.lean` | 16 | 4 | 20 | 31 |
| `TauCeti.Relator.commInvInv` | def | `TauCeti/GroupTheory/Presentation/Relator.lean` | 16 | 13 | 109 | 115 |
| `TauCeti.AlgebraicGeometry.WeilDivisor.pointDifference` | def | `TauCeti/AlgebraicGeometry/WeilDivisor/Basic.lean` | 15 | 6 | 51 | 89 |
| `TauCeti.ValidLieTypeIndex.rank` | abbrev | `TauCeti/GroupTheory/SpecificGroups/CFSG/Index.lean` | 15 | 4 | 28 | 30 |
| `TauCeti.zigzagBimoduleTensor` | abbrev | `TauCeti/RepresentationTheory/Quiver/Zigzag/Braid/Tensor.lean` | 15 | 1 | 25 | 34 |
| `TauCeti.IntegralLattice.dualCarrier` | abbrev | `TauCeti/LinearAlgebra/IntegralLattice/Dual/Basic.lean` | 14 | 10 | 174 | 193 |
| `TauCeti.PopaZagier.chainWeight₄` | def | `TauCeti/NumberTheory/ModularForms/LevelOne/TraceFormula/ExplicitElement/Basic.lean` | 14 | 2 | 15 | 23 |
| `TauCeti.ValidLieTypeIndex.dynkinType` | abbrev | `TauCeti/GroupTheory/SpecificGroups/CFSG/Index.lean` | 14 | 4 | 67 | 70 |
| `TauCeti.Bialgebra.AugmentationIdeal` | abbrev | `TauCeti/Algebra/AlgebraicGroup/Tangent/Cotangent.lean` | 13 | 5 | 68 | 91 |
| `TauCeti.G2ShortRoot.raisingMatrix` | def | `TauCeti/Algebra/Lie/G2/ShortRoot/Basic.lean` | 13 | 4 | 37 | 47 |
| `TauCeti.TypeDSpinCarrier.signSet` | abbrev | `TauCeti/Algebra/Lie/Orthogonal/TypeD/SpinCarrier/Basic.lean` | 12 | 4 | 48 | 55 |
| `TauCeti.G2ShortRoot.loweringMatrix` | def | `TauCeti/Algebra/Lie/G2/ShortRoot/Basic.lean` | 11 | 3 | 33 | 43 |
| `TauCeti.Green.curl` | def | `TauCeti/Analysis/Green/Basic.lean` | 10 | 8 | 118 | 123 |
| `TauCeti.PopaZagier.weight` | def | `TauCeti/NumberTheory/ModularForms/LevelOne/TraceFormula/ExplicitElement/Basic.lean` | 10 | 4 | 19 | 36 |
| `TauCeti.Green.circulationFun` | def | `TauCeti/Analysis/Green/Basic.lean` | 9 | 8 | 128 | 132 |
| `TauCeti.GridRectanglePentagonDecomposition.rectangle` | abbrev | `TauCeti/KnotTheory/Grid/Commutation/Decomposition.lean` | 9 | 4 | 623 | 643 |
| `TauCeti.GroupPresentation.generatorCount` | abbrev | `TauCeti/GroupTheory/Presentation/GroupPresentation.lean` | 9 | 5 | 20 | 29 |
| `TauCeti.IntegralLattice.sigNeg` | abbrev | `TauCeti/LinearAlgebra/IntegralLattice/Signature.lean` | 9 | 7 | 24 | 40 |
| `TauCeti.IntegralLattice.sigPos` | abbrev | `TauCeti/LinearAlgebra/IntegralLattice/Signature.lean` | 9 | 7 | 23 | 33 |
| `TauCeti.Multiquadratic.IsEvenPrimeDiscriminant` | def | `TauCeti/NumberTheory/Multiquadratic/EvenPrimeDiscriminant.lean` | 9 | 7 | 210 | 225 |
| `TauCeti.Multiquadratic.primeDiscriminantRadicand` | def | `TauCeti/NumberTheory/Multiquadratic/Prime/Discriminants.lean` | 9 | 4 | 134 | 166 |
| `TauCeti.CommHopfAlgCat.pointsFppfGroupObject` | def | `TauCeti/Algebra/AlgebraicGroup/Fppf/GroupObject.lean` | 8 | 1 | 35 | 41 |

## Most unfolded outside its directory

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `TauCeti.GridRectangleBetween.sideColumns` | def | `TauCeti/KnotTheory/Grid/Rectangle/Basic.lean` | 50 | 15 | 50 | 56 |
| `TauCeti.zigzagVertexIdempotent` | abbrev | `TauCeti/RepresentationTheory/Quiver/Zigzag/Projective/Basic.lean` | 22 | 1 | 51 | 176 |
| `TauCeti.AlgebraicGeometry.WeilDivisor.coeff` | def | `TauCeti/AlgebraicGeometry/WeilDivisor/Basic.lean` | 16 | 11 | 48 | 269 |
| `TauCeti.Relator.commInvInv` | def | `TauCeti/GroupTheory/Presentation/Relator.lean` | 16 | 13 | 109 | 115 |
| `TauCeti.IntegralLattice.dualCarrier` | abbrev | `TauCeti/LinearAlgebra/IntegralLattice/Dual/Basic.lean` | 14 | 10 | 150 | 193 |
| `TauCeti.Bialgebra.AugmentationIdeal` | abbrev | `TauCeti/Algebra/AlgebraicGroup/Tangent/Cotangent.lean` | 10 | 3 | 33 | 91 |
| `TauCeti.GroupPresentation.generatorCount` | abbrev | `TauCeti/GroupTheory/Presentation/GroupPresentation.lean` | 9 | 5 | 9 | 29 |
| `TauCeti.CommHopfAlgCat.pointsFppfGroupObject` | def | `TauCeti/Algebra/AlgebraicGroup/Fppf/GroupObject.lean` | 8 | 1 | 18 | 41 |
| `TauCeti.Multiquadratic.primeDiscriminantRadicand` | def | `TauCeti/NumberTheory/Multiquadratic/Prime/Discriminants.lean` | 8 | 3 | 46 | 166 |
| `TauCeti.CommHopfAlgCat.baseChange` | abbrev | `TauCeti/Algebra/AlgebraicGroup/CommHopfAlgCat/BaseChange.lean` | 7 | 7 | 342 | 372 |
| `TauCeti.ContCohomology.H1pi` | abbrev | `TauCeti/RepresentationTheory/Homological/ContCohomology/LowDegree.lean` | 7 | 4 | 15 | 27 |
| `CategoryTheory.CommMon.sectionsPresheaf` | def | `TauCeti/AlgebraicGeometry/Modules/Algebra/Sections.lean` | 6 | 1 | 21 | 40 |
| `TauCeti.AlgebraicGeometry.WeilDivisor.pointDifference` | def | `TauCeti/AlgebraicGeometry/WeilDivisor/Basic.lean` | 6 | 2 | 15 | 89 |
| `TauCeti.CommHopfAlgCat.pointsPresheafGrp` | def | `TauCeti/Algebra/AlgebraicGroup/Fppf/GroupObject.lean` | 6 | 1 | 10 | 43 |
| `TauCeti.CommHopfAlgCat.quotientPointsHom` | def | `TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Points/Basic.lean` | 6 | 6 | 223 | 254 |
| `TauCeti.Deck.subgroupFiberOrbitClass` | def | `TauCeti/AlgebraicTopology/UniversalCover/Deck/SubgroupFiberOrbit/Basic.lean` | 6 | 1 | 39 | 101 |
| `TauCeti.Multiquadratic.oddPrimeDiscriminant` | def | `TauCeti/NumberTheory/Multiquadratic/Prime/Discriminant/Basic.lean` | 6 | 1 | 65 | 92 |
| `TauCeti.Relator.conj` | def | `TauCeti/GroupTheory/Presentation/Relator.lean` | 6 | 3 | 76 | 82 |
| `TauCeti.Relator.div` | def | `TauCeti/GroupTheory/Presentation/Relator.lean` | 6 | 3 | 68 | 74 |
| `TauCeti.ClassData.rowsOfMap` | def | `TauCeti/RepresentationTheory/CharacterTable/Dixon/ClassData/Basic.lean` | 5 | 4 | 13 | 20 |
| `TauCeti.DynkinType.f4ShortRootAdjointMatrixBaseChange` | abbrev | `TauCeti/Algebra/Lie/F4/ShortRoot/Modular/Action.lean` | 5 | 3 | 49 | 50 |
| `TauCeti.GridState.pointSet` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 5 | 2 | 199 | 246 |
| `MvPowerSeries.pairSubstitution` | abbrev | `TauCeti/RingTheory/MvPowerSeries/Substitution.lean` | 4 | 1 | 96 | 115 |
| `TauCeti.GridDiagram.OSet` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 4 | 3 | 112 | 122 |
| `TauCeti.GridDiagram.XSet` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 4 | 3 | 136 | 155 |
| `TauCeti.GridDiagram.swapColumns` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 4 | 3 | 227 | 239 |
| `TauCeti.GridDiagram.swapRows` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 4 | 3 | 11 | 23 |
| `TauCeti.GridRectangleBetween.AvoidsMarkings` | def | `TauCeti/KnotTheory/Grid/Rectangle/Basic.lean` | 4 | 3 | 8 | 15 |
| `TauCeti.GridState.swapColumns` | def | `TauCeti/KnotTheory/Grid/Diagram/Basic.lean` | 4 | 4 | 150 | 179 |
| `TauCeti.powerClassQuotient` | abbrev | `TauCeti/Algebra/Group/PowerClassGroup/Basic.lean` | 4 | 2 | 54 | 59 |

## Diagnostics

- ambiguous name: 364
- field notation: 100,689
- names declared in several files: 2
