# Explicit unfoldings of definitions: Formal Frontier

Backend: `source`. Source: `repos`.
Files scanned: 1,342.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (3,821 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 3,593 | 856 | 23.8% | 31,477 | 1,710 | 118 | 1,375 | 216 | 1 | 5.43 |
| outside file | 1,416 | 133 | 9.4% | 19,369 | 299 | 22 | 244 | 33 | 0 | 1.54 |
| outside directory | 199 | 12 | 6.0% | 2,360 | 27 | 1 | 23 | 3 | 0 | 1.14 |

## instance (525 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 45 | 3 | 6.7% | 98 | 3 | 1 | 2 | 0 | 0 | 3.06 |
| outside file | 20 | 0 | 0.0% | 27 | 0 | 0 | 0 | 0 | 0 | 0.00 |
| outside directory | 9 | 0 | 0.0% | 9 | 0 | 0 | 0 | 0 | 0 | 0.00 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ToricIdeals.RationalNormalCurve.coordinateExponent` | def | `toric-ideals/ToricIdeals/RationalNormalCurve.lean` | 17 | 8 | 31 | 48 |
| `MvPolynomial.blockSubst` | def | `multivariate-polynomials/MultivariatePolynomials/BlockSubstitution.lean` | 10 | 2 | 66 | 69 |
| `Bass.IsRightUnimodular` | def | `stable-range/StableRange/Basic.lean` | 8 | 4 | 49 | 58 |
| `ContinuousCohomology.degreeOneIso` | def | `continuous-group-cohomology/ContinuousGroupCohomology/DegreeOne.lean` | 8 | 4 | 52 | 57 |
| `TopCat.Sheaf.pullbackCompInv` | abbrev | `sheaf-cohomology/SheafCohomology/PullbackCoherence.lean` | 8 | 5 | 53 | 55 |
| `ToricIdeals.RationalNormalCurve.hankelMinor` | def | `toric-ideals/ToricIdeals/RationalNormalCurve.lean` | 8 | 6 | 18 | 28 |
| `Matrix.GeneralLinearGroup.upperUnit` | def | `general-linear-groups/GeneralLinearGroups/Whitehead.lean` | 6 | 2 | 31 | 39 |
| `QuadraticAlgebra.definingPolynomial` | def | `quadratic-algebras/QuadraticAlgebras/AdjoinRoot.lean` | 6 | 2 | 21 | 30 |
| `UnitriangularCoordinateRing.relation` | def | `algebraic-groups/AlgebraicGroups/Algebra/UnitriangularCoordinateRing.lean` | 6 | 2 | 8 | 30 |
| `AlgebraicGeometry.SheafedSpace.triangleMap` | def | `sheaf-cohomology/SheafCohomology/ConePullback.lean` | 5 | 4 | 38 | 53 |
| `DiagonalCoordinateRing.relation` | def | `algebraic-groups/AlgebraicGroups/Algebra/DiagonalCoordinateRing.lean` | 5 | 2 | 5 | 18 |
| `Matrix.GeneralLinearGroup.lowerUnit` | def | `general-linear-groups/GeneralLinearGroups/Whitehead.lean` | 5 | 2 | 23 | 29 |
| `SphereTopology.sphere2SouthPoint` | def | `sphere-topology/SphereTopology/Homology/Singular/Sphere.lean` | 5 | 1 | 10 | 19 |
| `TopCat.Sheaf.pullbackCompHom` | abbrev | `sheaf-cohomology/SheafCohomology/PullbackCoherence.lean` | 5 | 3 | 33 | 35 |
| `UpperTriangularCoordinateRing.relation` | def | `algebraic-groups/AlgebraicGroups/Algebra/UpperTriangularCoordinateRing.lean` | 5 | 2 | 5 | 18 |
| `Matrix.GeneralLinearGroup.blockDiagonalUnit` | def | `general-linear-groups/GeneralLinearGroups/Whitehead.lean` | 4 | 3 | 25 | 28 |
| `ModuleCat.RightExtension.tmul` | def | `projective-modules/ProjectiveModules/Module/RightExtension.lean` | 4 | 3 | 225 | 304 |
| `RingedSpaces.Modules.BaseChange.pushPull` | def | `ringed-spaces/RingedSpaces/Modules/BaseChange.lean` | 4 | 1 | 20 | 38 |
| `TopCat.Sheaf.pullbackIdHom` | abbrev | `sheaf-cohomology/SheafCohomology/PullbackCoherence.lean` | 4 | 2 | 30 | 32 |
| `AlgebraicGeometry.IntegralDominantRationalSchemeOver.of` | def | `scheme-properties/SchemeProperties/IntegralDominantRationalCategoryOver.lean` | 3 | 1 | 8 | 8 |
| `AlgebraicGeometry.Scheme.Modules.tensorUnit` | def | `scheme-properties/SchemeProperties/ModuleTensor.lean` | 3 | 2 | 37 | 48 |
| `AlgebraicGeometry.SheafedSpace.NativeCylinderLimit.restrictedCone` | def | `sheaf-cohomology/SheafCohomology/NativeCylinderLimit.lean` | 3 | 3 | 34 | 35 |
| `AlgebraicGeometry.SheafedSpace.sheafMate` | def | `sheaf-cohomology/SheafCohomology/ConePullback.lean` | 3 | 3 | 88 | 102 |
| `AlgebraicGeometry.additiveGroupCoordinate` | def | `algebraic-groups/AlgebraicGroups/GroupScheme/Additive.lean` | 3 | 3 | 39 | 48 |
| `BalancedTensorProduct.smulAddHom` | def | `projective-modules/ProjectiveModules/Module/BalancedTensorProduct.lean` | 3 | 1 | 9 | 24 |
| `BalancedTensorProduct.smulBalancedMap` | def | `projective-modules/ProjectiveModules/Module/BalancedTensorProduct.lean` | 3 | 1 | 3 | 7 |
| `CentralPolynomialSimplex.fiberValue` | def | `simplicial-rings/SimplicialRings/CentralPolynomialSimplex.lean` | 3 | 1 | 7 | 21 |
| `GeneralLinearCoordinateRing.determinant` | def | `algebraic-groups/AlgebraicGroups/Algebra/GeneralLinearCoordinateRing.lean` | 3 | 3 | 44 | 70 |
| `Matrix.GeneralLinearGroup.elementaryUnit` | def | `general-linear-groups/GeneralLinearGroups/Elementary.lean` | 3 | 2 | 71 | 82 |
| `Profinite.stageHom` | abbrev | `profinite-groups/ProfiniteGroups/FiniteTargetHomColimit.lean` | 3 | 1 | 8 | 22 |

## Most unfolded outside its directory

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `UnitriangularCoordinateRing.relation` | def | `algebraic-groups/AlgebraicGroups/Algebra/UnitriangularCoordinateRing.lean` | 6 | 2 | 8 | 30 |
| `DiagonalCoordinateRing.relation` | def | `algebraic-groups/AlgebraicGroups/Algebra/DiagonalCoordinateRing.lean` | 5 | 2 | 5 | 18 |
| `UpperTriangularCoordinateRing.relation` | def | `algebraic-groups/AlgebraicGroups/Algebra/UpperTriangularCoordinateRing.lean` | 5 | 2 | 5 | 18 |
| `GeneralLinearCoordinateRing.determinant` | def | `algebraic-groups/AlgebraicGroups/Algebra/GeneralLinearCoordinateRing.lean` | 2 | 2 | 32 | 70 |
| `SpecialLinearCoordinateRing.determinantOneIdeal` | def | `algebraic-groups/AlgebraicGroups/Algebra/SpecialLinearCoordinateRing.lean` | 2 | 2 | 7 | 14 |
| `AlgebraicGeometry.additiveGroupCoordinate` | def | `algebraic-groups/AlgebraicGroups/GroupScheme/Additive.lean` | 1 | 1 | 7 | 48 |
| `DiagonalCoordinateRing.quotient` | def | `algebraic-groups/AlgebraicGroups/Algebra/DiagonalCoordinateRing.lean` | 1 | 1 | 49 | 62 |
| `GeneralLinearCoordinateRing.antipode` | def | `algebraic-groups/AlgebraicGroups/Algebra/GeneralLinearCoordinateRing.lean` | 1 | 1 | 2 | 5 |
| `GeneralLinearCoordinateRing.comul` | def | `algebraic-groups/AlgebraicGroups/Algebra/GeneralLinearCoordinateRing.lean` | 1 | 1 | 2 | 10 |
| `GeneralLinearCoordinateRing.counit` | def | `algebraic-groups/AlgebraicGroups/Algebra/GeneralLinearCoordinateRing.lean` | 1 | 1 | 2 | 12 |
| `SpecialLinearCoordinateRing.polynomialIdeal` | def | `algebraic-groups/AlgebraicGroups/Algebra/SpecialLinearCoordinateRing.lean` | 1 | 1 | 3 | 13 |
| `UpperTriangularCoordinateRing.quotient` | def | `algebraic-groups/AlgebraicGroups/Algebra/UpperTriangularCoordinateRing.lean` | 1 | 1 | 59 | 71 |

## Diagnostics

- ambiguous name: 63
- field notation: 2,605
- names declared in several files: 1
