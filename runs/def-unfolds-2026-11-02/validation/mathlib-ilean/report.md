# Explicit unfoldings of definitions: Mathlib (local build)

Backend: `ilean`. Source: `../mathlib4` at `e5f8f2fc1c03`.
Files scanned: 8,878.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (36,605 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 29,609 | 7,215 | 24.4% | 258,409 | 19,244 | 934 | 12,992 | 5,259 | 59 | 7.45 |
| outside file | 17,295 | 2,870 | 16.6% | 476,303 | 10,756 | 365 | 7,218 | 3,157 | 16 | 2.26 |
| outside directory | 11,800 | 1,700 | 14.4% | 328,187 | 6,246 | 185 | 4,202 | 1,852 | 7 | 1.90 |

## instance (12,137 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 1,427 | 37 | 2.6% | 1,904 | 79 | 5 | 49 | 25 | 0 | 4.15 |
| outside file | 1,200 | 32 | 2.7% | 2,755 | 59 | 13 | 31 | 15 | 0 | 2.14 |
| outside directory | 910 | 18 | 2.0% | 2,011 | 36 | 9 | 23 | 4 | 0 | 1.79 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ContinuousAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 125 | 67 | 1015 | 1015 |
| `Filter.EventuallyEq` | def | `Mathlib/Order/Filter/Defs.lean` | 112 | 65 | 124 | 126 |
| `Polynomial.leadingCoeff` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 97 | 41 | 754 | 781 |
| `iSup` | def | `Mathlib/Order/SetNotation.lean` | 89 | 46 | 430 | 433 |
| `dotProduct` | def | `Mathlib/Data/Matrix/Mul.lean` | 82 | 46 | 88 | 117 |
| `Function.onFun` | abbrev | `Mathlib/Logic/Function/Defs.lean` | 78 | 50 | 104 | 106 |
| `MeasureTheory.IntegrableOn` | def | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` | 72 | 34 | 626 | 802 |
| `ContinuousWithinAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 62 | 22 | 728 | 729 |
| `nhdsWithin` | def | `Mathlib/Topology/Defs/Filter.lean` | 59 | 30 | 71 | 77 |
| `Set.preimage` | def | `Mathlib/Data/Set/Operations.lean` | 55 | 36 | 134 | 135 |
| `Set.Nonempty` | def | `Mathlib/Data/Set/Defs.lean` | 54 | 41 | 2218 | 2218 |
| `EuclideanGeometry.angle` | def | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean` | 50 | 8 | 50 | 65 |
| `Filter.Tendsto` | def | `Mathlib/Order/Filter/Defs.lean` | 50 | 27 | 4895 | 4895 |
| `Set.uIcc` | def | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` | 50 | 18 | 313 | 347 |
| `Set.MapsTo` | def | `Mathlib/Data/Set/Operations.lean` | 49 | 35 | 854 | 858 |
| `SemiconjBy` | def | `Mathlib/Algebra/Group/Semigroup.lean` | 48 | 29 | 206 | 208 |
| `upperBounds` | def | `Mathlib/Order/Bounds/Defs.lean` | 46 | 35 | 205 | 207 |
| `Module.finrank` | def | `Mathlib/LinearAlgebra/Dimension/Finrank.lean` | 45 | 17 | 1960 | 1988 |
| `ENNReal.ofReal` | def | `Mathlib/Basic/ENNReal/Basic.lean` | 44 | 13 | 1048 | 1074 |
| `Matrix.mulVec` | def | `Mathlib/Data/Matrix/Mul.lean` | 44 | 31 | 76 | 90 |
| `Filter.Eventually` | def | `Mathlib/Order/Filter/Defs.lean` | 42 | 30 | 50 | 52 |
| `UpperHalfPlane.denom` | def | `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` | 42 | 14 | 102 | 157 |
| `IsIdempotentElem` | def | `Mathlib/Algebra/Group/Idempotent.lean` | 41 | 22 | 246 | 271 |
| `Set.Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 40 | 26 | 308 | 319 |
| `MeasureTheory.Measure.real` | def | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean` | 39 | 16 | 827 | 828 |
| `Polynomial.Monic` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 38 | 21 | 499 | 512 |
| `Finsupp.prod` | def | `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean` | 36 | 16 | 212 | 298 |
| `Nat.factorial` | def | `Mathlib/Data/Nat/Factorial/Basic.lean` | 36 | 16 | 274 | 279 |
| `Ideal.span` | abbrev | `Mathlib/RingTheory/Ideal/Span.lean` | 34 | 27 | 1225 | 1345 |
| `AlgebraicGeometry.Scheme.Hom.appLE` | def | `Mathlib/AlgebraicGeometry/Scheme.lean` | 33 | 11 | 174 | 198 |

## Most unfolded outside its directory

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ContinuousAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 125 | 67 | 1015 | 1015 |
| `Filter.EventuallyEq` | def | `Mathlib/Order/Filter/Defs.lean` | 106 | 62 | 112 | 126 |
| `Polynomial.leadingCoeff` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 83 | 37 | 614 | 781 |
| `Function.onFun` | abbrev | `Mathlib/Logic/Function/Defs.lean` | 78 | 50 | 97 | 106 |
| `dotProduct` | def | `Mathlib/Data/Matrix/Mul.lean` | 73 | 40 | 79 | 117 |
| `ContinuousWithinAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 62 | 22 | 728 | 729 |
| `nhdsWithin` | def | `Mathlib/Topology/Defs/Filter.lean` | 59 | 30 | 71 | 77 |
| `MeasureTheory.IntegrableOn` | def | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` | 54 | 25 | 368 | 802 |
| `Set.preimage` | def | `Mathlib/Data/Set/Operations.lean` | 53 | 34 | 112 | 135 |
| `Set.MapsTo` | def | `Mathlib/Data/Set/Operations.lean` | 49 | 35 | 693 | 858 |
| `Set.Nonempty` | def | `Mathlib/Data/Set/Defs.lean` | 46 | 36 | 1957 | 2218 |
| `iSup` | def | `Mathlib/Order/SetNotation.lean` | 44 | 28 | 307 | 433 |
| `upperBounds` | def | `Mathlib/Order/Bounds/Defs.lean` | 42 | 33 | 114 | 207 |
| `IsIdempotentElem` | def | `Mathlib/Algebra/Group/Idempotent.lean` | 41 | 22 | 245 | 271 |
| `Set.uIcc` | def | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` | 41 | 14 | 252 | 347 |
| `Set.Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 40 | 26 | 308 | 319 |
| `Matrix.mulVec` | def | `Mathlib/Data/Matrix/Mul.lean` | 38 | 26 | 69 | 90 |
| `Finsupp.prod` | def | `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean` | 36 | 16 | 212 | 298 |
| `Polynomial.Monic` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 36 | 19 | 479 | 512 |
| `Nat.factorial` | def | `Mathlib/Data/Nat/Factorial/Basic.lean` | 32 | 13 | 268 | 279 |
| `Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 32 | 21 | 410 | 437 |
| `ContinuousOn` | def | `Mathlib/Topology/Defs/Filter.lean` | 31 | 15 | 1775 | 1775 |
| `Filter.Eventually` | def | `Mathlib/Order/Filter/Defs.lean` | 31 | 23 | 36 | 52 |
| `UpperHalfPlane.denom` | def | `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` | 31 | 10 | 69 | 157 |
| `ClusterPt` | def | `Mathlib/Topology/Defs/Filter.lean` | 30 | 17 | 138 | 140 |
| `Function.update` | def | `Mathlib/Logic/Function/Basic.lean` | 29 | 25 | 701 | 762 |
| `Polynomial.IsRoot` | def | `Mathlib/Algebra/Polynomial/Eval/Defs.lean` | 29 | 18 | 156 | 193 |
| `Filter.Tendsto` | def | `Mathlib/Order/Filter/Defs.lean` | 28 | 21 | 4262 | 4895 |
| `Monotone` | def | `Mathlib/Order/Monotone/Defs.lean` | 28 | 16 | 1231 | 1324 |
| `SemiconjBy` | def | `Mathlib/Algebra/Group/Semigroup.lean` | 28 | 20 | 108 | 208 |

## Diagnostics

- declaration range not on its name: 17,444
- definition found through its references: 261
- module without source: 203
- use range not on the name (notation or stale): 20,525
