# Explicit unfoldings of definitions: Mathlib (local checkout)

Backend: `source`. Source: `../mathlib4` at `e5f8f2fc1c03`.
Files scanned: 8,677.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (37,049 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 28,357 | 7,241 | 25.5% | 231,033 | 19,255 | 937 | 12,971 | 5,278 | 69 | 8.33 |
| outside file | 15,666 | 2,877 | 18.4% | 375,858 | 10,775 | 368 | 7,250 | 3,141 | 16 | 2.87 |
| outside directory | 10,639 | 1,704 | 16.0% | 251,045 | 6,265 | 188 | 4,225 | 1,845 | 7 | 2.50 |

## instance (12,154 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 1,488 | 38 | 2.6% | 1,960 | 80 | 6 | 49 | 25 | 0 | 4.08 |
| outside file | 1,161 | 33 | 2.8% | 2,857 | 60 | 13 | 32 | 15 | 0 | 2.10 |
| outside directory | 880 | 19 | 2.2% | 2,086 | 37 | 9 | 24 | 4 | 0 | 1.77 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ContinuousAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 125 | 67 | 1013 | 1013 |
| `Filter.EventuallyEq` | def | `Mathlib/Order/Filter/Defs.lean` | 112 | 65 | 124 | 126 |
| `Polynomial.leadingCoeff` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 97 | 41 | 262 | 282 |
| `iSup` | def | `Mathlib/Order/SetNotation.lean` | 87 | 45 | 411 | 414 |
| `dotProduct` | def | `Mathlib/Data/Matrix/Mul.lean` | 82 | 46 | 88 | 117 |
| `Function.onFun` | abbrev | `Mathlib/Logic/Function/Defs.lean` | 79 | 51 | 97 | 98 |
| `MeasureTheory.IntegrableOn` | def | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` | 72 | 34 | 626 | 802 |
| `ContinuousWithinAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 62 | 22 | 726 | 727 |
| `nhdsWithin` | def | `Mathlib/Topology/Defs/Filter.lean` | 59 | 30 | 74 | 80 |
| `Set.Nonempty` | def | `Mathlib/Data/Set/Defs.lean` | 56 | 42 | 909 | 909 |
| `Set.preimage` | def | `Mathlib/Data/Set/Operations.lean` | 53 | 34 | 123 | 124 |
| `Set.MapsTo` | def | `Mathlib/Data/Set/Operations.lean` | 51 | 36 | 846 | 850 |
| `EuclideanGeometry.angle` | def | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean` | 50 | 8 | 50 | 66 |
| `Set.uIcc` | def | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` | 50 | 18 | 310 | 344 |
| `Filter.Tendsto` | def | `Mathlib/Order/Filter/Defs.lean` | 49 | 26 | 4830 | 4830 |
| `SemiconjBy` | def | `Mathlib/Algebra/Group/Semigroup.lean` | 48 | 29 | 206 | 208 |
| `upperBounds` | def | `Mathlib/Order/Bounds/Defs.lean` | 48 | 35 | 206 | 208 |
| `Module.finrank` | def | `Mathlib/LinearAlgebra/Dimension/Finrank.lean` | 45 | 17 | 1904 | 1932 |
| `ENNReal.ofReal` | def | `Mathlib/Basic/ENNReal/Basic.lean` | 44 | 13 | 895 | 921 |
| `Matrix.mulVec` | def | `Mathlib/Data/Matrix/Mul.lean` | 44 | 31 | 66 | 76 |
| `Set.Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 44 | 28 | 202 | 213 |
| `Filter.Eventually` | def | `Mathlib/Order/Filter/Defs.lean` | 42 | 30 | 50 | 51 |
| `IsIdempotentElem` | def | `Mathlib/Algebra/Group/Idempotent.lean` | 41 | 22 | 246 | 271 |
| `UpperHalfPlane.denom` | def | `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` | 41 | 14 | 100 | 155 |
| `MeasureTheory.Measure.real` | def | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean` | 39 | 16 | 806 | 807 |
| `Polynomial.Monic` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 38 | 21 | 169 | 178 |
| `Finsupp.prod` | def | `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean` | 36 | 16 | 39 | 48 |
| `Nat.factorial` | def | `Mathlib/Data/Nat/Factorial/Basic.lean` | 36 | 16 | 255 | 259 |
| `Ideal.span` | abbrev | `Mathlib/RingTheory/Ideal/Span.lean` | 34 | 27 | 1143 | 1263 |
| `AlgebraicGeometry.Scheme.Hom.appLE` | def | `Mathlib/AlgebraicGeometry/Scheme.lean` | 33 | 11 | 57 | 81 |

## Most unfolded outside its directory

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ContinuousAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 125 | 67 | 1013 | 1013 |
| `Filter.EventuallyEq` | def | `Mathlib/Order/Filter/Defs.lean` | 106 | 62 | 112 | 126 |
| `Polynomial.leadingCoeff` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 83 | 37 | 167 | 282 |
| `Function.onFun` | abbrev | `Mathlib/Logic/Function/Defs.lean` | 79 | 51 | 90 | 98 |
| `dotProduct` | def | `Mathlib/Data/Matrix/Mul.lean` | 73 | 40 | 79 | 117 |
| `ContinuousWithinAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 62 | 22 | 726 | 727 |
| `nhdsWithin` | def | `Mathlib/Topology/Defs/Filter.lean` | 59 | 30 | 74 | 80 |
| `MeasureTheory.IntegrableOn` | def | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` | 54 | 25 | 368 | 802 |
| `Set.preimage` | def | `Mathlib/Data/Set/Operations.lean` | 52 | 33 | 102 | 124 |
| `Set.MapsTo` | def | `Mathlib/Data/Set/Operations.lean` | 51 | 36 | 687 | 850 |
| `Set.Nonempty` | def | `Mathlib/Data/Set/Defs.lean` | 47 | 36 | 805 | 909 |
| `Set.Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 44 | 28 | 202 | 213 |
| `upperBounds` | def | `Mathlib/Order/Bounds/Defs.lean` | 43 | 33 | 115 | 208 |
| `iSup` | def | `Mathlib/Order/SetNotation.lean` | 42 | 27 | 288 | 414 |
| `IsIdempotentElem` | def | `Mathlib/Algebra/Group/Idempotent.lean` | 41 | 22 | 245 | 271 |
| `Set.uIcc` | def | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` | 41 | 14 | 249 | 344 |
| `Matrix.mulVec` | def | `Mathlib/Data/Matrix/Mul.lean` | 38 | 26 | 59 | 76 |
| `Finsupp.prod` | def | `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean` | 36 | 16 | 39 | 48 |
| `Polynomial.Monic` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 36 | 19 | 160 | 178 |
| `Nat.factorial` | def | `Mathlib/Data/Nat/Factorial/Basic.lean` | 32 | 13 | 250 | 259 |
| `Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 32 | 21 | 396 | 423 |
| `Filter.Eventually` | def | `Mathlib/Order/Filter/Defs.lean` | 31 | 23 | 36 | 51 |
| `ClusterPt` | def | `Mathlib/Topology/Defs/Filter.lean` | 30 | 17 | 137 | 139 |
| `ContinuousOn` | def | `Mathlib/Topology/Defs/Filter.lean` | 30 | 15 | 1772 | 1772 |
| `Function.update` | def | `Mathlib/Logic/Function/Basic.lean` | 30 | 26 | 680 | 741 |
| `UpperHalfPlane.denom` | def | `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` | 30 | 10 | 68 | 155 |
| `Monotone` | def | `Mathlib/Order/Monotone/Defs.lean` | 28 | 16 | 1230 | 1322 |
| `Polynomial.IsRoot` | def | `Mathlib/Algebra/Polynomial/Eval/Defs.lean` | 28 | 17 | 150 | 187 |
| `SemiconjBy` | def | `Mathlib/Algebra/Group/Semigroup.lean` | 28 | 20 | 108 | 208 |
| `Filter.Tendsto` | def | `Mathlib/Order/Filter/Defs.lean` | 27 | 20 | 4199 | 4830 |

## Diagnostics

- ambiguous name: 3,896
- field notation: 97,713
- names declared in several files: 161
