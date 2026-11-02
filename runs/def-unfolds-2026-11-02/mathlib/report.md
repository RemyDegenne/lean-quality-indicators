# Explicit unfoldings of definitions: Mathlib

Backend: `source`. Source: `repos/mathlib` at `e3e75e86143b`.
Files scanned: 8,175.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (34,098 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 26,607 | 7,065 | 26.6% | 223,096 | 18,677 | 921 | 12,610 | 5,091 | 55 | 8.37 |
| outside file | 15,006 | 2,858 | 19.0% | 365,655 | 10,692 | 370 | 7,160 | 3,146 | 16 | 2.92 |
| outside directory | 10,234 | 1,686 | 16.5% | 244,719 | 6,207 | 189 | 4,162 | 1,849 | 7 | 2.54 |

## instance (12,088 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 1,484 | 38 | 2.6% | 1,955 | 80 | 6 | 49 | 25 | 0 | 4.09 |
| outside file | 1,147 | 33 | 2.9% | 2,801 | 60 | 13 | 32 | 15 | 0 | 2.14 |
| outside directory | 866 | 19 | 2.2% | 2,031 | 37 | 9 | 24 | 4 | 0 | 1.82 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ContinuousAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 125 | 67 | 1013 | 1013 |
| `Filter.EventuallyEq` | def | `Mathlib/Order/Filter/Defs.lean` | 112 | 65 | 124 | 126 |
| `Polynomial.leadingCoeff` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 97 | 41 | 262 | 282 |
| `iSup` | def | `Mathlib/Order/SetNotation.lean` | 88 | 46 | 412 | 415 |
| `dotProduct` | def | `Mathlib/Data/Matrix/Mul.lean` | 82 | 46 | 88 | 117 |
| `Function.onFun` | abbrev | `Mathlib/Logic/Function/Defs.lean` | 79 | 51 | 97 | 98 |
| `MeasureTheory.IntegrableOn` | def | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` | 72 | 34 | 624 | 800 |
| `ContinuousWithinAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 63 | 23 | 725 | 726 |
| `Set.preimage` | def | `Mathlib/Data/Set/Operations.lean` | 61 | 36 | 131 | 132 |
| `nhdsWithin` | def | `Mathlib/Topology/Defs/Filter.lean` | 57 | 30 | 72 | 78 |
| `Set.Nonempty` | def | `Mathlib/Data/Set/Defs.lean` | 56 | 42 | 903 | 903 |
| `Set.MapsTo` | def | `Mathlib/Data/Set/Operations.lean` | 51 | 36 | 846 | 850 |
| `EuclideanGeometry.angle` | def | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean` | 50 | 8 | 50 | 66 |
| `Set.uIcc` | def | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` | 50 | 18 | 307 | 341 |
| `SemiconjBy` | def | `Mathlib/Algebra/Group/Semigroup.lean` | 48 | 29 | 206 | 208 |
| `upperBounds` | def | `Mathlib/Order/Bounds/Defs.lean` | 47 | 34 | 205 | 207 |
| `Filter.Tendsto` | def | `Mathlib/Order/Filter/Defs.lean` | 46 | 25 | 4770 | 4770 |
| `ENNReal.ofReal` | def | `Mathlib/Basic/ENNReal/Basic.lean` | 44 | 13 | 894 | 920 |
| `Matrix.mulVec` | def | `Mathlib/Data/Matrix/Mul.lean` | 44 | 31 | 66 | 76 |
| `Set.Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 44 | 28 | 202 | 213 |
| `Module.finrank` | def | `Mathlib/LinearAlgebra/Dimension/Finrank.lean` | 43 | 16 | 1873 | 1901 |
| `Filter.Eventually` | def | `Mathlib/Order/Filter/Defs.lean` | 42 | 30 | 48 | 49 |
| `IsIdempotentElem` | def | `Mathlib/Algebra/Group/Idempotent.lean` | 41 | 22 | 246 | 271 |
| `MeasureTheory.Measure.real` | def | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean` | 39 | 16 | 806 | 807 |
| `UpperHalfPlane.denom` | def | `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` | 39 | 13 | 98 | 153 |
| `Polynomial.Monic` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 38 | 21 | 169 | 178 |
| `Finsupp.prod` | def | `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean` | 36 | 16 | 39 | 48 |
| `Nat.factorial` | def | `Mathlib/Data/Nat/Factorial/Basic.lean` | 36 | 16 | 249 | 253 |
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
| `ContinuousWithinAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 63 | 23 | 725 | 726 |
| `Set.preimage` | def | `Mathlib/Data/Set/Operations.lean` | 60 | 35 | 110 | 132 |
| `nhdsWithin` | def | `Mathlib/Topology/Defs/Filter.lean` | 57 | 30 | 72 | 78 |
| `MeasureTheory.IntegrableOn` | def | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` | 54 | 25 | 366 | 800 |
| `Set.MapsTo` | def | `Mathlib/Data/Set/Operations.lean` | 51 | 36 | 687 | 850 |
| `Set.Nonempty` | def | `Mathlib/Data/Set/Defs.lean` | 47 | 36 | 799 | 903 |
| `Set.Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 44 | 28 | 202 | 213 |
| `iSup` | def | `Mathlib/Order/SetNotation.lean` | 42 | 27 | 288 | 415 |
| `upperBounds` | def | `Mathlib/Order/Bounds/Defs.lean` | 42 | 32 | 114 | 207 |
| `IsIdempotentElem` | def | `Mathlib/Algebra/Group/Idempotent.lean` | 41 | 22 | 245 | 271 |
| `Set.uIcc` | def | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` | 41 | 14 | 246 | 341 |
| `Matrix.mulVec` | def | `Mathlib/Data/Matrix/Mul.lean` | 38 | 26 | 59 | 76 |
| `Finsupp.prod` | def | `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean` | 36 | 16 | 39 | 48 |
| `Polynomial.Monic` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 36 | 19 | 160 | 178 |
| `Nat.factorial` | def | `Mathlib/Data/Nat/Factorial/Basic.lean` | 32 | 13 | 244 | 253 |
| `Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 32 | 21 | 395 | 422 |
| `Filter.Eventually` | def | `Mathlib/Order/Filter/Defs.lean` | 31 | 23 | 34 | 49 |
| `ClusterPt` | def | `Mathlib/Topology/Defs/Filter.lean` | 30 | 17 | 137 | 139 |
| `ContinuousOn` | def | `Mathlib/Topology/Defs/Filter.lean` | 30 | 15 | 1757 | 1757 |
| `Function.update` | def | `Mathlib/Logic/Function/Basic.lean` | 30 | 26 | 680 | 741 |
| `Monotone` | def | `Mathlib/Order/Monotone/Defs.lean` | 28 | 16 | 1227 | 1319 |
| `Polynomial.IsRoot` | def | `Mathlib/Algebra/Polynomial/Eval/Defs.lean` | 28 | 17 | 144 | 181 |
| `SemiconjBy` | def | `Mathlib/Algebra/Group/Semigroup.lean` | 28 | 20 | 108 | 208 |
| `UpperHalfPlane.denom` | def | `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` | 28 | 9 | 66 | 153 |
| `Function.Bijective` | def | `Mathlib/Logic/Function/Defs.lean` | 27 | 19 | 859 | 900 |

## Diagnostics

- ambiguous name: 3,833
- field notation: 94,133
- names declared in several files: 159
