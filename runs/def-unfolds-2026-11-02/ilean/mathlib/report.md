# Explicit unfoldings of definitions: Mathlib

Backend: `ilean`. Source: `repos/mathlib` at `e3e75e86143b`.
Files scanned: 8,175.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (33,931 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 27,691 | 7,047 | 25.4% | 249,553 | 18,711 | 918 | 12,647 | 5,087 | 59 | 7.50 |
| outside file | 16,432 | 2,857 | 17.4% | 462,321 | 10,693 | 367 | 7,146 | 3,164 | 16 | 2.31 |
| outside directory | 11,292 | 1,688 | 14.9% | 318,976 | 6,205 | 186 | 4,154 | 1,858 | 7 | 1.95 |

## instance (12,073 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 1,428 | 37 | 2.6% | 1,905 | 79 | 5 | 49 | 25 | 0 | 4.15 |
| outside file | 1,187 | 32 | 2.7% | 2,717 | 59 | 13 | 31 | 15 | 0 | 2.17 |
| outside directory | 897 | 18 | 2.0% | 1,974 | 36 | 9 | 23 | 4 | 0 | 1.82 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ContinuousAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 125 | 67 | 1015 | 1015 |
| `Filter.EventuallyEq` | def | `Mathlib/Order/Filter/Defs.lean` | 112 | 65 | 124 | 126 |
| `Polynomial.leadingCoeff` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 97 | 41 | 754 | 781 |
| `iSup` | def | `Mathlib/Order/SetNotation.lean` | 90 | 47 | 431 | 434 |
| `dotProduct` | def | `Mathlib/Data/Matrix/Mul.lean` | 82 | 46 | 88 | 117 |
| `Function.onFun` | abbrev | `Mathlib/Logic/Function/Defs.lean` | 78 | 50 | 104 | 106 |
| `MeasureTheory.IntegrableOn` | def | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` | 72 | 34 | 624 | 800 |
| `ContinuousWithinAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 63 | 23 | 727 | 728 |
| `Set.preimage` | def | `Mathlib/Data/Set/Operations.lean` | 63 | 38 | 142 | 143 |
| `nhdsWithin` | def | `Mathlib/Topology/Defs/Filter.lean` | 57 | 30 | 69 | 75 |
| `Set.Nonempty` | def | `Mathlib/Data/Set/Defs.lean` | 54 | 41 | 2205 | 2205 |
| `EuclideanGeometry.angle` | def | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean` | 50 | 8 | 50 | 65 |
| `Set.uIcc` | def | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` | 50 | 18 | 310 | 344 |
| `Set.MapsTo` | def | `Mathlib/Data/Set/Operations.lean` | 49 | 35 | 854 | 858 |
| `SemiconjBy` | def | `Mathlib/Algebra/Group/Semigroup.lean` | 48 | 29 | 206 | 208 |
| `Filter.Tendsto` | def | `Mathlib/Order/Filter/Defs.lean` | 47 | 26 | 4843 | 4843 |
| `upperBounds` | def | `Mathlib/Order/Bounds/Defs.lean` | 45 | 34 | 204 | 206 |
| `ENNReal.ofReal` | def | `Mathlib/Basic/ENNReal/Basic.lean` | 44 | 13 | 1047 | 1073 |
| `Matrix.mulVec` | def | `Mathlib/Data/Matrix/Mul.lean` | 44 | 31 | 76 | 90 |
| `Module.finrank` | def | `Mathlib/LinearAlgebra/Dimension/Finrank.lean` | 43 | 16 | 1929 | 1957 |
| `Filter.Eventually` | def | `Mathlib/Order/Filter/Defs.lean` | 42 | 30 | 48 | 50 |
| `IsIdempotentElem` | def | `Mathlib/Algebra/Group/Idempotent.lean` | 41 | 22 | 246 | 271 |
| `Set.Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 40 | 26 | 308 | 319 |
| `UpperHalfPlane.denom` | def | `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` | 40 | 13 | 100 | 155 |
| `MeasureTheory.Measure.real` | def | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean` | 39 | 16 | 827 | 828 |
| `Polynomial.Monic` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 38 | 21 | 499 | 512 |
| `Finsupp.prod` | def | `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean` | 36 | 16 | 211 | 297 |
| `Nat.factorial` | def | `Mathlib/Data/Nat/Factorial/Basic.lean` | 36 | 16 | 266 | 271 |
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
| `ContinuousWithinAt` | def | `Mathlib/Topology/Defs/Filter.lean` | 63 | 23 | 727 | 728 |
| `Set.preimage` | def | `Mathlib/Data/Set/Operations.lean` | 61 | 36 | 120 | 143 |
| `nhdsWithin` | def | `Mathlib/Topology/Defs/Filter.lean` | 57 | 30 | 69 | 75 |
| `MeasureTheory.IntegrableOn` | def | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` | 54 | 25 | 366 | 800 |
| `Set.MapsTo` | def | `Mathlib/Data/Set/Operations.lean` | 49 | 35 | 693 | 858 |
| `Set.Nonempty` | def | `Mathlib/Data/Set/Defs.lean` | 46 | 36 | 1944 | 2205 |
| `iSup` | def | `Mathlib/Order/SetNotation.lean` | 44 | 28 | 307 | 434 |
| `IsIdempotentElem` | def | `Mathlib/Algebra/Group/Idempotent.lean` | 41 | 22 | 245 | 271 |
| `Set.uIcc` | def | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` | 41 | 14 | 249 | 344 |
| `upperBounds` | def | `Mathlib/Order/Bounds/Defs.lean` | 41 | 32 | 113 | 206 |
| `Set.Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 40 | 26 | 308 | 319 |
| `Matrix.mulVec` | def | `Mathlib/Data/Matrix/Mul.lean` | 38 | 26 | 69 | 90 |
| `Finsupp.prod` | def | `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean` | 36 | 16 | 211 | 297 |
| `Polynomial.Monic` | def | `Mathlib/Algebra/Polynomial/Degree/Defs.lean` | 36 | 19 | 479 | 512 |
| `Nat.factorial` | def | `Mathlib/Data/Nat/Factorial/Basic.lean` | 32 | 13 | 260 | 271 |
| `Pairwise` | def | `Mathlib/Logic/Pairwise.lean` | 32 | 21 | 409 | 436 |
| `ContinuousOn` | def | `Mathlib/Topology/Defs/Filter.lean` | 31 | 15 | 1760 | 1760 |
| `Filter.Eventually` | def | `Mathlib/Order/Filter/Defs.lean` | 31 | 23 | 34 | 50 |
| `ClusterPt` | def | `Mathlib/Topology/Defs/Filter.lean` | 30 | 17 | 138 | 140 |
| `Function.update` | def | `Mathlib/Logic/Function/Basic.lean` | 29 | 25 | 701 | 762 |
| `Polynomial.IsRoot` | def | `Mathlib/Algebra/Polynomial/Eval/Defs.lean` | 29 | 18 | 150 | 187 |
| `UpperHalfPlane.denom` | def | `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` | 29 | 9 | 67 | 155 |
| `Monotone` | def | `Mathlib/Order/Monotone/Defs.lean` | 28 | 16 | 1228 | 1321 |
| `SemiconjBy` | def | `Mathlib/Algebra/Group/Semigroup.lean` | 28 | 20 | 108 | 208 |
| `Function.Bijective` | def | `Mathlib/Logic/Function/Defs.lean` | 27 | 19 | 868 | 909 |

## Diagnostics

- declaration range not on its name: 17,296
- definition found through its references: 253
- use range not on the name (notation or stale): 20,116
