# Source backend against the ilean reference: Mathlib

Reference: `runs/def-unfolds-2026-11-02/ilean/mathlib` (ilean). Compared: `runs/def-unfolds-2026-11-02/mathlib` (source).

## Definitions

- found by both: 45,998
- only in the reference: 6
- only in the compared output: 188

Only in the reference (first 6): `CategoryTheory.CommGrpObj`, `IsAffineAddMonoid`, `IsAffineMonoid`, `Lists.Equiv.decidable`, `Lists.Subset.decidable`, `Lists.mem.decidable`

Only in the compared output (first 15): `Algebra.FormallySmooth.liftAdicCompletionAux`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.T`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.basis`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.basisLeft`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.basisRight`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.cotangentEquivProd`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.fhom`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.gbar`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.hom`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.kerGen`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.pres`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.presLeft`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.presRight`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentEquiv`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentHom`

## Explicit unfoldings (definitions found by both)

| Category | Scope | Reference | Compared | Matched | Precision | Recall |
|---|---|---:|---:|---:|---:|---:|
| unfold | all | 1,303 | 1,305 | 1,296 | 99.3% | 99.5% |
| unfold | outside file | 380 | 383 | 379 | 99.0% | 99.7% |
| unfold | outside directory | 195 | 198 | 194 | 98.0% | 99.5% |
| simp | all | 19,873 | 19,770 | 19,685 | 99.6% | 99.1% |
| simp | outside file | 7,177 | 7,192 | 7,139 | 99.3% | 99.5% |
| simp | outside directory | 4,177 | 4,186 | 4,161 | 99.4% | 99.6% |
| rw | all | 8,291 | 8,251 | 8,251 | 100.0% | 99.5% |
| rw | outside file | 3,179 | 3,161 | 3,161 | 100.0% | 99.4% |
| rw | outside directory | 1,862 | 1,853 | 1,853 | 100.0% | 99.5% |
| eq_def | all | 75 | 71 | 71 | 100.0% | 94.7% |
| eq_def | outside file | 16 | 16 | 16 | 100.0% | 100.0% |
| eq_def | outside directory | 7 | 7 | 7 | 100.0% | 100.0% |
| all | all | 29,542 | 29,397 | 29,303 | 99.7% | 99.2% |
| all | outside file | 10,752 | 10,752 | 10,695 | 99.5% | 99.5% |
| all | outside directory | 6,241 | 6,244 | 6,215 | 99.5% | 99.6% |

Missed (in the reference only), first 15:

- `AddChar.zmod` at `Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean:57` (simp)
- `AdicCompletion.ofLinearEquiv` at `Mathlib/RingTheory/AdicCompletion/Basic.lean:853` (simp)
- `AdjoinRoot.root` at `Mathlib/RingTheory/AdjoinRoot.lean:303` (rw)
- `Algebra.trdeg` at `Mathlib/RingTheory/AlgebraicIndependent/Basic.lean:336` (rw)
- `Algebra.trdeg` at `Mathlib/RingTheory/AlgebraicIndependent/Basic.lean:346` (rw)
- `Algebra.trdeg` at `Mathlib/RingTheory/AlgebraicIndependent/Transcendental.lean:246` (rw)
- `AlgebraicGeometry.Scheme.IsLocallyDirected.V` at `Mathlib/AlgebraicGeometry/Gluing.lean:637` (simp)
- `AlgebraicGeometry.Scheme.IsLocallyDirected.tAux` at `Mathlib/AlgebraicGeometry/Gluing.lean:637` (simp)
- `AlgebraicGeometry.Scheme.Pullback.p2` at `Mathlib/AlgebraicGeometry/Pullbacks.lean:368` (rw)
- `AlgebraicGeometry.Scheme.Pullback.p2` at `Mathlib/AlgebraicGeometry/Pullbacks.lean:388` (simp)
- `AlgebraicGeometry.StructureSheaf.comapFun` at `Mathlib/AlgebraicGeometry/StructureSheaf.lean:1036` (simp)
- `AlgebraicGeometry.StructureSheaf.comapFun` at `Mathlib/AlgebraicGeometry/StructureSheaf.lean:1038` (simp)
- `AlgebraicGeometry.StructureSheaf.comapFun` at `Mathlib/AlgebraicGeometry/StructureSheaf.lean:1045` (simp)
- `AlgebraicGeometry.StructureSheaf.comapₗ` at `Mathlib/AlgebraicGeometry/StructureSheaf.lean:1045` (simp)
- `Bimod.TensorBimod.X` at `Mathlib/CategoryTheory/Monoidal/Bimod.lean:228` (simp)

Spurious (in the compared output only), first 15:

- `AbsoluteValue.trivial` at `Mathlib/Analysis/AbsoluteValue/Equivalence.lean:100` (simp)
- `AlgebraicGeometry.Scheme.Cover.pullbackHom` at `Mathlib/AlgebraicGeometry/Pullbacks.lean:626` (simp)
- `CategoryTheory.MorphismProperty.RespectsIso.diagonal` at `Mathlib/CategoryTheory/MorphismProperty/Limits.lean:800` (unfold)
- `CategoryTheory.Quotient.Linear.smul` at `Mathlib/CategoryTheory/Quotient/Linear.lean:62` (simp)
- `CategoryTheory.Quotient.Linear.smul` at `Mathlib/CategoryTheory/Quotient/Linear.lean:66` (simp)
- `CategoryTheory.Quotient.Linear.smul` at `Mathlib/CategoryTheory/Quotient/Linear.lean:70` (simp)
- `CategoryTheory.Quotient.Linear.smul` at `Mathlib/CategoryTheory/Quotient/Linear.lean:75` (simp)
- `CategoryTheory.Quotient.Linear.smul` at `Mathlib/CategoryTheory/Quotient/Linear.lean:79` (simp)
- `ChevalleyThm.degBound` at `Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean:292` (unfold)
- `ChevalleyThm.degBound` at `Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean:296` (unfold)
- `Filter.instInfSet` at `Mathlib/Probability/Process/Filtration.lean:184` (simp)
- `FilterBasis.filter` at `Mathlib/Order/Filter/Bases/Basic.lean:181` (simp)
- `Finset.Nonempty` at `Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean:1038` (simp)
- `Finset.Nonempty` at `Mathlib/Combinatorics/Additive/Convolution.lean:75` (simp)
- `Finset.Nonempty` at `Mathlib/Data/Finset/Powerset.lean:292` (simp)

## Uses (definitions found by both)

| Scope | Reference uses | Compared uses | Ratio | Spearman per definition |
|---|---:|---:|---:|---:|
| all | 716,484 | 592,333 | 0.827 | 0.950 |
| outside file | 465,037 | 368,456 | 0.792 | 0.938 |
| outside directory | 320,949 | 246,750 | 0.769 | 0.935 |

Individual uses, matched by definition, file and line:

| Scope | Reference | Compared | Matched | Precision | Recall |
|---|---:|---:|---:|---:|---:|
| all | 716,484 | 592,333 | 582,256 | 98.3% | 81.3% |
| outside file | 465,037 | 368,456 | 360,386 | 97.8% | 77.5% |
| outside directory | 320,949 | 246,750 | 240,905 | 97.6% | 75.1% |

Uses in the compared output only (every 671th of 10,077):

- `AEMeasurable` at `Mathlib/MeasureTheory/Function/ConditionalLExpectation.lean:165`
- `AlgebraicGeometry.Scheme.Γ` at `Mathlib/AlgebraicGeometry/Normalization.lean:107`
- `CategoryTheory.GradedObject.map` at `Mathlib/CategoryTheory/GradedObject.lean:76`
- `CategoryTheory.asIso` at `Mathlib/CategoryTheory/Galois/IsFundamentalgroup.lean:114`
- `ContinuousLinearMap.apply` at `Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:340`
- `ContinuousMap.C` at `Mathlib/Topology/ContinuousMap/Algebra.lean:537`
- `EquivLike.toEquiv` at `Mathlib/Data/Fintype/Sort.lean:42`
- `Function.invFun` at `Mathlib/Data/ZMod/Basic.lean:878`
- `LinearEquiv.toAffineEquiv` at `Mathlib/Analysis/Normed/Affine/Isometry.lean:422`
- `MeasurableSet` at `Mathlib/Probability/Process/Stopping.lean:730`
- `MvPowerSeries.pderiv` at `Mathlib/RingTheory/MvPowerSeries/Derivative.lean:83`
- `Polynomial.ring` at `Mathlib/Analysis/Polynomial/Order.lean:91`
- `SSet.nonDegenerate` at `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/PairingCore.lean:72`
- `Submodule.smul` at `Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Basic.lean:408`
- `UniformSpace.Completion` at `Mathlib/Topology/Algebra/Valued/WithVal.lean:616`

Largest differences in total uses:

| Definition | Reference | Compared |
|---|---:|---:|
| `Equiv.symm` | 4490 | 19 |
| `Quiver.Hom.op` | 2384 | 54 |
| `CategoryTheory.Iso.symm` | 2084 | 48 |
| `LinearEquiv.symm` | 1953 | 21 |
| `Set.univ` | 3845 | 2402 |
| `Filter.atTop` | 3499 | 2161 |
| `Set.Nonempty` | 2205 | 903 |
| `Quiver.Hom.unop` | 1156 | 17 |
| `ENNReal.toReal` | 1253 | 116 |
| `CategoryTheory.Functor.op` | 1134 | 19 |
| `Polynomial.natDegree` | 1913 | 808 |
| `RingHom.comp` | 1140 | 80 |
| `Nat.Prime` | 1228 | 302 |
| `Set.Finite` | 1616 | 709 |
| `LinearMap.comp` | 928 | 34 |

## Library indicators (definitions found by both)

| Group | Where | Measure | Reference | Compared |
|---|---|---|---:|---:|
| def/abbrev | outside file | definitions used | 16431 | 15006 |
| def/abbrev | outside file | definitions unfolded | 2857 | 2858 |
| def/abbrev | outside file | share unfolded | 17.4% | 19.0% |
| def/abbrev | outside file | unfoldings | 10693 | 10692 |
| def/abbrev | outside file | unfoldings per 100 uses | 2.31 | 2.92 |
| def/abbrev | outside dir | definitions used | 11291 | 10234 |
| def/abbrev | outside dir | definitions unfolded | 1688 | 1686 |
| def/abbrev | outside dir | share unfolded | 14.9% | 16.5% |
| def/abbrev | outside dir | unfoldings | 6205 | 6207 |
| def/abbrev | outside dir | unfoldings per 100 uses | 1.95 | 2.54 |
| instance | outside file | definitions used | 1187 | 1147 |
| instance | outside file | definitions unfolded | 32 | 33 |
| instance | outside file | share unfolded | 2.7% | 2.9% |
| instance | outside file | unfoldings | 59 | 60 |
| instance | outside file | unfoldings per 100 uses | 2.17 | 2.14 |
| instance | outside dir | definitions used | 897 | 866 |
| instance | outside dir | definitions unfolded | 18 | 19 |
| instance | outside dir | share unfolded | 2.0% | 2.2% |
| instance | outside dir | unfoldings | 36 | 37 |
| instance | outside dir | unfoldings per 100 uses | 1.82 | 1.82 |
