# Source backend against the ilean reference: Mathlib (local build)

Reference: `runs/def-unfolds-2026-11-02/validation/mathlib-ilean` (ilean). Compared: `runs/def-unfolds-2026-11-02/validation/mathlib-source` (source).

7 files whose build index does not match the source are left out on both sides.

## Definitions

- found by both: 48,705
- only in the reference: 9
- only in the compared output: 465

Only in the reference (first 9): `CategoryTheory.CommGrpObj`, `IsAffineAddMonoid`, `IsAffineMonoid`, `Lists.Equiv.decidable`, `Lists.Subset.decidable`, `Lists.mem.decidable`, `Mathlib.Meta.FunProp.funProp`, `Tactic.ReduceModChar.normIntNumeral'`, `Tactic.ReduceModChar.normPow`

Only in the compared output (first 15): `Algebra.FormallySmooth.liftAdicCompletionAux`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.T`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.basis`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.basisLeft`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.basisRight`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.cotangentEquivProd`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.fhom`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.gbar`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.hom`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.kerGen`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.pres`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.presLeft`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.presRight`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentEquiv`, `Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentHom`

## Explicit unfoldings (definitions found by both)

| Category | Scope | Reference | Compared | Matched | Precision | Recall |
|---|---|---:|---:|---:|---:|---:|
| unfold | all | 1,317 | 1,319 | 1,310 | 99.3% | 99.5% |
| unfold | outside file | 378 | 381 | 377 | 99.0% | 99.7% |
| unfold | outside directory | 194 | 197 | 193 | 98.0% | 99.5% |
| simp | all | 20,283 | 20,191 | 20,094 | 99.5% | 99.1% |
| simp | outside file | 7,246 | 7,269 | 7,205 | 99.1% | 99.4% |
| simp | outside directory | 4,224 | 4,239 | 4,207 | 99.2% | 99.6% |
| rw | all | 8,455 | 8,415 | 8,415 | 100.0% | 99.5% |
| rw | outside file | 3,171 | 3,153 | 3,153 | 100.0% | 99.4% |
| rw | outside directory | 1,856 | 1,847 | 1,847 | 100.0% | 99.5% |
| eq_def | all | 75 | 85 | 71 | 83.5% | 94.7% |
| eq_def | outside file | 16 | 16 | 16 | 100.0% | 100.0% |
| eq_def | outside directory | 7 | 7 | 7 | 100.0% | 100.0% |
| all | all | 30,130 | 30,010 | 29,890 | 99.6% | 99.2% |
| all | outside file | 10,811 | 10,819 | 10,751 | 99.4% | 99.4% |
| all | outside directory | 6,281 | 6,290 | 6,254 | 99.4% | 99.6% |

Missed (in the reference only), first 15:

- `AddChar.zmod` at `Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean:60` (simp)
- `AdicCompletion.ofLinearEquiv` at `Mathlib/RingTheory/AdicCompletion/Basic.lean:853` (simp)
- `AdjoinRoot.root` at `Mathlib/RingTheory/AdjoinRoot.lean:303` (rw)
- `Algebra.trdeg` at `Mathlib/RingTheory/AlgebraicIndependent/Basic.lean:336` (rw)
- `Algebra.trdeg` at `Mathlib/RingTheory/AlgebraicIndependent/Basic.lean:346` (rw)
- `Algebra.trdeg` at `Mathlib/RingTheory/AlgebraicIndependent/Transcendental.lean:246` (rw)
- `AlgebraicGeometry.Scheme.IsLocallyDirected.V` at `Mathlib/AlgebraicGeometry/Gluing.lean:636` (simp)
- `AlgebraicGeometry.Scheme.IsLocallyDirected.tAux` at `Mathlib/AlgebraicGeometry/Gluing.lean:636` (simp)
- `AlgebraicGeometry.Scheme.Pullback.p2` at `Mathlib/AlgebraicGeometry/Pullbacks.lean:368` (rw)
- `AlgebraicGeometry.Scheme.Pullback.p2` at `Mathlib/AlgebraicGeometry/Pullbacks.lean:388` (simp)
- `AlgebraicGeometry.StructureSheaf.comapFun` at `Mathlib/AlgebraicGeometry/StructureSheaf.lean:1036` (simp)
- `AlgebraicGeometry.StructureSheaf.comapFun` at `Mathlib/AlgebraicGeometry/StructureSheaf.lean:1038` (simp)
- `AlgebraicGeometry.StructureSheaf.comapFun` at `Mathlib/AlgebraicGeometry/StructureSheaf.lean:1045` (simp)
- `AlgebraicGeometry.StructureSheaf.comapₗ` at `Mathlib/AlgebraicGeometry/StructureSheaf.lean:1045` (simp)
- `Bimod.TensorBimod.X` at `Mathlib/CategoryTheory/Monoidal/Bimod.lean:227` (simp)

Spurious (in the compared output only), first 15:

- `AbsoluteValue.trivial` at `Mathlib/Analysis/AbsoluteValue/Equivalence.lean:100` (simp)
- `AlgebraicGeometry.Scheme.Cover.pullbackHom` at `Mathlib/AlgebraicGeometry/Pullbacks.lean:626` (simp)
- `CategoryTheory.Bicategory.whiskerLeftIso` at `Mathlib/Tactic/CategoryTheory/Coherence.lean:221` (simp)
- `CategoryTheory.Bicategory.whiskerRightIso` at `Mathlib/Tactic/CategoryTheory/Coherence.lean:221` (simp)
- `CategoryTheory.Iso.refl` at `Mathlib/Tactic/CategoryTheory/Coherence.lean:219` (simp)
- `CategoryTheory.Iso.symm` at `Mathlib/Tactic/CategoryTheory/Coherence.lean:219` (simp)
- `CategoryTheory.Iso.trans` at `Mathlib/Tactic/CategoryTheory/Coherence.lean:219` (simp)
- `CategoryTheory.MonoidalCategory.whiskerLeftIso` at `Mathlib/Tactic/CategoryTheory/Coherence.lean:220` (simp)
- `CategoryTheory.MonoidalCategory.whiskerRightIso` at `Mathlib/Tactic/CategoryTheory/Coherence.lean:220` (simp)
- `CategoryTheory.MorphismProperty.RespectsIso.diagonal` at `Mathlib/CategoryTheory/MorphismProperty/Limits.lean:795` (unfold)
- `CategoryTheory.Quotient.Linear.smul` at `Mathlib/CategoryTheory/Quotient/Linear.lean:62` (simp)
- `CategoryTheory.Quotient.Linear.smul` at `Mathlib/CategoryTheory/Quotient/Linear.lean:66` (simp)
- `CategoryTheory.Quotient.Linear.smul` at `Mathlib/CategoryTheory/Quotient/Linear.lean:70` (simp)
- `CategoryTheory.Quotient.Linear.smul` at `Mathlib/CategoryTheory/Quotient/Linear.lean:75` (simp)
- `CategoryTheory.Quotient.Linear.smul` at `Mathlib/CategoryTheory/Quotient/Linear.lean:79` (simp)

## Uses (definitions found by both)

| Scope | Reference uses | Compared uses | Ratio | Spearman per definition |
|---|---:|---:|---:|---:|
| all | 739,128 | 609,272 | 0.824 | 0.941 |
| outside file | 478,903 | 378,389 | 0.790 | 0.932 |
| outside directory | 330,121 | 252,903 | 0.766 | 0.931 |

Individual uses, matched by definition, file and line:

| Scope | Reference | Compared | Matched | Precision | Recall |
|---|---:|---:|---:|---:|---:|
| all | 739,113 | 609,075 | 598,368 | 98.2% | 81.0% |
| outside file | 478,888 | 378,192 | 369,703 | 97.8% | 77.2% |
| outside directory | 330,109 | 252,708 | 246,564 | 97.6% | 74.7% |

Uses in the compared output only (every 713th of 10,707):

- `AEMeasurable` at `Mathlib/MeasureTheory/Function/ConditionalLExpectation.lean:165`
- `AlgebraicGeometry.Scheme.Γ` at `Mathlib/AlgebraicGeometry/Normalization.lean:622`
- `CategoryTheory.Lax.LaxTrans.whiskerLeft` at `Mathlib/CategoryTheory/Bicategory/FunctorBicategory/Lax.lean:102`
- `CategoryTheory.forget₂` at `Mathlib/Order/Category/BoolAlg.lean:175`
- `ContinuousLinearMap.apply` at `Mathlib/Geometry/Manifold/VectorField/Pullback.lean:299`
- `ContinuousMap.C` at `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean:155`
- `Filter.Tendsto` at `Mathlib/Probability/Process/LimitProcess.lean:167`
- `FundamentalGroupoid.map` at `Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean:319`
- `Mathlib.Meta.NormNum.eval` at `Mathlib/Tactic/NormNum/BigOperators.lean:388`
- `MeasurableSet` at `Mathlib/Probability/Independence/ZeroOne.lean:65`
- `MvPolynomial.X` at `Mathlib/Algebra/MvPolynomial/Equiv.lean:673`
- `Polynomial.coeff` at `Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean:500`
- `SSet.Truncated.Path.vertex` at `Mathlib/AlgebraicTopology/SimplicialSet/Path.lean:113`
- `Submodule.module` at `Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Semisimple.lean:89`
- `UniformSpace.Core.toTopologicalSpace` at `Mathlib/Topology/Algebra/Module/Spaces/UniformConvergenceCLM.lean:148`

Largest differences in total uses:

| Definition | Reference | Compared |
|---|---:|---:|
| `Equiv.symm` | 4493 | 20 |
| `Quiver.Hom.op` | 2384 | 54 |
| `CategoryTheory.Iso.symm` | 2105 | 55 |
| `LinearEquiv.symm` | 1954 | 21 |
| `Set.univ` | 3852 | 2405 |
| `Filter.atTop` | 3600 | 2222 |
| `Set.Nonempty` | 2218 | 909 |
| `ENNReal.toReal` | 1261 | 116 |
| `Quiver.Hom.unop` | 1156 | 17 |
| `CategoryTheory.Functor.op` | 1134 | 19 |
| `Polynomial.natDegree` | 1933 | 824 |
| `RingHom.comp` | 1143 | 82 |
| `Nat.Prime` | 1245 | 310 |
| `Set.Finite` | 1618 | 705 |
| `LinearMap.comp` | 937 | 34 |

## Library indicators (definitions found by both)

| Group | Where | Measure | Reference | Compared |
|---|---|---|---:|---:|
| def/abbrev | outside file | definitions used | 17277 | 15638 |
| def/abbrev | outside file | definitions unfolded | 2867 | 2872 |
| def/abbrev | outside file | share unfolded | 16.6% | 18.4% |
| def/abbrev | outside file | unfoldings | 10752 | 10761 |
| def/abbrev | outside file | unfoldings per 100 uses | 2.26 | 2.87 |
| def/abbrev | outside dir | definitions used | 11787 | 10618 |
| def/abbrev | outside dir | definitions unfolded | 1699 | 1701 |
| def/abbrev | outside dir | share unfolded | 14.4% | 16.0% |
| def/abbrev | outside dir | unfoldings | 6245 | 6255 |
| def/abbrev | outside dir | unfoldings per 100 uses | 1.90 | 2.49 |
| instance | outside file | definitions used | 1200 | 1161 |
| instance | outside file | definitions unfolded | 32 | 33 |
| instance | outside file | share unfolded | 2.7% | 2.8% |
| instance | outside file | unfoldings | 59 | 60 |
| instance | outside file | unfoldings per 100 uses | 2.14 | 2.10 |
| instance | outside dir | definitions used | 910 | 880 |
| instance | outside dir | definitions unfolded | 18 | 19 |
| instance | outside dir | share unfolded | 2.0% | 2.2% |
| instance | outside dir | unfoldings | 36 | 37 |
| instance | outside dir | unfoldings per 100 uses | 1.79 | 1.77 |
