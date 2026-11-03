# Compression ratio, by library

[compression.py](../../scripts/compression.py) on the files of each library, in the scope of the other audits. Ratio = original size / compressed size (zstd level 19); higher means more repetitive. *Code only*: comments and string literals removed, then trailing spaces and blank lines. Chunks: the files concatenated in path order, cut into chunks of a fixed size, each compressed alone; these ratios do not depend on the library's size, unlike the whole-library one.

## Source as is

| Library | Files | MB | Per file | 64 KB chunks | 1 MB chunks | 8 MB chunks | Whole library | Compressed MB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | 8,175 | 95.2 | 3.83 | 4.47 | 5.47 | 5.94 | 6.17 | 15.4 |
| Tau Ceti | 16,726 | 177.0 | 3.64 | 4.59 | 5.86 | 6.42 | 6.65 | 26.6 |
| Lean Pool | 21,182 | 360.4 | 5.05 | 5.75 | 7.39 | 8.01 | 8.39 | 43.0 |
| FLT (Anthropic) | 30,962 | 895.1 | 5.41 | 5.78 | 9.89 | 12.74 | 16.03 | 55.8 |
| Formal Frontier | 1,342 | 13.8 | 4.06 | 5.05 | 6.26 | 6.67 | 6.90 | 2.0 |
| OpenAI Math | 121,797 | 1,485.5 | 5.27 | 6.29 | 8.15 | 9.05 | 9.72 | 152.8 |
| CFSG (AxiomMath) | 194,203 | 1,958.8 | 3.80 | 4.69 | 6.02 | 6.72 | 7.34 | 266.7 |

## Code only

| Library | Files | MB | Per file | 64 KB chunks | 1 MB chunks | 8 MB chunks | Whole library | Compressed MB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | 8,175 | 75.8 | 4.08 | 4.81 | 5.77 | 6.19 | 6.39 | 11.9 |
| Tau Ceti | 16,726 | 110.5 | 4.05 | 5.46 | 6.80 | 7.38 | 7.60 | 14.5 |
| Lean Pool | 21,182 | 314.3 | 5.77 | 6.53 | 8.35 | 9.02 | 9.41 | 33.4 |
| FLT (Anthropic) | 30,962 | 851.4 | 5.20 | 5.62 | 9.64 | 12.36 | 15.56 | 54.7 |
| Formal Frontier | 1,342 | 10.8 | 4.64 | 5.88 | 7.20 | 7.62 | 7.72 | 1.4 |
| OpenAI Math | 121,797 | 1,464.6 | 5.37 | 6.41 | 8.31 | 9.23 | 9.89 | 148.0 |
| CFSG (AxiomMath) | 194,203 | 1,922.9 | 3.83 | 4.76 | 6.16 | 6.89 | 7.56 | 254.3 |

## Spread across 1 MB chunks (code only)

| Library | Chunks | 10th percentile | Median | 90th percentile |
|---|---:|---:|---:|---:|
| Mathlib | 72 | 5.29 | 5.69 | 6.54 |
| Tau Ceti | 105 | 5.92 | 6.81 | 7.85 |
| Lean Pool | 299 | 6.38 | 7.72 | 18.93 |
| FLT (Anthropic) | 811 | 7.08 | 9.46 | 15.84 |
| Formal Frontier | 10 | 6.66 | 7.12 | 8.79 |
| OpenAI Math | 1,396 | 5.73 | 7.09 | 28.08 |
| CFSG (AxiomMath) | 1,833 | 5.60 | 6.14 | 7.14 |

## Other measures

*Lines in another file*: share of the code lines (at least 40 characters once stripped, other than `import`, `set_option` and `open` lines) that occur verbatim in another file of the library.

| Library | Code lines counted | Lines in another file | Comments and blank lines (share of bytes) | Identical files |
|---|---:|---:|---:|---:|
| Mathlib | 786,512 | 3.8% | 20.4% | 0 |
| Tau Ceti | 1,216,592 | 10.5% | 37.6% | 0 |
| Lean Pool | 3,211,352 | 20.1% | 12.8% | 0 |
| FLT (Anthropic) | 6,495,943 | 60.5% | 4.9% | 0 |
| Formal Frontier | 120,317 | 8.0% | 22.0% | 0 |
| OpenAI Math | 13,031,949 | 25.4% | 1.4% | 34 |
| CFSG (AxiomMath) | 19,071,436 | 27.5% | 1.8% | 70 |

## Most compressible files (code only, at least 8 KB of code)

### Mathlib

| File | KB of code | Ratio |
|---|---:|---:|
| `Mathlib/CategoryTheory/Limits/Preserves/Opposites.lean` | 36.6 | 14.0 |
| `Mathlib/Geometry/Euclidean/Angle/Oriented/RightAngle.lean` | 37.4 | 13.6 |
| `Mathlib/Algebra/Ring/InjSurj.lean` | 23.7 | 12.4 |
| `Mathlib/CategoryTheory/Limits/Preserves/Creates/Opposites.lean` | 21.3 | 11.6 |
| `Mathlib/Algebra/Order/Group/Synonym.lean` | 16.8 | 10.4 |
| `Mathlib/Order/Interval/Finset/Fin.lean` | 25.7 | 10.0 |
| `Mathlib/RingTheory/Coalgebra/CoassocSimps.lean` | 30.5 | 9.7 |
| `Mathlib/Order/Interval/Set/Fin.lean` | 27.4 | 9.4 |
| `Mathlib/Algebra/Homology/BifunctorAssociator.lean` | 39.8 | 9.3 |
| `Mathlib/Order/Bounded.lean` | 18.6 | 9.0 |

### Tau Ceti

| File | KB of code | Ratio |
|---|---:|---:|
| `TauCeti/GroupTheory/SpecificGroups/CFSG/Assembly/GraphTwisted.lean` | 39.9 | 13.2 |
| `TauCeti/KnotTheory/Grid/Commutation/Overlap/Right.lean` | 40.0 | 12.7 |
| `TauCeti/GroupTheory/SpecificGroups/CFSG/Assembly/AmbientGroup.lean` | 22.5 | 12.4 |
| `TauCeti/RingTheory/Huber/LocalizationTopology/Laurent/Identification.lean` | 21.2 | 11.9 |
| `TauCeti/NumberTheory/QuadraticForm/OrthogonalGroup/DoubleCoset/Basic.lean` | 20.3 | 11.7 |
| `TauCeti/RepresentationTheory/Quiver/Zigzag/Braid/Triple/Differentials.lean` | 43.7 | 11.3 |
| `TauCeti/KnotTheory/Grid/Commutation/Disjoint/Basic.lean` | 24.3 | 11.1 |
| `TauCeti/CategoryTheory/Exact/Stable/Product/Triangulated.lean` | 17.1 | 10.9 |
| `TauCeti/KnotTheory/Grid/Commutation/Overlap/Basic.lean` | 35.9 | 10.6 |
| `TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Naturality.lean` | 18.5 | 10.5 |

### Lean Pool

| File | KB of code | Ratio |
|---|---:|---:|
| `LeanPool/BrillNoetherGraphs/LowGenus/Generated/G4Row099.lean` | 189.5 | 79.2 |
| `LeanPool/BrillNoetherGraphs/LowGenus/Generated/G4Row100.lean` | 214.7 | 74.1 |
| `LeanPool/Zeta5Irrational/Growth/InnerTable.lean` | 315.3 | 72.4 |
| `LeanPool/NFWeakPartition/NAR5H088P001Part004.lean` | 127.8 | 64.1 |
| `LeanPool/NFWeakPartition/NAR4C082C001Part004.lean` | 122.3 | 63.3 |
| `LeanPool/NFWeakPartition/NAR4C072C001Part017.lean` | 127.1 | 58.1 |
| `LeanPool/BrillNoetherGraphs/LowGenus/GenusFiveRow06CoverCells3.lean` | 134.6 | 57.4 |
| `LeanPool/BrillNoetherGraphs/LowGenus/GenusFiveRow06CoverCells2.lean` | 135.7 | 55.8 |
| `LeanPool/NFWeakPartition/NAR4C075C001Part004.lean` | 104.1 | 55.6 |
| `LeanPool/BrillNoetherGraphs/LowGenus/GenusFiveRow06CoverCells4.lean` | 134.9 | 55.5 |

### FLT (Anthropic)

| File | KB of code | Ratio |
|---|---:|---:|
| `P2M/Sol/S_LanglandsTunnell_CubicInduction_inducedPicture_quantisedMinor_annihilates_lowest_of_matched.lean` | 199.5 | 23.5 |
| `P2M/Sol/S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback.lean` | 366.9 | 21.9 |
| `P2M/Sol/S_TateCurve_ks17_D3_exports.lean` | 194.9 | 21.3 |
| `P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3.lean` | 117.4 | 21.0 |
| `P2M/Sol/S_AutomorphicForm_twistedWeightedClassIntegral_eq_finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_of_coupled_of_isSemiLocalFactorization.lean` | 314.4 | 19.8 |
| `P2M/Sol/S_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_blockQuadratic_colHarmonic.lean` | 123.0 | 18.0 |
| `P2M/Sol/S_CerednikDrinfeld_FormalODModule_smul_rigidNum_map_single_eq_smul_baseChange_of_rigidNum_single_eq_of_edge_isogeny.lean` | 75.6 | 17.6 |
| `P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isOpenImmersion_stratum_window_of_rigidifiedToG_of_bdd_local.lean` | 428.7 | 17.0 |
| `P2M/Sol/S_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_colHarmonic.lean` | 94.7 | 16.0 |
| `P2M/Sol/S_ModularCurve_DRModelPackage_exists_isDomain_ringHom_functionField_and_ringHom_modularFunctionFieldC_of_residueField_compZero.lean` | 205.8 | 15.4 |

### Formal Frontier

| File | KB of code | Ratio |
|---|---:|---:|
| `algebraic-direct-limits/AlgebraicDirectLimits/Topology/TensorProduct/Prod.lean` | 40.4 | 10.0 |
| `sheaf-cohomology/SheafCohomology/OpenCohomologyPushforwardResolution.lean` | 50.2 | 9.8 |
| `algebraic-direct-limits/AlgebraicDirectLimits/Topology/TensorAssociativity.lean` | 26.6 | 9.6 |
| `sheaf-cohomology/SheafCohomology/OpenCohomologyRightDerived.lean` | 22.8 | 9.6 |
| `profinite-groups/ProfiniteGroups/IndDualRealization.lean` | 29.6 | 9.5 |
| `sphere-topology/SphereTopology/Homology/Singular/MayerVietoris.lean` | 71.2 | 8.6 |
| `algebraic-groups/AlgebraicGroups/GroupScheme/UpperTriangularSplitKernel.lean` | 34.9 | 8.5 |
| `scheme-properties/SchemeProperties/GlobalSectionsBaseChange.lean` | 26.2 | 8.5 |
| `projective-modules/ProjectiveModules/Module/RightExtensionTensorProduct.lean` | 54.1 | 8.4 |
| `ringed-spaces/RingedSpaces/ChartedSpace/CompatibleAtlasSheaf.lean` | 18.9 | 8.3 |

### OpenAI Math

| File | KB of code | Ratio |
|---|---:|---:|
| `lean/OAI/GameTheory/SnakyConditional/Templates/Level36Part01.lean` | 1,339.3 | 50.8 |
| `lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_7.lean` | 317.1 | 48.6 |
| `lean/OAI/GameTheory/SnakyConditional/Templates/Level32Part03.lean` | 1,146.3 | 47.5 |
| `lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_8.lean` | 224.2 | 46.5 |
| `lean/OAI/GameTheory/SnakyConditional/Templates/Level35Part01.lean` | 1,335.5 | 46.4 |
| `lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_11.lean` | 225.7 | 42.1 |
| `lean/OAI/MathematicalPhysics/ContinuumCoulomb/Quantum/QuantumFourCorrelationCertificate.lean` | 36.8 | 39.9 |
| `lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_6.lean` | 240.0 | 38.1 |
| `lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_3.lean` | 159.1 | 36.7 |
| `lean/OAI/Combinatorics/Ramsey/CycleClique/Construction/CoverageK17.lean` | 1,666.8 | 36.2 |

### CFSG (AxiomMath)

| File | KB of code | Ratio |
|---|---:|---:|
| `CFSG/Milestones/ASVolI/F48/D43/Data.lean` | 4,537.8 | 1477.6 |
| `CFSG/LocalAnalysis/RankFourTheoremC/PEmpty/FongSporBigData4.lean` | 45.7 | 56.7 |
| `CFSG/LocalAnalysis/QuasithinUnique/Unconstrained/L2_5_19HSAutData.lean` | 13.4 | 53.0 |
| `CFSG/LocalAnalysis/LargeEvenClassification/C8FourSubgroupValid7.lean` | 19.7 | 41.8 |
| `CFSG/LocalAnalysis/LargeEvenClassification/C8FourSubgroupValid12.lean` | 19.7 | 41.5 |
| `CFSG/LocalAnalysis/EvenSmallLie/OmegaEight/SpBranchClsData.lean` | 70.2 | 41.2 |
| `CFSG/LocalAnalysis/LargeEvenClassification/C8FourSubgroupValid11.lean` | 19.7 | 40.3 |
| `CFSG/LocalAnalysis/LargeEvenClassification/C8FourSubgroupValid13.lean` | 19.7 | 40.3 |
| `CFSG/LocalAnalysis/LargeEvenClassification/C8FourSubgroupValid5.lean` | 19.7 | 40.3 |
| `CFSG/LocalAnalysis/LargeEvenClassification/C8FourSubgroupValid8.lean` | 19.7 | 40.3 |

Sources: Mathlib `e3e75e86143b`; Tau Ceti `e8b7b600c36c`; Lean Pool `01db1d7049cf`; FLT (Anthropic) `6e837e753555`; Formal Frontier (43 repositories); OpenAI Math `1581d4cbdd69`; CFSG (AxiomMath) `5f8042b343bd`.
