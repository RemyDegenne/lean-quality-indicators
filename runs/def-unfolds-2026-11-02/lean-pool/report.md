# Explicit unfoldings of definitions: Lean Pool

Backend: `source`. Source: `repos/lean-pool` at `01db1d7049cf`.
Files scanned: 21,182.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (74,932 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 66,760 | 31,255 | 46.8% | 664,223 | 87,643 | 15,613 | 60,477 | 11,518 | 35 | 13.19 |
| outside file | 38,513 | 16,390 | 42.6% | 1,832,109 | 97,384 | 22,478 | 67,389 | 7,483 | 34 | 5.32 |
| outside directory | 8,790 | 3,071 | 34.9% | 542,832 | 24,309 | 4,063 | 18,574 | 1,661 | 11 | 4.48 |

## instance (6,558 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 431 | 16 | 3.7% | 694 | 27 | 12 | 14 | 1 | 0 | 3.89 |
| outside file | 212 | 6 | 2.8% | 797 | 9 | 3 | 2 | 4 | 0 | 1.13 |
| outside directory | 54 | 1 | 1.9% | 89 | 1 | 0 | 0 | 1 | 0 | 1.12 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ConwaySoifer.cross` | def | `LeanPool/ConwaySoifer/Geometry/TriangleHalfspaces.lean` | 880 | 44 | 1386 | 1402 |
| `ConwaySoifer.rot` | def | `LeanPool/ConwaySoifer/Geometry/Support.lean` | 736 | 36 | 759 | 831 |
| `Zeta5Irrational.M0` | abbrev | `LeanPool/Zeta5Irrational/Measure.lean` | 687 | 4 | 706 | 706 |
| `ConwaySoifer.supportNum` | def | `LeanPool/ConwaySoifer/Geometry/Support.lean` | 663 | 34 | 1331 | 1347 |
| `Complexity.TM.step` | def | `LeanPool/BeyondBethe/Complexitylib/Models/TuringMachine.lean` | 485 | 65 | 641 | 651 |
| `Complexity.RAM.Structured.Basic.exec` | def | `LeanPool/BeyondBethe/Complexitylib/Models/RandomAccessMachine/Structured/Defs.lean` | 472 | 21 | 479 | 479 |
| `CKN.Foundation.Parabolic.vec3EuclideanNorm` | def | `LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Basic.lean` | 437 | 231 | 10541 | 10559 |
| `Homogenization.vecDot` | def | `LeanPool/AnomalousDiffusion/Homogenization/Ambient/Basic.lean` | 412 | 205 | 2008 | 2024 |
| `Complexity.Tape.move` | def | `LeanPool/BeyondBethe/Complexitylib/Models/TuringMachine.lean` | 404 | 73 | 442 | 448 |
| `MovingSofa.frame` | def | `LeanPool/MovingSofa/Development/Geometry/Foundations/Development001.lean` | 386 | 9 | 386 | 417 |
| `oneChip` | def | `LeanPool/BrillNoetherGraphs/ChipFiringWithLean/Basic.lean` | 370 | 86 | 5455 | 5470 |
| `ConwaySoifer.normSq` | def | `LeanPool/ConwaySoifer/Geometry/Support.lean` | 350 | 36 | 687 | 746 |
| `MovingSofa.normalVector` | abbrev | `LeanPool/MovingSofa/Development/Geometry/Foundations/Development001.lean` | 336 | 9 | 2426 | 2664 |
| `Complexity.TM.idleDir` | def | `LeanPool/BeyondBethe/Complexitylib/Models/TuringMachine/Combinators/Helpers.lean` | 282 | 55 | 1375 | 1389 |
| `Complexity.Tape.read` | def | `LeanPool/BeyondBethe/Complexitylib/Models/TuringMachine.lean` | 272 | 52 | 681 | 685 |
| `AVenhance.spaceGrad` | def | `LeanPool/AnomalousDiffusion/AVenhance/Statements/Roots/SpaceGrad.lean` | 267 | 155 | 5794 | 5794 |
| `Complexity.Tape.write` | def | `LeanPool/BeyondBethe/Complexitylib/Models/TuringMachine.lean` | 238 | 51 | 293 | 299 |
| `CKN.spatialDeriv` | def | `LeanPool/CaffarelliKohnNirenberg/Pressure/LeibnizLaplacian.lean` | 229 | 124 | 6452 | 6501 |
| `CKN.spatialGradientSq` | def | `LeanPool/CaffarelliKohnNirenberg/Statements/SpatialGradientSq.lean` | 226 | 130 | 1852 | 1852 |
| `linearEquiv` | def | `LeanPool/BrillNoetherGraphs/ChipFiringWithLean/Basic.lean` | 223 | 83 | 884 | 915 |
| `Erdos97Octagon.sqDist` | def | `LeanPool/Erdos97ConvexOctagon/CayleyMenger.lean` | 202 | 13 | 464 | 495 |
| `EulerVolterraConvolution.extendPath` | def | `LeanPool/NavierStokesAndEuler/Euler/VolterraConvolution.lean` | 202 | 85 | 1564 | 1571 |
| `CKN.vecEuclideanNorm` | def | `LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Cutoff/Basic.lean` | 188 | 105 | 776 | 786 |
| `CKN.vecNormSq` | def | `LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Cutoff/Basic.lean` | 180 | 102 | 283 | 293 |
| `CKN.vecDot` | def | `LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Cutoff/Basic.lean` | 178 | 100 | 178 | 181 |
| `NFChoice.Compiler.CompactSourceSyntax.synWb` | def | `LeanPool/NFWeakPartition/CompactSourceSyntax.lean` | 170 | 21 | 2465 | 2467 |
| `Complexity.Tape.writeAndMove` | abbrev | `LeanPool/BeyondBethe/Complexitylib/Models/TuringMachine.lean` | 165 | 30 | 200 | 202 |
| `Complexity.RAM.Structured.Basic.execList` | def | `LeanPool/BeyondBethe/Complexitylib/Models/RandomAccessMachine/Structured/Defs.lean` | 164 | 14 | 374 | 375 |
| `Complexity.Tape.init` | def | `LeanPool/BeyondBethe/Complexitylib/Models/TuringMachine.lean` | 162 | 46 | 1053 | 1077 |
| `PDL.Sequent.toFinset` | def | `LeanPool/PDL/Sequent.lean` | 156 | 13 | 234 | 242 |

## Most unfolded outside its directory

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ConwaySoifer.cross` | def | `LeanPool/ConwaySoifer/Geometry/TriangleHalfspaces.lean` | 848 | 37 | 1030 | 1402 |
| `ConwaySoifer.rot` | def | `LeanPool/ConwaySoifer/Geometry/Support.lean` | 728 | 35 | 733 | 831 |
| `ConwaySoifer.supportNum` | def | `LeanPool/ConwaySoifer/Geometry/Support.lean` | 663 | 34 | 1331 | 1347 |
| `CKN.Foundation.Parabolic.vec3EuclideanNorm` | def | `LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Basic.lean` | 427 | 226 | 10421 | 10559 |
| `Homogenization.vecDot` | def | `LeanPool/AnomalousDiffusion/Homogenization/Ambient/Basic.lean` | 398 | 203 | 1940 | 2024 |
| `oneChip` | def | `LeanPool/BrillNoetherGraphs/ChipFiringWithLean/Basic.lean` | 365 | 84 | 5395 | 5470 |
| `ConwaySoifer.normSq` | def | `LeanPool/ConwaySoifer/Geometry/Support.lean` | 344 | 34 | 661 | 746 |
| `AVenhance.spaceGrad` | def | `LeanPool/AnomalousDiffusion/AVenhance/Statements/Roots/SpaceGrad.lean` | 267 | 155 | 5792 | 5794 |
| `Complexity.RAM.Structured.Basic.exec` | def | `LeanPool/BeyondBethe/Complexitylib/Models/RandomAccessMachine/Structured/Defs.lean` | 228 | 12 | 228 | 479 |
| `CKN.spatialGradientSq` | def | `LeanPool/CaffarelliKohnNirenberg/Statements/SpatialGradientSq.lean` | 226 | 130 | 1844 | 1852 |
| `Complexity.TM.idleDir` | def | `LeanPool/BeyondBethe/Complexitylib/Models/TuringMachine/Combinators/Helpers.lean` | 224 | 44 | 1126 | 1389 |
| `linearEquiv` | def | `LeanPool/BrillNoetherGraphs/ChipFiringWithLean/Basic.lean` | 216 | 80 | 868 | 915 |
| `CKN.spatialDeriv` | def | `LeanPool/CaffarelliKohnNirenberg/Pressure/LeibnizLaplacian.lean` | 190 | 105 | 5184 | 6501 |
| `CKN.vecEuclideanNorm` | def | `LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Cutoff/Basic.lean` | 187 | 104 | 756 | 786 |
| `CKN.vecNormSq` | def | `LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Cutoff/Basic.lean` | 177 | 100 | 274 | 293 |
| `CKN.vecDot` | def | `LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Cutoff/Basic.lean` | 175 | 98 | 175 | 181 |
| `MovingSofa.frame` | def | `LeanPool/MovingSofa/Development/Geometry/Foundations/Development001.lean` | 154 | 3 | 154 | 417 |
| `Homogenization.vecNormSq` | def | `LeanPool/AnomalousDiffusion/Homogenization/Ambient/Basic.lean` | 153 | 95 | 1090 | 1148 |
| `MovingSofa.normalVector` | abbrev | `LeanPool/MovingSofa/Development/Geometry/Foundations/Development001.lean` | 138 | 3 | 816 | 2664 |
| `Complexity.TM.step` | def | `LeanPool/BeyondBethe/Complexitylib/Models/TuringMachine.lean` | 132 | 12 | 145 | 651 |
| `CKN.spatialPartial` | def | `LeanPool/CaffarelliKohnNirenberg/Statements/SpatialPartial.lean` | 127 | 82 | 7693 | 7722 |
| `Zeta5Irrational.lrow` | def | `LeanPool/Zeta5Irrational/Arith/InnerAlloc.lean` | 127 | 3 | 132 | 166 |
| `CIV.meridional` | def | `LeanPool/CIVAxisymmetric/Statements/Meridional.lean` | 124 | 37 | 1140 | 1146 |
| `Lean4GlCoalgebras.Ext.p` | def | `LeanPool/Lean4GlCoalgebras/Split/ProofTransformations.lean` | 113 | 1 | 116 | 136 |
| `EulerGevrey.majorant` | def | `LeanPool/NavierStokesAndEuler/Euler/Foundations/Gevrey.lean` | 111 | 57 | 1348 | 1446 |
| `Homogenization.basisVec` | def | `LeanPool/AnomalousDiffusion/Homogenization/Sobolev/WeakDerivatives.lean` | 109 | 57 | 2113 | 2165 |
| `AVenhance.l2NormSq` | def | `LeanPool/AnomalousDiffusion/AVenhance/Statements/Roots/L2NormSq.lean` | 99 | 57 | 1601 | 1604 |
| `ContinuousLinearMap.kyFanGauge` | def | `LeanPool/DavisKahan/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean` | 94 | 55 | 168 | 263 |
| `AVenhance.a` | def | `LeanPool/AnomalousDiffusion/AVenhance/Statements/Ingredients/A.lean` | 88 | 50 | 1568 | 1570 |
| `AVenhance.unitCube` | def | `LeanPool/AnomalousDiffusion/AVenhance/Statements/Roots/UnitCube.lean` | 88 | 60 | 1948 | 1960 |

## Diagnostics

- ambiguous name: 3,534
- field notation: 182,399
- names declared in several files: 25
