# Explicit unfoldings of definitions: CFSG (AxiomMath)

Backend: `source`. Source: `repos/axiom-cfsg` at `5f8042b343bd`.
Files scanned: 194,203.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (275,245 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 231,581 | 52,060 | 22.5% | 1,671,289 | 126,616 | 21,448 | 71,296 | 33,785 | 87 | 7.58 |
| outside file | 168,869 | 40,449 | 24.0% | 9,647,389 | 233,224 | 44,256 | 134,209 | 54,701 | 58 | 2.42 |
| outside directory | 49,991 | 10,348 | 20.7% | 5,149,791 | 102,338 | 19,231 | 60,935 | 22,159 | 13 | 1.99 |

## instance (3,562 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 149 | 0 | 0.0% | 208 | 0 | 0 | 0 | 0 | 0 | 0.00 |
| outside file | 324 | 0 | 0.0% | 2,448 | 0 | 0 | 0 | 0 | 0 | 0.00 |
| outside directory | 168 | 0 | 0.0% | 1,832 | 0 | 0 | 0 | 0 | 0 | 0.00 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `CFSG.StandardType.ggCellAtI` | def | `CFSG/LocalAnalysis/StandardType/GGResICell.lean` | 1576 | 131 | 1577 | 1578 |
| `CFSG.Yardstones.Md0ec50421ce4.onLie` | def | `CFSG/Yardstones/Md0ec50421ce4/Definitions.lean` | 1558 | 254 | 2390 | 2393 |
| `CFSG.StandardType.LargeEvenRawDatum` | def | `CFSG/Assembly/LargeEvenDefs.lean` | 1508 | 784 | 1810 | 1812 |
| `CFSG.Open.pCoreOf` | def | `CFSG/Open/LocalVocabulary.lean` | 1156 | 891 | 123257 | 123259 |
| `CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem` | def | `CFSG/ThirdParty/QiuzhenCFSG/BenderSuzuki/PFAppendixIII/Basic.lean` | 1109 | 278 | 5002 | 5019 |
| `CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm` | def | `CFSG/LocalAnalysis/ComponentInitial/LinearUnitaryField.lean` | 1005 | 500 | 3346 | 3346 |
| `CFSG.conjugate` | def | `CFSG/Foundations/Basic.lean` | 999 | 569 | 26389 | 26392 |
| `CFSG.Quasithin.rk` | def | `CFSG/Quasithin/Background/D2Basic.lean` | 963 | 620 | 14835 | 14861 |
| `CFSG.Assembly.LargeEvenInLambda2` | def | `CFSG/Assembly/GL83LieDefs.lean` | 954 | 367 | 5167 | 5169 |
| `CFSG.StandardType.markTag` | def | `CFSG/LocalAnalysis/StandardType/MarkingDict.lean` | 943 | 287 | 1650 | 1651 |
| `CFSG.LieType.Universal.Unitary.conjTr` | def | `CFSG/LieType/Universal/Unitary/Basic.lean` | 926 | 525 | 5262 | 5292 |
| `CFSG.StandardType.GGCellCheckI` | def | `CFSG/LocalAnalysis/StandardType/GGResICell.lean` | 910 | 252 | 1824 | 1824 |
| `CFSG.inSubgroup` | def | `CFSG/Foundations/Basic.lean` | 875 | 610 | 12565 | 12565 |
| `CFSG.StandardType.markDeg` | def | `CFSG/LocalAnalysis/StandardType/MarkingDict.lean` | 759 | 259 | 1334 | 1335 |
| `CFSG.StandardType.markRank` | def | `CFSG/LocalAnalysis/StandardType/MarkingDict.lean` | 704 | 235 | 1266 | 1267 |
| `CFSG.Yardstones.Md0ec50421ce4.ambiguousChev` | def | `CFSG/Yardstones/Md0ec50421ce4/Definitions.lean` | 699 | 107 | 811 | 812 |
| `CFSG.Blueprint.classicalTags` | def | `CFSG/Blueprint/Catalog.lean` | 693 | 364 | 921 | 923 |
| `CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar` | def | `CFSG/LocalAnalysis/ComponentInitial/RootDiagonalConjugation.lean` | 691 | 507 | 7745 | 7760 |
| `CFSG.StandardType.markChar` | def | `CFSG/LocalAnalysis/StandardType/MarkingDict.lean` | 621 | 231 | 1126 | 1127 |
| `CFSG.Blueprint.Multiplier.exceptionalOrders` | def | `CFSG/Blueprint/MultiplierDefs.lean` | 620 | 324 | 2059 | 2061 |
| `CFSG.ComponentClassification.CatLeaf.lieSylowExponent` | def | `CFSG/LocalAnalysis/ComponentClassification/CatLeafInputs.lean` | 582 | 110 | 1050 | 1051 |
| `CFSG.Quasithin.conjSubgroup` | def | `CFSG/Quasithin/Background/A1cTransfer.lean` | 560 | 314 | 27228 | 27248 |
| `CFSG.Blueprint.Multiplier.genericOrders` | def | `CFSG/Blueprint/MultiplierDefs.lean` | 548 | 237 | 2016 | 2018 |
| `CFSG.ComponentClassification.CatLeaf.lieOrderNumerator` | def | `CFSG/LocalAnalysis/ComponentClassification/CatLeafInputs.lean` | 497 | 180 | 1432 | 1433 |
| `CFSG.Blueprint.chevalleyExceptionalTags` | def | `CFSG/Blueprint/Catalog.lean` | 488 | 242 | 702 | 705 |
| `Subgroup.conjBy` | def | `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/BGsection3/Defs.lean` | 488 | 173 | 2940 | 2945 |
| `CFSG.Quasithin.commSub` | def | `CFSG/Quasithin/Background/D2Basic.lean` | 451 | 308 | 14867 | 14878 |
| `CFSG.ClassicalInvolution.Generic.conjSub` | def | `CFSG/ClassicalInvolution/Generic/Frame.lean` | 436 | 319 | 34742 | 34776 |
| `CFSG.Section1.degree` | def | `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PFsection1/PFsection1_4.lean` | 417 | 57 | 3475 | 3486 |
| `CFSG.Blueprint.Chevalley.rootSpan` | def | `CFSG/Blueprint/ChevalleyPinned.lean` | 416 | 346 | 12265 | 12267 |

## Most unfolded outside its directory

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `CFSG.Yardstones.Md0ec50421ce4.onLie` | def | `CFSG/Yardstones/Md0ec50421ce4/Definitions.lean` | 1558 | 254 | 2390 | 2393 |
| `CFSG.StandardType.LargeEvenRawDatum` | def | `CFSG/Assembly/LargeEvenDefs.lean` | 1508 | 784 | 1810 | 1812 |
| `CFSG.Open.pCoreOf` | def | `CFSG/Open/LocalVocabulary.lean` | 1156 | 891 | 123247 | 123259 |
| `CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem` | def | `CFSG/ThirdParty/QiuzhenCFSG/BenderSuzuki/PFAppendixIII/Basic.lean` | 1109 | 278 | 5002 | 5019 |
| `CFSG.conjugate` | def | `CFSG/Foundations/Basic.lean` | 998 | 568 | 26381 | 26392 |
| `CFSG.Assembly.LargeEvenInLambda2` | def | `CFSG/Assembly/GL83LieDefs.lean` | 954 | 367 | 5165 | 5169 |
| `CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm` | def | `CFSG/LocalAnalysis/ComponentInitial/LinearUnitaryField.lean` | 926 | 466 | 3001 | 3346 |
| `CFSG.LieType.Universal.Unitary.conjTr` | def | `CFSG/LieType/Universal/Unitary/Basic.lean` | 918 | 521 | 5034 | 5292 |
| `CFSG.inSubgroup` | def | `CFSG/Foundations/Basic.lean` | 875 | 610 | 12565 | 12565 |
| `CFSG.Yardstones.Md0ec50421ce4.ambiguousChev` | def | `CFSG/Yardstones/Md0ec50421ce4/Definitions.lean` | 699 | 107 | 811 | 812 |
| `CFSG.Blueprint.classicalTags` | def | `CFSG/Blueprint/Catalog.lean` | 693 | 364 | 920 | 923 |
| `CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar` | def | `CFSG/LocalAnalysis/ComponentInitial/RootDiagonalConjugation.lean` | 691 | 507 | 7745 | 7760 |
| `CFSG.Quasithin.rk` | def | `CFSG/Quasithin/Background/D2Basic.lean` | 665 | 435 | 10466 | 14861 |
| `CFSG.Blueprint.Multiplier.exceptionalOrders` | def | `CFSG/Blueprint/MultiplierDefs.lean` | 620 | 324 | 2059 | 2061 |
| `CFSG.Quasithin.conjSubgroup` | def | `CFSG/Quasithin/Background/A1cTransfer.lean` | 554 | 310 | 26173 | 27248 |
| `CFSG.Blueprint.Multiplier.genericOrders` | def | `CFSG/Blueprint/MultiplierDefs.lean` | 548 | 237 | 2016 | 2018 |
| `CFSG.Blueprint.chevalleyExceptionalTags` | def | `CFSG/Blueprint/Catalog.lean` | 488 | 242 | 701 | 705 |
| `Subgroup.conjBy` | def | `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/BGsection3/Defs.lean` | 483 | 171 | 2916 | 2945 |
| `CFSG.ClassicalInvolution.Generic.conjSub` | def | `CFSG/ClassicalInvolution/Generic/Frame.lean` | 430 | 315 | 34604 | 34776 |
| `CFSG.Blueprint.Chevalley.rootSpan` | def | `CFSG/Blueprint/ChevalleyPinned.lean` | 416 | 346 | 12263 | 12267 |
| `CFSG.ComponentClassification.CatLeaf.lieSylowExponent` | def | `CFSG/LocalAnalysis/ComponentClassification/CatLeafInputs.lean` | 407 | 76 | 714 | 1051 |
| `CFSG.Section1.degree` | def | `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PFsection1/PFsection1_4.lean` | 399 | 53 | 3325 | 3486 |
| `CFSG.Assembly.LargeEvenRawDatum` | def | `CFSG/Assembly/GL83LieDefs.lean` | 391 | 181 | 605 | 615 |
| `CFSG.ComponentClassification.CatLeaf.lieOrderNumerator` | def | `CFSG/LocalAnalysis/ComponentClassification/CatLeafInputs.lean` | 391 | 139 | 1167 | 1433 |
| `CFSG.StandardType.markTag` | def | `CFSG/LocalAnalysis/StandardType/MarkingDict.lean` | 387 | 130 | 688 | 1651 |
| `CFSG.Quasithin.E3.mQuot` | def | `CFSG/Quasithin/Background/E3Defs.lean` | 349 | 254 | 4866 | 5674 |
| `CFSG.LieType.Universal.Unitary.antidiag` | def | `CFSG/LieType/Universal/Unitary/Basic.lean` | 348 | 188 | 4463 | 4537 |
| `CFSG.ComponentClassification.CatLeaf.lieOrderDivisor` | def | `CFSG/LocalAnalysis/ComponentClassification/CatLeafInputs.lean` | 330 | 97 | 1095 | 1346 |
| `CFSG.Quasithin.commSub` | def | `CFSG/Quasithin/Background/D2Basic.lean` | 328 | 224 | 12392 | 14878 |
| `CFSG.Assembly.LargeEvenUntwisted` | def | `CFSG/Assembly/GL83LieDefs.lean` | 327 | 124 | 388 | 398 |

## Diagnostics

- ambiguous name: 38,603
- field notation: 852,399
- names declared in several files: 57
