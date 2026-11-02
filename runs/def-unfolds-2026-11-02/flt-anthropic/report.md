# Explicit unfoldings of definitions: FLT (Anthropic)

Backend: `source`. Source: `repos/flt-anthropic` at `6e837e753555`.
Files scanned: 30,962.

An explicit unfolding is a use of the name in `unfold`/`delta`/`unseal` (unfold), a simp-like lemma list (simp), a rewrite rule list (rw), or an equation lemma `foo.eq_def`/`foo.eq_<n>` (eq_def). Scopes: the definition's own file, the rest of its directory (subdirectories included), and everything else.

## def/abbrev (78,206 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 76,084 | 22,864 | 30.1% | 908,494 | 57,957 | 11,198 | 26,736 | 20,021 | 2 | 6.38 |
| outside file | 6,683 | 2,425 | 36.3% | 2,429,825 | 48,528 | 13,195 | 21,484 | 13,849 | 0 | 2.00 |
| outside directory | 6,460 | 2,390 | 37.0% | 2,392,836 | 47,712 | 13,075 | 21,052 | 13,585 | 0 | 1.99 |

## instance (10,172 definitions)

| Where | Definitions used | Definitions unfolded | Share unfolded | Uses | Unfoldings | unfold | simp | rw | eq_def | Unfoldings per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| own file | 580 | 0 | 0.0% | 834 | 0 | 0 | 0 | 0 | 0 | 0.00 |
| outside file | 748 | 1 | 0.1% | 585,542 | 1 | 1 | 0 | 0 | 0 | 0.00 |
| outside directory | 746 | 1 | 0.1% | 585,500 | 1 | 1 | 0 | 0 | 0 | 0.00 |

## Most unfolded outside its file

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ModularCurve.coeffEmb` | def | `Definitions/Def_ModularCurve_LaurentCoeff.lean` | 1031 | 514 | 18946 | 18953 |
| `ModularCurve.intSeriesC` | def | `Definitions/Def_ModularCurve_X1.lean` | 999 | 337 | 6684 | 6701 |
| `LanglandsTunnell.CubicInduction.embedMat2` | def | `Definitions/Def_LanglandsTunnell_CubicInduction_Carrier.lean` | 734 | 193 | 1049 | 1059 |
| `ModularFormClass.qCoeff` | def | `Definitions/Def_FLTPrelim_Modularity.lean` | 659 | 277 | 6833 | 6845 |
| `ModularCurve.IsIntegralQExp` | def | `Definitions/Def_ModularCurve_X1.lean` | 644 | 206 | 4034 | 4049 |
| `ModularCurve.jqNModC` | def | `Definitions/Def_ModularCurve_JqCoeff.lean` | 502 | 256 | 8977 | 8980 |
| `AlgebraicCurve.Place.ord` | def | `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean` | 480 | 210 | 22794 | 22817 |
| `ModularCurve.NodeLocalized.modularEval` | def | `Definitions/Def_ModularCurve_NodeLocalized.lean` | 455 | 97 | 2859 | 2880 |
| `NumberField.TateGlobal.ideleNorm` | def | `Definitions/Def_NumberField_TateGlobalZeta.lean` | 373 | 239 | 17515 | 17523 |
| `LanglandsTunnell.Converse.ArchR.quasiChar` | def | `Definitions/Def_LanglandsTunnell_JLConverse.lean` | 346 | 122 | 3539 | 3541 |
| `LanglandsTunnell.CubicInduction.gl3Entry` | def | `Definitions/Def_LanglandsTunnell_CubicInduction_PrincipalSeries3.lean` | 308 | 33 | 3070 | 3122 |
| `CohCarrier.gamma0Units` | def | `Definitions/Def_CohCarrier_Level.lean` | 298 | 133 | 1335 | 1342 |
| `LanglandsTunnell.Converse.ArchR.diagOne` | def | `Definitions/Def_LanglandsTunnell_JLConverse.lean` | 294 | 101 | 3612 | 3614 |
| `CerednikDrinfeld.QM.mapPt` | def | `Definitions/Def_CerednikDrinfeld_QMModuli.lean` | 288 | 66 | 11427 | 11441 |
| `AlgebraicCurve.Divisor.degree` | def | `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean` | 284 | 250 | 6301 | 6308 |
| `CerednikDrinfeld.QM.pushPt` | abbrev | `Definitions/Def_CerednikDrinfeld_QMModuli.lean` | 283 | 119 | 4726 | 4734 |
| `CerednikDrinfeld.QM.nsmulPt` | def | `Definitions/Def_CerednikDrinfeld_QMModuli.lean` | 281 | 90 | 3966 | 3968 |
| `AutomorphicForm.whittakerCoefficient` | def | `Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean` | 268 | 101 | 3326 | 3330 |
| `LanglandsTunnell.CubicInduction.upperUnipotent3` | def | `Definitions/Def_LanglandsTunnell_CubicInduction_Carrier.lean` | 249 | 74 | 5835 | 5844 |
| `AutomorphicForm.constantTerm` | def | `Definitions/Def_AutomorphicForm_ConstantTerm.lean` | 243 | 126 | 1545 | 1550 |
| `WeierstrassCurve.Affine.vcXInv` | def | `Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean` | 243 | 86 | 987 | 995 |
| `AlgebraicGeometry.RelPicard.baseChangeSnd` | def | `Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean` | 242 | 116 | 2640 | 2649 |
| `ModularCurve.UVCrossingModel.annulusWeight` | def | `Definitions/Def_ModularCurve_UVCrossingGaussOrder.lean` | 232 | 35 | 619 | 622 |
| `AutomorphicForm.sigmaTensor` | def | `Definitions/Def_AutomorphicForm_TwistedOrbital.lean` | 231 | 125 | 3188 | 3189 |
| `ModularCurve.tateBase` | def | `Definitions/Def_ModularCurve_TateSlots.lean` | 231 | 70 | 1801 | 1803 |
| `WeierstrassCurve.veluGy` | def | `Definitions/Def_WeierstrassCurve_Velu.lean` | 228 | 92 | 822 | 832 |
| `ModularCurve.jqN` | def | `Definitions/Def_ModularCurve_X0.lean` | 221 | 102 | 3104 | 3106 |
| `AlgebraicGeometry.Polarisation.sliceAt` | def | `Definitions/Def_AlgebraicGeometry_PolarisationRosati.lean` | 213 | 68 | 1219 | 1221 |
| `AutomorphicForm.unipotentGL2` | def | `Definitions/Def_AutomorphicForm_ConstantTerm.lean` | 207 | 111 | 17634 | 17642 |
| `ModularCurve.tateLaurent` | def | `Definitions/Def_ModularCurve_TateFormal.lean` | 207 | 84 | 722 | 727 |

## Most unfolded outside its directory

| Definition | Kind | File | Unfoldings | Files | Uses there | Total uses |
|---|---|---|---:|---:|---:|---:|
| `ModularCurve.coeffEmb` | def | `Definitions/Def_ModularCurve_LaurentCoeff.lean` | 1030 | 513 | 18833 | 18953 |
| `ModularCurve.intSeriesC` | def | `Definitions/Def_ModularCurve_X1.lean` | 993 | 335 | 6639 | 6701 |
| `LanglandsTunnell.CubicInduction.embedMat2` | def | `Definitions/Def_LanglandsTunnell_CubicInduction_Carrier.lean` | 731 | 191 | 1045 | 1059 |
| `ModularFormClass.qCoeff` | def | `Definitions/Def_FLTPrelim_Modularity.lean` | 655 | 274 | 6765 | 6845 |
| `ModularCurve.IsIntegralQExp` | def | `Definitions/Def_ModularCurve_X1.lean` | 644 | 206 | 4015 | 4049 |
| `ModularCurve.jqNModC` | def | `Definitions/Def_ModularCurve_JqCoeff.lean` | 489 | 247 | 8822 | 8980 |
| `AlgebraicCurve.Place.ord` | def | `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean` | 471 | 204 | 22415 | 22817 |
| `ModularCurve.NodeLocalized.modularEval` | def | `Definitions/Def_ModularCurve_NodeLocalized.lean` | 455 | 97 | 2835 | 2880 |
| `NumberField.TateGlobal.ideleNorm` | def | `Definitions/Def_NumberField_TateGlobalZeta.lean` | 373 | 239 | 17478 | 17523 |
| `LanglandsTunnell.Converse.ArchR.quasiChar` | def | `Definitions/Def_LanglandsTunnell_JLConverse.lean` | 346 | 122 | 3534 | 3541 |
| `LanglandsTunnell.CubicInduction.gl3Entry` | def | `Definitions/Def_LanglandsTunnell_CubicInduction_PrincipalSeries3.lean` | 308 | 33 | 3070 | 3122 |
| `LanglandsTunnell.Converse.ArchR.diagOne` | def | `Definitions/Def_LanglandsTunnell_JLConverse.lean` | 294 | 101 | 3611 | 3614 |
| `CohCarrier.gamma0Units` | def | `Definitions/Def_CohCarrier_Level.lean` | 293 | 130 | 1313 | 1342 |
| `CerednikDrinfeld.QM.mapPt` | def | `Definitions/Def_CerednikDrinfeld_QMModuli.lean` | 288 | 66 | 11335 | 11441 |
| `AlgebraicCurve.Divisor.degree` | def | `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean` | 283 | 249 | 6208 | 6308 |
| `CerednikDrinfeld.QM.pushPt` | abbrev | `Definitions/Def_CerednikDrinfeld_QMModuli.lean` | 283 | 119 | 4703 | 4734 |
| `CerednikDrinfeld.QM.nsmulPt` | def | `Definitions/Def_CerednikDrinfeld_QMModuli.lean` | 281 | 90 | 3960 | 3968 |
| `AutomorphicForm.whittakerCoefficient` | def | `Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean` | 267 | 100 | 3312 | 3330 |
| `LanglandsTunnell.CubicInduction.upperUnipotent3` | def | `Definitions/Def_LanglandsTunnell_CubicInduction_Carrier.lean` | 246 | 71 | 5746 | 5844 |
| `AutomorphicForm.constantTerm` | def | `Definitions/Def_AutomorphicForm_ConstantTerm.lean` | 240 | 124 | 1537 | 1550 |
| `AlgebraicGeometry.RelPicard.baseChangeSnd` | def | `Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean` | 235 | 111 | 2578 | 2649 |
| `WeierstrassCurve.Affine.vcXInv` | def | `Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean` | 235 | 82 | 964 | 995 |
| `ModularCurve.UVCrossingModel.annulusWeight` | def | `Definitions/Def_ModularCurve_UVCrossingGaussOrder.lean` | 232 | 35 | 618 | 622 |
| `AutomorphicForm.sigmaTensor` | def | `Definitions/Def_AutomorphicForm_TwistedOrbital.lean` | 231 | 125 | 3164 | 3189 |
| `ModularCurve.tateBase` | def | `Definitions/Def_ModularCurve_TateSlots.lean` | 230 | 69 | 1787 | 1803 |
| `ModularCurve.jqN` | def | `Definitions/Def_ModularCurve_X0.lean` | 220 | 101 | 3091 | 3106 |
| `AlgebraicGeometry.Polarisation.sliceAt` | def | `Definitions/Def_AlgebraicGeometry_PolarisationRosati.lean` | 213 | 68 | 1218 | 1221 |
| `WeierstrassCurve.veluGy` | def | `Definitions/Def_WeierstrassCurve_Velu.lean` | 211 | 83 | 780 | 832 |
| `AutomorphicForm.unipotentGL2` | def | `Definitions/Def_AutomorphicForm_ConstantTerm.lean` | 205 | 109 | 17571 | 17642 |
| `ModularCurve.tateLaurent` | def | `Definitions/Def_ModularCurve_TateFormal.lean` | 204 | 82 | 707 | 727 |

## Diagnostics

- ambiguous name: 5,816
- field notation: 328,284
- names declared in several files: 23
