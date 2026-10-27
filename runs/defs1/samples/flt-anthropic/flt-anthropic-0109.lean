namespace P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option autoImplicit false

p2m_open

namespace ModularCurve p2m_export "ModularCurve" "CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full NodeLocalized.modularEval NodeLocalized.pointEval NodeLocalized.modularLocalizedAtPoint ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar coe_geomAut_coeffEmb frobNodePair frobenius_identity_geom_unconditional exists_isFrickeAutFull CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional" end ModularCurve

p2m_open_scoped "ModularCurve" in

p2m_open

p2m_reactivate

p2m_open

p2m_reactivate

namespace ModularCurve

p2m_open

p2m_open

section LevelQ

variable (q : ℕ) [Fact q.Prime]

local notation "F_" q => modularFunctionFieldBar (1 * q)

local notation "Qb" => AlgebraicClosure ℚ

noncomputable def modularEvalF (A : Subring Qb) : MvPolynomial (Fin 2) A →+* modularFunctionFieldBar (1 * q) :=
  (modularEval (1 * q) A).codRestrict (modularFunctionFieldBar (1 * q)).toSubring
    (fun p => modularRing_le q A (modularEval_mem_modularRing (1 * q) A p))

end LevelQ
end ModularCurve
end ModularCurve
end P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint
