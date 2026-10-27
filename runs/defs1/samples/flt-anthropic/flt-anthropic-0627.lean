namespace P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical

open Polynomial ModularCurve ModularCurve.IgusaScheme WithZero

namespace NeronLeg1CuspSections

section Charts

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull (N * p)) : Type)

set_option quotPrecheck false in
local notation "ℤp" => (↥(GaloisRep.ratLocalizedAt p) : Type)

local notation "w" => atkinLehnerInvolutionFull N p

def cuspRetraction (φ : F →ₐ[ℚ] F)
    (hφ : ∀ b : ↥(chartAlgInf (N * p) p), ((φ (b : F) : F) : LaurentSeries ℚ) ∈ 𝒪 ∧
      ((φ (b : F) : F) : LaurentSeries ℚ).coeff 0 ∈ GaloisRep.ratLocalizedAt p) :
    ↥(chartAlgInf (N * p) p) →ₐ[ℤp] ℤp where
  toFun b := ⟨((φ (b : F) : F) : LaurentSeries ℚ).coeff 0, (hφ b).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' b c := Subtype.ext (by
    have := map_mul ρ ⟨_, (hφ b).1⟩ ⟨_, (hφ c).1⟩
    simp only [ρ_apply, MulMemClass.mk_mul_mk] at this
    change ((φ ((b * c : ↥(chartAlgInf (N * p) p)) : F) : F) : LaurentSeries ℚ).coeff 0 = _
    rw [Subalgebra.coe_mul, map_mul, IntermediateField.coe_mul, this]
    rfl)
  map_zero' := Subtype.ext (by simp)
  map_add' b c := Subtype.ext (by
    change ((φ ((b + c : ↥(chartAlgInf (N * p) p)) : F) : F) : LaurentSeries ℚ).coeff 0 = _
    rw [Subalgebra.coe_add, map_add, IntermediateField.coe_add, HahnSeries.coeff_add]
    rfl)
  commutes' c := Subtype.ext (by
    change ((φ ((algebraMap ℤp ↥(chartAlgInf (N * p) p) c : ↥(chartAlgInf (N * p) p)) : F) : F) :
      LaurentSeries ℚ).coeff 0 = (c : ℚ)
    rw [Subalgebra.coe_algebraMap, algebraMap_Zl_apply, AlgHom.commutes, coe_algebraMap_rat,
      HahnSeries.C_apply, HahnSeries.coeff_single_same])

end Charts
end NeronLeg1CuspSections
end
end P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
