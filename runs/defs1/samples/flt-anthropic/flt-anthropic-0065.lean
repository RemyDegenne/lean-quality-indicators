namespace P2MW.S_ModularCurve_isModuliPlaceOf_map_frobenius_smul

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

open scoped Pointwise

universe u

namespace IsModuliPlaceOfFrobSmulSol

section Twist

variable {κ : Type u} [Field κ] (τ : κ ≃+* κ) (Ω : Type u)

scoped instance [h : Field Ω] : Field (Tw τ Ω) := h

scoped instance [h : DecidableEq Ω] : DecidableEq (Tw τ Ω) := h

scoped instance [Field Ω] [Algebra κ Ω] : Algebra κ (Tw τ Ω) :=
  ((algebraMap κ Ω).comp τ.symm.toRingHom).toAlgebra

variable {Ω} in

def twPlace [Field Ω] [Algebra κ Ω] (V : Place κ Ω) : Place κ (Tw τ Ω) where
  toValuationSubring := (V.toValuationSubring : ValuationSubring Ω)
  algebraMap_mem' c := V.algebraMap_mem' (τ.symm c)
  ne_top' := V.ne_top'
  isPrincipalIdealRing' := V.isPrincipalIdealRing'

end Twist
end IsModuliPlaceOfFrobSmulSol
end
end P2MW.S_ModularCurve_isModuliPlaceOf_map_frobenius_smul
