namespace P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.deprecated false

namespace WcPort

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup

open scoped MatrixGroups ModularForm

p2m_reactivate

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function

open scoped MatrixGroups ModularForm Real

p2m_reactivate

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function

open scoped MatrixGroups ModularForm Manifold

p2m_reactivate

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function

open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace ModularCurve

variable (M q : ℕ)

namespace ALData

variable {M q : ℕ} (W : ALData M q)

def sqUnitSL : SL(2, ℤ) := ⟨W.sqUnit, W.det_sqUnit⟩

end ALData
end ModularCurve
end
end WcPort
end P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0
