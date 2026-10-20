namespace P2MW.S_ModularForm_isZeroAt_add_heckeU_alSlash

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

@[scoped simp] lemma det_sqUnit : W.sqUnit.det = 1 := by
  rw [sqUnit, Matrix.det_fin_two_of]
  linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout

end ALData
end ModularCurve
end
end WcPort
end P2MW.S_ModularForm_isZeroAt_add_heckeU_alSlash
