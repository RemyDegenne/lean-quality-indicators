namespace P2MW.S_ModularForm_alSlash_heckeT_comm

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

p2m_reactivate

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function

open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace ModularCurve

namespace ALData

variable {M q : ℕ} (W : ALData M q)

def traceRepMat : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => W.mat
  | some j => HeckeAnalytic.repMat q (some j)

end ALData
end ModularCurve
end
end WcPort
end P2MW.S_ModularForm_alSlash_heckeT_comm
