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

p2m_reactivate

p2m_reactivate

namespace HeckeAnalytic

open ModularCurve

variable {M q : ℕ} (W : ALData M q)

@[scoped simp] lemma traceRepGL_none [NeZero M] [NeZero q] : traceRepGL W none = alGL W := rfl

end HeckeAnalytic
end
end WcPort
end P2MW.S_ModularForm_alSlash_heckeT_comm
