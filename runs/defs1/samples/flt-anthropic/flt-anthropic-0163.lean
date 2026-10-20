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

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace CuspForm

open HeckeAnalytic ModularCurve CongruenceSubgroup OnePoint

variable {M q : ℕ} {k : ℤ}

def atkinLehnerHom [NeZero M] (W : ALData M q) :
    CuspForm (Gamma0 M) k →ₗ[ℂ] CuspForm (Gamma0 M) k where
  toFun := atkinLehner W
  map_add' := atkinLehner_add W
  map_smul' := atkinLehner_smul W

end CuspForm
end
end WcPort
end P2MW.S_ModularForm_alSlash_heckeT_comm
