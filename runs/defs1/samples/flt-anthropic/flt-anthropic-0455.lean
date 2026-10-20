namespace P2MW.S_ModularForm_alSlash_add_heckeU_alSlash_alSlash

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

namespace SlashInvariantForm

open HeckeAnalytic ModularCurve CongruenceSubgroup

variable {M q : ℕ} {k : ℤ}

def atkinLehner [NeZero M] (W : ALData M q) (f : SlashInvariantForm (Gamma0 M) k) :
    SlashInvariantForm (Gamma0 M) k where
  toFun := alSlash W k f
  slash_action_eq' := fun _ hγ => alSlash_slash W f.slash_action_eq' hγ

end SlashInvariantForm
end
end WcPort
end P2MW.S_ModularForm_alSlash_add_heckeU_alSlash_alSlash
