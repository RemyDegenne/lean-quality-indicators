namespace P2MW.S_ModularForm_alSlash_add_heckeU_alSlash_alSlash

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.deprecated false

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace WcPort

open UpperHalfPlane

open scoped ModularForm MatrixGroups

def toALData {M q : ℕ} (W : _root_.ModularForm.AtkinLehnerDatum M q) : ModularCurve.ALData M q :=
  ⟨W.R, W.hM, W.a, W.b, W.bezout⟩

end WcPort
end P2MW.S_ModularForm_alSlash_add_heckeU_alSlash_alSlash
