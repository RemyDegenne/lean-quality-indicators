namespace P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass

set_option autoImplicit false

set_option Elab.async false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_LocalGlobalModulus

set_option autoImplicit false

p2m_open

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField

namespace TateGlobal

p2m_open

variable {F : Type} [Field F] [NumberField F]

section LG

variable (v : HeightOneSpectrum (𝓞 F))

def coordAt (x : AdeleRing (𝓞 F) F) : v.adicCompletion F := (x.2 : FiniteAdeleRing (𝓞 F) F) v

end LG
end TateGlobal
end NumberField
end
end Fold_LocalGlobalModulus
end P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass
