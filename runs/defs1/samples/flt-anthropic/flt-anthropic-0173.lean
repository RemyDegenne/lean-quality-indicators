namespace P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar

set_option autoImplicit false

set_option Elab.async false

section Fold_FadContent

set_option autoImplicit false

p2m_open

open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter

p2m_open

variable (K : Type*) [Field K] [NumberField K]

section StageA

def placeOrd (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  -WithZero.log (Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v))

end StageA
end HeckeCharacter
end
end Fold_FadContent
end P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar
