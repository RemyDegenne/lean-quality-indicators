namespace P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar

set_option autoImplicit false

set_option Elab.async false

section Fold_IdeleContentBuild

set_option autoImplicit false

p2m_open

open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter

p2m_open

variable (K : Type*) [Field K] [NumberField K]

section StageC

open _root_.NumberField.InfinitePlace.Completion in

noncomputable def archRealProjTau (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) : ℝ :=
  ringEquivRealOfIsReal (isReal_placeOf K τ)
    (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) (placeOf K τ))

end StageC
end HeckeCharacter
end
end Fold_IdeleContentBuild
end P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar
