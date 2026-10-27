namespace P2MW.S_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne

set_option autoImplicit false

open MeasureTheory NumberField

open scoped Pointwise

noncomputable section

namespace R1MellinOrthogonality

section Idele

variable (F : Type) [Field F] [NumberField F]

def principalUnits : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range

end Idele
end R1MellinOrthogonality
end
end P2MW.S_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
