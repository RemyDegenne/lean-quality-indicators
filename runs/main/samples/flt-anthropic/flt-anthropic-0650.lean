namespace P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero

set_option autoImplicit false

open Matrix

p2m_open

namespace UnramifiedWhittaker

namespace C8P1

p2m_open

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

variable {F}

@[scoped simp] theorem cpt_placeEmbed_self (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (v.adicCompletion F)) :
    cpt F v (placeEmbed F v x) = x := by
  rw [placeEmbed_eq, cpt_finEmbed, finComponent_localEmbed_self]

end C8P1
end UnramifiedWhittaker
end P2MW.S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero
