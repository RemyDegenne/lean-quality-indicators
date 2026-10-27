namespace P2MW.S_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero

set_option autoImplicit false

open Matrix

open IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace UnramW17

section Matrices

variable {F : Type*} [Field F]

def scalarHom : Fˣ →* GL (Fin 2) F := Units.map (Matrix.scalar (Fin 2) : F →+* _).toMonoidHom

end Matrices
end UnramW17
end
end P2MW.S_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero
