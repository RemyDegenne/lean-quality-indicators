set_option autoImplicit false

namespace SwdAlgebra

noncomputable def ev (F : Type) [Field F] : MvPolynomial (Fin 2) F →ₐ[F] PowerSeries F :=
  MvPolynomial.aeval ![qE4 F, qE6 F]

end SwdAlgebra
