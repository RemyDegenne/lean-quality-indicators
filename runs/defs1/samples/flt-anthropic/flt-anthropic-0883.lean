namespace P2MW.S_AutomorphicForm_measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero

set_option autoImplicit false

open scoped TensorProduct

namespace PolyAux

section main

variable (K F L : Type*) [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
  [FiniteDimensional K L]
  (ι : Type*) [Fintype ι] (n : Type*) [Fintype n] [DecidableEq n] (b : ι → Matrix n n L)

noncomputable def normPoly : MvPolynomial ι F :=
  Algebra.norm (MvPolynomial ι F) (genericMatrix K F L ι n b).det

end main
end PolyAux
end P2MW.S_AutomorphicForm_measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero
