@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option linter.mathlibStandardSet true

set_option linter.style.header false

noncomputable section

open Polynomial

namespace QuadraticAlgebra

/-- A selected complex root of an irreducible real polynomial. This choice
does not impose a sign convention. -/
noncomputable def complexRootOfIrreducible (p : ℝ[X]) (hp : Irreducible p) : ℂ :=
  Classical.choose
    (IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne')

end QuadraticAlgebra
end
end
