@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option linter.mathlibStandardSet true

set_option linter.style.header false

noncomputable section

open Polynomial

namespace QuadraticAlgebra

@[simp] theorem adjoinRootComplexEquivOfIrreducible_root (p : ℝ[X])
    (hp : Irreducible p) (hdeg : 1 < p.natDegree) :
    adjoinRootComplexEquivOfIrreducible p hp hdeg (AdjoinRoot.root p) =
      complexRootOfIrreducible p hp := by
  exact adjoinRootComplexEquivOfRoot_root p hp _ _ _

end QuadraticAlgebra
end
end
