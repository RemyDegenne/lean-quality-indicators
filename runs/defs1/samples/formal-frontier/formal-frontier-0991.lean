@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option linter.mathlibStandardSet true

set_option linter.style.header false

noncomputable section

open Polynomial

namespace QuadraticAlgebra

/-- For an irreducible real quadratic, a specified complex root determines
the equivalence that evaluates polynomial classes at that root. No choice of
square-root sign or monic normalization is imposed. -/
noncomputable def adjoinRootComplexEquivOfRoot (p : ℝ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (z : ℂ) (hz : p.aeval z = 0) :
    AdjoinRoot p ≃ₐ[ℝ] ℂ := by
  have hz' : p.aeval (realComplexEquiv.symm z) = 0 := by
    apply realComplexEquiv.injective
    rw [map_zero, ← Polynomial.aeval_algHom_apply, realComplexEquiv.apply_symm_apply]
    exact hz
  exact (adjoinRootEquivOfRoot p hp hdeg (realComplexEquiv.symm z) hz').trans
    realComplexEquiv

end QuadraticAlgebra
end
end
