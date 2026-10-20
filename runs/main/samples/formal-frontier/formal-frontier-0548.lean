@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option linter.mathlibStandardSet true

set_option linter.style.header false

noncomputable section

open Polynomial

namespace QuadraticAlgebra

@[simp] theorem realComplexEquiv_symm_apply (z : ℂ) :
    realComplexEquiv.symm z = ⟨z.re, z.im⟩ := by
  apply realComplexEquiv.injective
  rw [realComplexEquiv.apply_symm_apply, realComplexEquiv_apply]
  exact (Complex.re_add_im z).symm

end QuadraticAlgebra
end
end
