namespace P2MW.S_AutomorphicForm_mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open scoped Manifold

noncomputable section

namespace Ws23

namespace M3core

p2m_open

open scoped Manifold

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

def ptE (z : UpperHalfPlane) (t : ℝ) : UpperHalfPlane :=
  ⟨(z : ℂ) + (t * z.im : ℝ), by rw [im_coe_add_ofReal]; exact z.im_pos⟩

end M3core
end Ws23
end
end P2MW.S_AutomorphicForm_mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt
