namespace P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell

namespace CubicInduction

namespace RaySupplyK1

p2m_open

open _root_.WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock AutomorphicForm AutomorphicForm.StandardKernel Matrix

theorem idA_mulA (e : Arr) : mulA idA e = e := by
  have : Matrix.of (mulA idA e) = Matrix.of e := by rw [of_mulA, of_idA, Matrix.one_mul]
  exact this

end RaySupplyK1
end CubicInduction
end LanglandsTunnell
end
end P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le
