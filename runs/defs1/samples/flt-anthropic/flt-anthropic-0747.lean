namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction MeasureTheory

namespace Ws23PhiFlatM

open LanglandsTunnell.Converse.ArchR Set

noncomputable def eM (x y₁ y₂ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ / y₁, -(x * Real.cos θ) / y₁ + Real.sin θ / y₂;
     -(Real.sin θ) / y₁, x * Real.sin θ / y₁ + Real.cos θ / y₂]

end Ws23PhiFlatM
end P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
