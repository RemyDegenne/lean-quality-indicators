namespace P2MW.S_LanglandsTunnell_CubicInduction_forall_isCompact_norm_whittaker3_le_of_forall_isCompact_orth3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory InnerProductSpace

open scoped Matrix Pointwise

namespace R1ALT6b155e1a

open LanglandsTunnell.CubicInduction AutomorphicForm.StandardKernel

theorem continuous_ρ : Continuous ρ := by
  have h1 : Continuous (archComponent3 (𝓞 ℚ) ℚ : G → GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
    Continuous.units_map _ ((continuous_id.matrix_map (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)) :
      Continuous fun m : Matrix (Fin 3) (Fin 3) A => m.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ))
  have h2 : Continuous (realGL : GL (Fin 3) (InfiniteAdeleRing ℚ) → GL (Fin 3) ℝ) :=
    Continuous.units_map _ ((continuous_id.matrix_map continuous_realCoord) :
      Continuous fun m : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) => m.map realCoord)
  exact h2.comp h1

end R1ALT6b155e1a
end P2MW.S_LanglandsTunnell_CubicInduction_forall_isCompact_norm_whittaker3_le_of_forall_isCompact_orth3
