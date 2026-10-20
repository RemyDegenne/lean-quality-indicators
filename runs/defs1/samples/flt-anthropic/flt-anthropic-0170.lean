namespace P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.AdelicEpstein

open scoped ENNReal

namespace KcEpsteinTail

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

local notation "𝔸f" => IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ

local notation "Ẑˣ" => IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ

def Z (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) (i : Fin 3) : 𝔸f :=
  fin (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸) i)

end KcEpsteinTail
end
end P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul
