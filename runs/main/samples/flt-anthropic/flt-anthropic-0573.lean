namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_dual_rsIntegrand22_withDensity_of_admissible_of_chamber

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace ABSP

open Filter Topology NumberField.StandardAddChar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

local notation "K₀" => AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

theorem det_unipotent_mul (x : F) (g : G2) :
    Matrix.GeneralLinearGroup.det (unipotent x * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  have : Matrix.GeneralLinearGroup.det (unipotent x : G2) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, unipotent_eq_unipotentGL2, unipotentGL2_coe, Matrix.det_fin_two_of]
    simp
  rw [this, one_mul]

end ABSP
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_dual_rsIntegrand22_withDensity_of_admissible_of_chamber
