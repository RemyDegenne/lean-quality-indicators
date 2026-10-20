set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain

open AutomorphicForm AutomorphicForm.WindowedSiegel

noncomputable section

namespace LanglandsTunnell.RankinSelberg

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section Global

variable (F : Type) [Field F] [NumberField F]

def rs22Kernel (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    Φ (bottomRowVec F g 1)

end Global
end LanglandsTunnell.RankinSelberg
end
