namespace P2MW.S_LanglandsTunnell_CubicInduction_whittaker3_mirabolicSeries_eq

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm Matrix MeasureTheory

open scoped NNReal ENNReal Pointwise ProbabilityTheory

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel

local notation "μbox" =>
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

p2m_reactivate

p2m_reactivate

p2m_open

theorem solution
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ
      (fun x => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * x)) g = W g := by
  show (∫ x, ∫ y, ∫ z, (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (upperUnipotent3 x y z * g))) * ψ (-(x + y))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) = W g
  exact integral_integral_integral_mirabolicSeries_eq _hψ _hW _hsum g

end P2MW.S_LanglandsTunnell_CubicInduction_whittaker3_mirabolicSeries_eq
