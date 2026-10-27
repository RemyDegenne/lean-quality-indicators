namespace P2MW.S_AutomorphicForm_integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open IsDedekindDomain

open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

open AutomorphicForm AdelicDock LocalGL2

namespace RowH

variable {K : Type} [Field K] [NumberField K]

section Conv

attribute [local instance] NumberField.AdelicHaar.glBorel

variable {J : HeightOneSpectrum (𝓞 K) → Type} [∀ v, Fintype (J v)]
  (w : ∀ v : HeightOneSpectrum (𝓞 K), J v → GL (Fin 2) (v.adicCompletion K))

def gIter [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (gS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (l : List (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) : GL (Fin 2) (v.adicCompletion K) → ℂ :=
  if v ∈ l then fun x => ∑ j, gS v ((w v j)⁻¹ * x) else gS v

end Conv
end RowH
end
end P2MW.S_AutomorphicForm_integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization
