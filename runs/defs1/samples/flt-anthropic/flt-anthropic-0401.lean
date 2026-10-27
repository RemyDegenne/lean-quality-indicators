set_option autoImplicit false

open NumberField NumberField.AdelicLevel MeasureTheory IsDedekindDomain

open AutomorphicForm.WindowedSiegel

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K]

variable {K}

variable (K)

section Factors

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def maximalCompactAwayHaar : Measure (maximalCompactAway K S) := Measure.haarMeasure ⊤

end Factors
end AutomorphicForm
end
