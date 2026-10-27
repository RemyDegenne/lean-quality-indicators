namespace P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter

open NumberField.AdelicLevel TensorProduct

open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm

namespace TwistedCentralizerHaarFactor

p2m_open

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

section Embedding

def entryAdele (i j : Fin 2) (t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1)) :
    FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
    (fun w : HeightOneSpectrum (𝓞 L) => (w.adicCompletionIntegers L : Set (w.adicCompletion L)))
    (cofinite_le_principal_compl S) (entryPrincipal S i j t)

end Embedding
end TwistedCentralizerHaarFactor
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
