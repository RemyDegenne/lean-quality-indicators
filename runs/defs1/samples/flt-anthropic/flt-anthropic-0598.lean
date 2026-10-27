set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

open scoped TensorProduct Pointwise

namespace AutomorphicForm.TransversalMeasure

def saturated (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 L) L)ˣ :=
  {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sτ → semiLocalIdele K L v t ∈ saturatedUnits K L v}

end AutomorphicForm.TransversalMeasure
