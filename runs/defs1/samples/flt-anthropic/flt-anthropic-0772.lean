namespace P2MW.S_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt

attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

noncomputable section

namespace UnramTwist

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal

open IsDedekindDomain AutomorphicForm

open scoped NNReal

variable {K : Type} [Field K] [NumberField K]

def idl (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)

end UnramTwist
end
end P2MW.S_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt
