namespace P2MW.S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter

open NumberField.AdelicLevel NumberField.AdelicHaar TensorProduct

open scoped TensorProduct.RightActions NNReal ENNReal Pointwise Classical

noncomputable section

namespace AutomorphicForm

namespace PrescribedComponents

p2m_open

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev SL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  L ⊗[K] v.adicCompletion K

end PrescribedComponents
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset
