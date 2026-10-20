namespace P2MW.S_AutomorphicForm_exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Topology TopologicalSpace Set Filter

open NumberField.AdelicLevel TensorProduct

open scoped TensorProduct.RightActions Classical

noncomputable section

namespace AutomorphicForm

namespace LocalCofinite

p2m_open

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Gt (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)

end LocalCofinite
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet
