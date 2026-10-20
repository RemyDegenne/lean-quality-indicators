namespace P2MW.S_AutomorphicForm_exists_rightConv_eq_of_archCutProjector

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel

open AutomorphicForm.CuspidalConstituent

open scoped Pointwise BigOperators

noncomputable section

namespace F4CutWords

scoped instance compactSpace_rowIsometrySubgroup₀ (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K) :
    CompactSpace (rowIsometrySubgroup₀ w.Completion) :=
  isCompact_iff_compactSpace.mp (isCompact_rowIsometrySubgroup₀ K w)

variable (F : Type) [Field F] [NumberField F]

section PartB

variable (F : Type) [Field F] [NumberField F]

local instance : MeasurableSpace (ArchIsometryProd F) := borel _

local instance : BorelSpace (ArchIsometryProd F) := ⟨rfl⟩

theorem orbitSpan_le_Ecf {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ Ecf F) : orbitSpan F φ ≤ Ecf F := by
  intro ψ hψ
  refine ⟨continuous_of_mem_orbitSpan F hφ.1 ψ hψ, ?_⟩
  haveI := hφ.2
  exact Submodule.finiteDimensional_of_le (orbitSpan_le_of_mem F hψ)

end PartB
end F4CutWords
end
end P2MW.S_AutomorphicForm_exists_rightConv_eq_of_archCutProjector
