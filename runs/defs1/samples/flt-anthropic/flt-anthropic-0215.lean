namespace P2MW.S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Matrix AutomorphicForm

open scoped ComplexConjugate

namespace KcConjType

section Delta

variable {G : Type*} [Group G]

variable {Kc : Type*} [Group Kc] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc]
  [MeasurableSpace Kc] [BorelSpace Kc]

variable (μ : Measure Kc) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [μ.IsMulRightInvariant]

variable (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))

variable (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)

variable [FiniteDimensional ℂ E]

variable (hcont : ∀ v ∈ E, ∀ x : G, Continuous fun κ : Kc => v (x * ι κ))

def Hm : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
  Mint μ fun κ => (Pm ι E hE κ)ᴴ * Pm ι E hE κ

end Delta
end KcConjType
end
end P2MW.S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support
