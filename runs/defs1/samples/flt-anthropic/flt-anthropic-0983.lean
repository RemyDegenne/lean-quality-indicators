namespace P2MW.S_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel UnramifiedWhittaker Topology Filter

open Rat.HeightOneSpectrum

open scoped Classical Pointwise

namespace KirillovSchwartzEngine

section Span

variable {G : Type*} [Group G]

abbrev cyc (W₀ : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h))

end Span
end KirillovSchwartzEngine
end
end P2MW.S_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible
