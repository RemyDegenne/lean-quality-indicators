namespace P2MW.S_AutomorphicForm_exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open IsDedekindDomain

open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField AutomorphicForm

open scoped ComplexConjugate

noncomputable section

namespace AVA

section Quarry

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

theorem archComponent_glArch_inclAt_self (w : InfinitePlace F) (x : GL (Fin 2) w.Completion) :
    archComponent F w (glArch (𝓞 F) F (adelicArchGLInclAt F w x)) = x := by
  show archComponent F w (glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w x))) = x
  rw [glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

end Quarry
end AVA
end
end P2MW.S_AutomorphicForm_exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne
