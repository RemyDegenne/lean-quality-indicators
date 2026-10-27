namespace P2MW.S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule

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

def archProdIncl : ArchIsometryProd F →* AdelicGL2 (𝓞 F) F :=
  MonoidHom.noncommPiCoprod (fun w => rowIsometryInclAt₀ F w) fun v w hvw x y => by
    rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply]
    exact commute_adelicArchGLInclAt_of_ne F hvw _ _

end F4CutWords
end
end P2MW.S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule
