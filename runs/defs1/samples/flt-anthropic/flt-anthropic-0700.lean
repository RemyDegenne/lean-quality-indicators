set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace.Completion Matrix

variable (F : Type) [Field F] [NumberField F]

section Flows

variable {F}

def archFlowAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) : AdelicGL2 (𝓞 F) F :=
  archRealGLAt hw (archFlowMatrix d t)

end Flows
end AutomorphicForm
end
