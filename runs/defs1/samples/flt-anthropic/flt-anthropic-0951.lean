set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace

open AutomorphicForm

noncomputable section

namespace NumberField.StandardAddChar

variable (F : Type) [Field F] [NumberField F]

namespace AdelicTraceData

variable {F}

variable (T : AdelicTraceData F)

def psiK : AddChar (AdeleRing (𝓞 F) F) ℂ :=
  psiQ.compAddMonoidHom T.adelicTrace

end AdelicTraceData
end NumberField.StandardAddChar
end
