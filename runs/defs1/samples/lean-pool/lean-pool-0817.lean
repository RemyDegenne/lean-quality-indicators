public section

namespace NFChoice

open NFChoice.Set

namespace Fol

universe u v

variable {L : Language.{u}}

/-- T itself is a Theory_over T hT -/
@[expose]
def overSelf (T : SentTheory L) (hT : T.isConsistent) : TheoryOver T hT :=
  ⟨T, le_refl _, hT⟩

end Fol
end NFChoice
end
