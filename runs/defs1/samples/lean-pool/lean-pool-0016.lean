@[expose] public section

namespace FirstOrder

namespace Language

namespace HanfLadder

open Ordinal

variable {α : Ordinal.{0}}

section Semantics

variable (α) {M : Type} [(ladderLang α).Structure M]

/-- The value of the `n`-th constant. -/
def constVal (n : ℕ) : M :=
  Structure.funMap (L := ladderLang α) (show (ladderLang α).Functions 0 from n) Fin.elim0

end Semantics
end HanfLadder
end Language
end FirstOrder
end
