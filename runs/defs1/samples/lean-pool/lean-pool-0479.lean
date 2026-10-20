@[expose] public section

noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

scoped prefix:max "^rel " => qqRel

scoped prefix:max "^nrel " => qqNRel

scoped notation "^⊤" => qqVerum

scoped notation "^⊥" => qqFalsum

scoped notation p:69 " ^⋏ " q:70 => qqAnd p q

scoped notation p:68 " ^⋎ " q:69 => qqOr p q

scoped notation "^∀ " p:64 => qqAll p

scoped notation "^∃ " p:64 => qqEx p

namespace Language

namespace UformulaRec1

variable (V)

variable {V}

namespace Construction

variable {β : Blueprint pL} (c : Construction V L β)

variable {param : V}

variable {c}

variable (c β)

variable {β}

variable (param)

/-- Imported declaration from the Incompleteness formalization. -/
def result (p : V) : V := Classical.choose! (c.exists_unique_all param p)

end Construction
end UformulaRec1
end Language
end Arith
end LO
end «lp_nc_section_1»
end
