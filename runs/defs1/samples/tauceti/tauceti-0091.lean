public section

namespace TauCeti

open Finset Pointwise

universe u u' v v' w

variable {V : Type u} (Q : V → V → Type v) (K : Type w)

variable {Q K}

section AddCommGroup

variable [AddCommGroup K] [∀ v w, Fintype (Q v w)]

variable [Fintype V]

/-- A (signed) *circulation* is an arrow assignment conserved at every vertex: its excess vanishes
everywhere. No sign or capacity constraint is imposed. -/
def IsCirculation (f : Assignment Q K) : Prop :=
  ∀ v, excessAt f v = 0

end AddCommGroup
end TauCeti
end
