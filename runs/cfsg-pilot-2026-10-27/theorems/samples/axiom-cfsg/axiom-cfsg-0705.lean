public noncomputable section

namespace CFSG.LieType.Chevalley.G2FieldFour

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ExceptionalCover

open scoped commutatorElement

variable {K : Type} [Field K]

variable {ω : Kˣ}

section Table

variable [CharP K 2] (x y : K)

theorem commute_rootX_bc
    : Commute (rootX rootB x) (rootX rootC y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Table
end CFSG.LieType.Chevalley.G2FieldFour
end
