public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- The setoid of characteristic covectors in the same lattice orbit. -/
def spinCSetoid : Setoid P.characteristicVectors where
  r := P.IsSpinCEquivalent
  iseqv := {
    refl := fun k => P.isSpinCEquivalent_refl k
    symm := fun {_ _} h => IsSpinCEquivalent.symm P h
    trans := fun {_ _ _} h₁ h₂ => IsSpinCEquivalent.trans P h₁ h₂ }

end PlumbingGraph
end TauCeti
end
