public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open Module

namespace NoOffRest

section Model

variable {p : ℕ}

theorem card_eigE8 [Fact p.Prime] (hp2 : p ≠ 2) {lam : ZMod p} (hlam : lam * lam = -1) :
    Nat.card (eigE8 p lam) = p ^ 4 := by
  rw [natCard_submodule, finrank_eigE8 hp2 hlam]

end Model
end NoOffRest
end CFSG.StandardType
end
