public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

section Group

variable (G : Type u) [Group G]

variable {G}

variable (G)

/-- Tannaka duality transported along an equivalence: if a functor `e` from a category `C` to
`G`-sets is an equivalence, then the group `G` is the automorphism group of the composite
`C ⥤ Type u`. -/
def autCompForgetActionMulEquiv {C : Type*} [Category C] (e : C ⥤ Action (Type u) G)
    [e.IsEquivalence] : G ≃* Aut (e ⋙ Action.forget (Type u) G) :=
  toUnits.trans (unitsAutCompForgetActionMulEquiv G e)

end Group
end TauCeti
end
end
