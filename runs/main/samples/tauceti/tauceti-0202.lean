public section

open WithConv

namespace TauCeti.SpecialLinear

open DynkinType

universe u w

variable {r : ℕ}

@[simp] theorem diagonalRootDatumEquiv_indexEquiv (r : ℕ) :
    (diagonalRootDatumEquiv.{u} r).indexEquiv = (typeAIndexEquiv r).symm := (rfl)

end TauCeti.SpecialLinear
end
